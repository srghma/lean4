// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: Lean.Meta.Sym.Arith.EvalNum Lean.Meta.Sym.SynthInstance Lean.Meta.Sym.Canon Lean.Meta.DecLevel Init.Grind.Ring
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le,
    lean_usize_land, lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub,
    lean_usize_to_nat,
};
use crate::r#gen::Init::Grind::Ring::{
    initialize_Init_Grind_Ring, runtime_initialize_Init_Grind_Ring,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_hasMVar, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp, l_Lean_Meta_mkFreshExprMVar,
};
use crate::r#gen::Lean::Meta::DecLevel::{
    initialize_Lean_Meta_DecLevel, l_Lean_Meta_getDecLevel, runtime_initialize_Lean_Meta_DecLevel,
};
use crate::r#gen::Lean::Meta::Sym::Arith::EvalNum::{
    initialize_Lean_Meta_Sym_Arith_EvalNum, l_Lean_Meta_Sym_Arith_evalNat_x3f,
    runtime_initialize_Lean_Meta_Sym_Arith_EvalNum,
};
use crate::r#gen::Lean::Meta::Sym::Arith::Types::{
    l_Lean_Meta_Sym_Arith_arithExt, l_Lean_Meta_Sym_Arith_getArithState___redArg,
};
use crate::r#gen::Lean::Meta::Sym::Canon::{
    initialize_Lean_Meta_Sym_Canon, l_Lean_Meta_Sym_canon, runtime_initialize_Lean_Meta_Sym_Canon,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::{
    initialize_Lean_Meta_Sym_SynthInstance, l_Lean_Meta_Sym_synthInstanceMeta_x3f,
    runtime_initialize_Lean_Meta_Sym_SynthInstance,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 115, 67, 104, 97, 114, 80, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value) as *mut crate::leanh::LeanObject,5319903737885873089 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11442535297760353691 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 97, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,12969150934523051142 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value: crate::leanh::LeanStringObject<18> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value) as *mut crate::leanh::LeanObject,5648161575337860430 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value) as *mut crate::leanh::LeanObject,12221341192526463479 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut crate::leanh::LeanObject,14047490016268445595 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut crate::leanh::LeanObject,16367934121419604941 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value) as *mut crate::leanh::LeanObject,9499613419783151494 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value) as *mut crate::leanh::LeanObject,8615353994042975301 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15814158821706329669 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut crate::leanh::LeanObject,15814158821706329669 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut crate::leanh::LeanObject,4308150853741380486 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value: crate::leanh::LeanStringObject<2> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [81, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut crate::leanh::LeanObject,10806710915646349764 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value) as *mut crate::leanh::LeanObject,8254287559757149654 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value) as *mut crate::leanh::LeanObject,12174124158933200568 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value: crate::leanh::LeanStringObject<37> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 97, 105, 108, 117, 114, 101, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105, 110, 103, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value) as *mut crate::leanh::LeanObject,12050285396929189622 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(
    mut v_e_1583_: *mut crate::leanh::LeanObject,
    mut v___y_1584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = l_Lean_Expr_hasMVar(v_e_1583_);
                if v___x_1586_ == 0 {
                    v___x_1587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1587_, 0, v_e_1583_);
                    return v___x_1587_;
                } else {
                    v___x_1588_ = lean_st_ref_get(v___y_1584_);
                    v_mctx_1589_ = crate::leanh::lean_ctor_get(v___x_1588_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1589_);
                    crate::leanh::lean_dec(v___x_1588_);
                    v___x_1590_ = l_Lean_instantiateMVarsCore(v_mctx_1589_, v_e_1583_);
                    v_fst_1591_ = crate::leanh::lean_ctor_get(v___x_1590_, 0);
                    crate::leanh::lean_inc(v_fst_1591_);
                    v_snd_1592_ = crate::leanh::lean_ctor_get(v___x_1590_, 1);
                    crate::leanh::lean_inc(v_snd_1592_);
                    crate::leanh::lean_dec_ref(v___x_1590_);
                    v___x_1593_ = lean_st_ref_take(v___y_1584_);
                    v_cache_1594_ = crate::leanh::lean_ctor_get(v___x_1593_, 1);
                    v_zetaDeltaFVarIds_1595_ = crate::leanh::lean_ctor_get(v___x_1593_, 2);
                    v_postponed_1596_ = crate::leanh::lean_ctor_get(v___x_1593_, 3);
                    v_diag_1597_ = crate::leanh::lean_ctor_get(v___x_1593_, 4);
                    v_isSharedCheck_1606_ = (!crate::leanh::lean_is_exclusive(v___x_1593_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v_unused_1607_ = crate::leanh::lean_ctor_get(v___x_1593_, 0);
                        crate::leanh::lean_dec(v_unused_1607_);
                        v___x_1599_ = v___x_1593_;
                        v_isShared_1600_ = v_isSharedCheck_1606_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1597_);
                        crate::leanh::lean_inc(v_postponed_1596_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1595_);
                        crate::leanh::lean_inc(v_cache_1594_);
                        crate::leanh::lean_dec(v___x_1593_);
                        v___x_1599_ = crate::leanh::lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1606_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1599_, 0, v_snd_1592_);
                    v___x_1602_ = v___x_1599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_snd_1592_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_cache_1594_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1605_,
                        2,
                        v_zetaDeltaFVarIds_1595_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_postponed_1596_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_diag_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1603_ = lean_st_ref_set(v___y_1584_, v___x_1602_);
                v___x_1604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1604_, 0, v_fst_1591_);
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(
    mut v_e_1608_: *mut crate::leanh::LeanObject,
    mut v___y_1609_: *mut crate::leanh::LeanObject,
    mut v___y_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_1608_, v___y_1609_);
    crate::leanh::lean_dec(v___y_1609_);
    return v_res_1611_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(
    mut v_e_1612_: *mut crate::leanh::LeanObject,
    mut v___y_1613_: *mut crate::leanh::LeanObject,
    mut v___y_1614_: *mut crate::leanh::LeanObject,
    mut v___y_1615_: *mut crate::leanh::LeanObject,
    mut v___y_1616_: *mut crate::leanh::LeanObject,
    mut v___y_1617_: *mut crate::leanh::LeanObject,
    mut v___y_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_1612_, v___y_1616_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(
    mut v_e_1621_: *mut crate::leanh::LeanObject,
    mut v___y_1622_: *mut crate::leanh::LeanObject,
    mut v___y_1623_: *mut crate::leanh::LeanObject,
    mut v___y_1624_: *mut crate::leanh::LeanObject,
    mut v___y_1625_: *mut crate::leanh::LeanObject,
    mut v___y_1626_: *mut crate::leanh::LeanObject,
    mut v___y_1627_: *mut crate::leanh::LeanObject,
    mut v___y_1628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
    crate::leanh::lean_dec(v___y_1627_);
    crate::leanh::lean_dec_ref(v___y_1626_);
    crate::leanh::lean_dec(v___y_1625_);
    crate::leanh::lean_dec_ref(v___y_1624_);
    crate::leanh::lean_dec(v___y_1623_);
    crate::leanh::lean_dec_ref(v___y_1622_);
    return v_res_1629_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(
    mut v_k_1630_: *mut crate::leanh::LeanObject,
    mut v___y_1631_: *mut crate::leanh::LeanObject,
    mut v___y_1632_: *mut crate::leanh::LeanObject,
    mut v___y_1633_: *mut crate::leanh::LeanObject,
    mut v___y_1634_: *mut crate::leanh::LeanObject,
    mut v___y_1635_: *mut crate::leanh::LeanObject,
    mut v___y_1636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___y_1632_);
    crate::leanh::lean_inc_ref(v___y_1631_);
    v___x_1638_ = crate::leanh::lean_apply_7(
        v_k_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
        v___y_1634_,
        v___y_1635_,
        v___y_1636_,
        crate::leanh::lean_box(0),
    );
    return v___x_1638_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
    crate::leanh::lean_dec(v___y_1641_);
    crate::leanh::lean_dec_ref(v___y_1640_);
    return v_res_1647_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(
    mut v_k_1648_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1649_: u8,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v___y_1651_);
                crate::leanh::lean_inc_ref(v___y_1650_);
                v___f_1657_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                crate::leanh::lean_closure_set(v___f_1657_, 0, v_k_1648_);
                crate::leanh::lean_closure_set(v___f_1657_, 1, v___y_1650_);
                crate::leanh::lean_closure_set(v___f_1657_, 2, v___y_1651_);
                v___x_1658_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    crate::leanh::lean_box(0),
                    v_allowLevelAssignments_1649_,
                    v___f_1657_,
                    v___y_1652_,
                    v___y_1653_,
                    v___y_1654_,
                    v___y_1655_,
                );
                if crate::leanh::lean_obj_tag(v___x_1658_) == 0 {
                    return v___x_1658_;
                } else {
                    v_a_1659_ = crate::leanh::lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1666_ = (!crate::leanh::lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1661_ = v___x_1658_;
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1659_);
                        crate::leanh::lean_dec(v___x_1658_);
                        v___x_1661_ = crate::leanh::lean_box(0);
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1662_ == 0 {
                    v___x_1664_ = v___x_1661_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
                    v___x_1664_ = v_reuseFailAlloc_1665_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1664_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___boxed(
    mut v_k_1667_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1668_: *mut crate::leanh::LeanObject,
    mut v___y_1669_: *mut crate::leanh::LeanObject,
    mut v___y_1670_: *mut crate::leanh::LeanObject,
    mut v___y_1671_: *mut crate::leanh::LeanObject,
    mut v___y_1672_: *mut crate::leanh::LeanObject,
    mut v___y_1673_: *mut crate::leanh::LeanObject,
    mut v___y_1674_: *mut crate::leanh::LeanObject,
    mut v___y_1675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1676_: u8 = 0;
    let mut v_res_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1676_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1668_) as u8);
    v_res_1677_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_1667_, v_allowLevelAssignments_boxed_1676_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
    crate::leanh::lean_dec(v___y_1674_);
    crate::leanh::lean_dec_ref(v___y_1673_);
    crate::leanh::lean_dec(v___y_1672_);
    crate::leanh::lean_dec_ref(v___y_1671_);
    crate::leanh::lean_dec(v___y_1670_);
    crate::leanh::lean_dec_ref(v___y_1669_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(
    mut v_00_u03b1_1678_: *mut crate::leanh::LeanObject,
    mut v_k_1679_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1680_: u8,
    mut v___y_1681_: *mut crate::leanh::LeanObject,
    mut v___y_1682_: *mut crate::leanh::LeanObject,
    mut v___y_1683_: *mut crate::leanh::LeanObject,
    mut v___y_1684_: *mut crate::leanh::LeanObject,
    mut v___y_1685_: *mut crate::leanh::LeanObject,
    mut v___y_1686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_1679_, v_allowLevelAssignments_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(
    mut v_00_u03b1_1689_: *mut crate::leanh::LeanObject,
    mut v_k_1690_: *mut crate::leanh::LeanObject,
    mut v_allowLevelAssignments_1691_: *mut crate::leanh::LeanObject,
    mut v___y_1692_: *mut crate::leanh::LeanObject,
    mut v___y_1693_: *mut crate::leanh::LeanObject,
    mut v___y_1694_: *mut crate::leanh::LeanObject,
    mut v___y_1695_: *mut crate::leanh::LeanObject,
    mut v___y_1696_: *mut crate::leanh::LeanObject,
    mut v___y_1697_: *mut crate::leanh::LeanObject,
    mut v___y_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_allowLevelAssignments_boxed_1699_: u8 = 0;
    let mut v_res_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1699_ =
        (crate::leanh::lean_unbox(v_allowLevelAssignments_1691_) as u8);
    v_res_1700_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_1689_, v_k_1690_, v_allowLevelAssignments_boxed_1699_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
    crate::leanh::lean_dec(v___y_1697_);
    crate::leanh::lean_dec_ref(v___y_1696_);
    crate::leanh::lean_dec(v___y_1695_);
    crate::leanh::lean_dec_ref(v___y_1694_);
    crate::leanh::lean_dec(v___y_1693_);
    crate::leanh::lean_dec_ref(v___y_1692_);
    return v_res_1700_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(
    mut v___x_1708_: *mut crate::leanh::LeanObject,
    mut v___x_1709_: u8,
    mut v___x_1710_: *mut crate::leanh::LeanObject,
    mut v_u_1711_: *mut crate::leanh::LeanObject,
    mut v___x_1712_: *mut crate::leanh::LeanObject,
    mut v_type_1713_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1714_: *mut crate::leanh::LeanObject,
    mut v___y_1715_: *mut crate::leanh::LeanObject,
    mut v___y_1716_: *mut crate::leanh::LeanObject,
    mut v___y_1717_: *mut crate::leanh::LeanObject,
    mut v___y_1718_: *mut crate::leanh::LeanObject,
    mut v___y_1719_: *mut crate::leanh::LeanObject,
    mut v___y_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_charType_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v_val_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_val_1741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_a_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v___x_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_a_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v_a_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1786_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1722_ = l_Lean_Meta_mkFreshExprMVar(
                    v___x_1708_,
                    v___x_1709_,
                    v___x_1710_,
                    v___y_1717_,
                    v___y_1718_,
                    v___y_1719_,
                    v___y_1720_,
                );
                if crate::leanh::lean_obj_tag(v___x_1722_) == 0 {
                    v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                    crate::leanh::lean_inc_n(v_a_1723_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1722_, 1);
                    v___x_1724_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3;
                    v___x_1725_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1725_, 0, v_u_1711_);
                    crate::leanh::lean_ctor_set(v___x_1725_, 1, v___x_1712_);
                    v___x_1726_ = l_Lean_mkConst(v___x_1724_, v___x_1725_);
                    v_charType_1727_ =
                        l_Lean_mkApp3(v___x_1726_, v_type_1713_, v_semiringInst_1714_, v_a_1723_);
                    v___x_1728_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v_charType_1727_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1728_) == 0 {
                        v_a_1729_ = crate::leanh::lean_ctor_get(v___x_1728_, 0);
                        v_isSharedCheck_1770_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1728_)) as u8;
                        if v_isSharedCheck_1770_ == 0 {
                            v___x_1731_ = v___x_1728_;
                            v_isShared_1732_ = v_isSharedCheck_1770_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1729_);
                            crate::leanh::lean_dec(v___x_1728_);
                            v___x_1731_ = crate::leanh::lean_box(0);
                            v_isShared_1732_ = v_isSharedCheck_1770_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1723_);
                        v_a_1771_ = crate::leanh::lean_ctor_get(v___x_1728_, 0);
                        v_isSharedCheck_1778_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1728_)) as u8;
                        if v_isSharedCheck_1778_ == 0 {
                            v___x_1773_ = v___x_1728_;
                            v_isShared_1774_ = v_isSharedCheck_1778_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1771_);
                            crate::leanh::lean_dec(v___x_1728_);
                            v___x_1773_ = crate::leanh::lean_box(0);
                            v_isShared_1774_ = v_isSharedCheck_1778_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_semiringInst_1714_);
                    crate::leanh::lean_dec_ref(v_type_1713_);
                    crate::leanh::lean_dec(v___x_1712_);
                    crate::leanh::lean_dec(v_u_1711_);
                    v_a_1779_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                    v_isSharedCheck_1786_ = (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1722_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1779_);
                        crate::leanh::lean_dec(v___x_1722_);
                        v___x_1781_ = crate::leanh::lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1729_) == 1 {
                    crate::leanh::lean_del_object(v___x_1731_);
                    v_val_1733_ = crate::leanh::lean_ctor_get(v_a_1729_, 0);
                    crate::leanh::lean_inc(v_val_1733_);
                    crate::leanh::lean_dec_ref_known(v_a_1729_, 1);
                    v___x_1734_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_1723_, v___y_1718_);
                    v_a_1735_ = crate::leanh::lean_ctor_get(v___x_1734_, 0);
                    crate::leanh::lean_inc(v_a_1735_);
                    crate::leanh::lean_dec_ref(v___x_1734_);
                    v___x_1736_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(
                        v_a_1735_,
                        v___y_1715_,
                        v___y_1716_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1736_) == 0 {
                        v_a_1737_ = crate::leanh::lean_ctor_get(v___x_1736_, 0);
                        v_isSharedCheck_1757_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1736_)) as u8;
                        if v_isSharedCheck_1757_ == 0 {
                            v___x_1739_ = v___x_1736_;
                            v_isShared_1740_ = v_isSharedCheck_1757_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1737_);
                            crate::leanh::lean_dec(v___x_1736_);
                            v___x_1739_ = crate::leanh::lean_box(0);
                            v_isShared_1740_ = v_isSharedCheck_1757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_1733_);
                        v_a_1758_ = crate::leanh::lean_ctor_get(v___x_1736_, 0);
                        v_isSharedCheck_1765_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1736_)) as u8;
                        if v_isSharedCheck_1765_ == 0 {
                            v___x_1760_ = v___x_1736_;
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1758_);
                            crate::leanh::lean_dec(v___x_1736_);
                            v___x_1760_ = crate::leanh::lean_box(0);
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1729_);
                    crate::leanh::lean_dec(v_a_1723_);
                    v___x_1766_ = crate::leanh::lean_box(0);
                    if v_isShared_1732_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1731_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1731_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_1737_) == 1 {
                    v_val_1741_ = crate::leanh::lean_ctor_get(v_a_1737_, 0);
                    v_isSharedCheck_1752_ = (!crate::leanh::lean_is_exclusive(v_a_1737_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1743_ = v_a_1737_;
                        v_isShared_1744_ = v_isSharedCheck_1752_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1741_);
                        crate::leanh::lean_dec(v_a_1737_);
                        v___x_1743_ = crate::leanh::lean_box(0);
                        v_isShared_1744_ = v_isSharedCheck_1752_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1737_);
                    crate::leanh::lean_dec(v_val_1733_);
                    v___x_1753_ = crate::leanh::lean_box(0);
                    if v_isShared_1740_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1753_);
                        v___x_1755_ = v___x_1739_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
                        v___x_1755_ = v_reuseFailAlloc_1756_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1745_, 0, v_val_1733_);
                crate::leanh::lean_ctor_set(v___x_1745_, 1, v_val_1741_);
                if v_isShared_1744_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1743_, 0, v___x_1745_);
                    v___x_1747_ = v___x_1743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1745_);
                    v___x_1747_ = v_reuseFailAlloc_1751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1740_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1739_, 0, v___x_1747_);
                    v___x_1749_ = v___x_1739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
                    v___x_1749_ = v_reuseFailAlloc_1750_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1749_;
            }
            6 => {
                return v___x_1755_;
            }
            7 => {
                if v_isShared_1761_ == 0 {
                    v___x_1763_ = v___x_1760_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
                    v___x_1763_ = v_reuseFailAlloc_1764_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1763_;
            }
            9 => {
                return v___x_1768_;
            }
            10 => {
                if v_isShared_1774_ == 0 {
                    v___x_1776_ = v___x_1773_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_1777_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
                    v___x_1776_ = v_reuseFailAlloc_1777_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_1776_;
            }
            12 => {
                if v_isShared_1782_ == 0 {
                    v___x_1784_ = v___x_1781_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
                    v___x_1784_ = v_reuseFailAlloc_1785_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1784_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed(
    mut v___x_1787_: *mut crate::leanh::LeanObject,
    mut v___x_1788_: *mut crate::leanh::LeanObject,
    mut v___x_1789_: *mut crate::leanh::LeanObject,
    mut v_u_1790_: *mut crate::leanh::LeanObject,
    mut v___x_1791_: *mut crate::leanh::LeanObject,
    mut v_type_1792_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1793_: *mut crate::leanh::LeanObject,
    mut v___y_1794_: *mut crate::leanh::LeanObject,
    mut v___y_1795_: *mut crate::leanh::LeanObject,
    mut v___y_1796_: *mut crate::leanh::LeanObject,
    mut v___y_1797_: *mut crate::leanh::LeanObject,
    mut v___y_1798_: *mut crate::leanh::LeanObject,
    mut v___y_1799_: *mut crate::leanh::LeanObject,
    mut v___y_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3810__boxed_1801_: u8 = 0;
    let mut v_res_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810__boxed_1801_ = (crate::leanh::lean_unbox(v___x_1788_) as u8);
    v_res_1802_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(
            v___x_1787_,
            v___x_3810__boxed_1801_,
            v___x_1789_,
            v_u_1790_,
            v___x_1791_,
            v_type_1792_,
            v_semiringInst_1793_,
            v___y_1794_,
            v___y_1795_,
            v___y_1796_,
            v___y_1797_,
            v___y_1798_,
            v___y_1799_,
        );
    crate::leanh::lean_dec(v___y_1799_);
    crate::leanh::lean_dec_ref(v___y_1798_);
    crate::leanh::lean_dec(v___y_1797_);
    crate::leanh::lean_dec_ref(v___y_1796_);
    crate::leanh::lean_dec(v___y_1795_);
    crate::leanh::lean_dec_ref(v___y_1794_);
    return v_res_1802_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = crate::leanh::lean_box(0);
    v___x_1807_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1;
    v___x_1808_ = l_Lean_mkConst(v___x_1807_, v___x_1806_);
    return v___x_1808_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1809_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2);
    v___x_1810_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1810_, 0, v___x_1809_);
    return v___x_1810_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(
    mut v_u_1811_: *mut crate::leanh::LeanObject,
    mut v_type_1812_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1813_: *mut crate::leanh::LeanObject,
    mut v_a_1814_: *mut crate::leanh::LeanObject,
    mut v_a_1815_: *mut crate::leanh::LeanObject,
    mut v_a_1816_: *mut crate::leanh::LeanObject,
    mut v_a_1817_: *mut crate::leanh::LeanObject,
    mut v_a_1818_: *mut crate::leanh::LeanObject,
    mut v_a_1819_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1821_ = crate::leanh::lean_box(0);
    v___x_1822_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3);
    v___x_1823_ = 0;
    v___x_1824_ = crate::leanh::lean_box(0);
    v___x_1825_ = crate::leanh::lean_box((v___x_1823_) as usize);
    v___f_1826_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
    crate::leanh::lean_closure_set(v___f_1826_, 0, v___x_1822_);
    crate::leanh::lean_closure_set(v___f_1826_, 1, v___x_1825_);
    crate::leanh::lean_closure_set(v___f_1826_, 2, v___x_1824_);
    crate::leanh::lean_closure_set(v___f_1826_, 3, v_u_1811_);
    crate::leanh::lean_closure_set(v___f_1826_, 4, v___x_1821_);
    crate::leanh::lean_closure_set(v___f_1826_, 5, v_type_1812_);
    crate::leanh::lean_closure_set(v___f_1826_, 6, v_semiringInst_1813_);
    v___x_1827_ = 0;
    v___x_1828_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_1826_, v___x_1827_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
    return v___x_1828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(
    mut v_u_1829_: *mut crate::leanh::LeanObject,
    mut v_type_1830_: *mut crate::leanh::LeanObject,
    mut v_semiringInst_1831_: *mut crate::leanh::LeanObject,
    mut v_a_1832_: *mut crate::leanh::LeanObject,
    mut v_a_1833_: *mut crate::leanh::LeanObject,
    mut v_a_1834_: *mut crate::leanh::LeanObject,
    mut v_a_1835_: *mut crate::leanh::LeanObject,
    mut v_a_1836_: *mut crate::leanh::LeanObject,
    mut v_a_1837_: *mut crate::leanh::LeanObject,
    mut v_a_1838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1839_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(
        v_u_1829_,
        v_type_1830_,
        v_semiringInst_1831_,
        v_a_1832_,
        v_a_1833_,
        v_a_1834_,
        v_a_1835_,
        v_a_1836_,
        v_a_1837_,
    );
    crate::leanh::lean_dec(v_a_1837_);
    crate::leanh::lean_dec_ref(v_a_1836_);
    crate::leanh::lean_dec(v_a_1835_);
    crate::leanh::lean_dec_ref(v_a_1834_);
    crate::leanh::lean_dec(v_a_1833_);
    crate::leanh::lean_dec_ref(v_a_1832_);
    return v_res_1839_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(
    mut v_u_1850_: *mut crate::leanh::LeanObject,
    mut v_type_1851_: *mut crate::leanh::LeanObject,
    mut v_a_1852_: *mut crate::leanh::LeanObject,
    mut v_a_1853_: *mut crate::leanh::LeanObject,
    mut v_a_1854_: *mut crate::leanh::LeanObject,
    mut v_a_1855_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleType_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v_val_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1857_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1;
                v___x_1858_ = crate::leanh::lean_box(0);
                v___x_1859_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1859_, 0, v_u_1850_);
                crate::leanh::lean_ctor_set(v___x_1859_, 1, v___x_1858_);
                crate::leanh::lean_inc_ref(v___x_1859_);
                v___x_1860_ = l_Lean_mkConst(v___x_1857_, v___x_1859_);
                crate::leanh::lean_inc_ref(v_type_1851_);
                v_natModuleType_1861_ = l_Lean_Expr_app___override(v___x_1860_, v_type_1851_);
                v___x_1862_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_natModuleType_1861_,
                    v_a_1852_,
                    v_a_1853_,
                    v_a_1854_,
                    v_a_1855_,
                );
                if crate::leanh::lean_obj_tag(v___x_1862_) == 0 {
                    v_a_1863_ = crate::leanh::lean_ctor_get(v___x_1862_, 0);
                    v_isSharedCheck_1876_ = (!crate::leanh::lean_is_exclusive(v___x_1862_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1865_ = v___x_1862_;
                        v_isShared_1866_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1863_);
                        crate::leanh::lean_dec(v___x_1862_);
                        v___x_1865_ = crate::leanh::lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1859_, 2);
                    crate::leanh::lean_dec_ref(v_type_1851_);
                    return v___x_1862_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1863_) == 1 {
                    crate::leanh::lean_del_object(v___x_1865_);
                    v_val_1867_ = crate::leanh::lean_ctor_get(v_a_1863_, 0);
                    crate::leanh::lean_inc(v_val_1867_);
                    crate::leanh::lean_dec_ref_known(v_a_1863_, 1);
                    v___x_1868_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3;
                    v___x_1869_ = l_Lean_mkConst(v___x_1868_, v___x_1859_);
                    v___x_1870_ = l_Lean_mkAppB(v___x_1869_, v_type_1851_, v_val_1867_);
                    v___x_1871_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_1870_,
                        v_a_1852_,
                        v_a_1853_,
                        v_a_1854_,
                        v_a_1855_,
                    );
                    return v___x_1871_;
                } else {
                    crate::leanh::lean_dec(v_a_1863_);
                    crate::leanh::lean_dec_ref_known(v___x_1859_, 2);
                    crate::leanh::lean_dec_ref(v_type_1851_);
                    v___x_1872_ = crate::leanh::lean_box(0);
                    if v_isShared_1866_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1865_, 0, v___x_1872_);
                        v___x_1874_ = v___x_1865_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
                        v___x_1874_ = v_reuseFailAlloc_1875_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1874_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___boxed(
    mut v_u_1877_: *mut crate::leanh::LeanObject,
    mut v_type_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
    mut v_a_1882_: *mut crate::leanh::LeanObject,
    mut v_a_1883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1884_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_1877_, v_type_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
    crate::leanh::lean_dec(v_a_1882_);
    crate::leanh::lean_dec_ref(v_a_1881_);
    crate::leanh::lean_dec(v_a_1880_);
    crate::leanh::lean_dec_ref(v_a_1879_);
    return v_res_1884_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(
    mut v_u_1885_: *mut crate::leanh::LeanObject,
    mut v_type_1886_: *mut crate::leanh::LeanObject,
    mut v_a_1887_: *mut crate::leanh::LeanObject,
    mut v_a_1888_: *mut crate::leanh::LeanObject,
    mut v_a_1889_: *mut crate::leanh::LeanObject,
    mut v_a_1890_: *mut crate::leanh::LeanObject,
    mut v_a_1891_: *mut crate::leanh::LeanObject,
    mut v_a_1892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_1885_, v_type_1886_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
    return v___x_1894_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(
    mut v_u_1895_: *mut crate::leanh::LeanObject,
    mut v_type_1896_: *mut crate::leanh::LeanObject,
    mut v_a_1897_: *mut crate::leanh::LeanObject,
    mut v_a_1898_: *mut crate::leanh::LeanObject,
    mut v_a_1899_: *mut crate::leanh::LeanObject,
    mut v_a_1900_: *mut crate::leanh::LeanObject,
    mut v_a_1901_: *mut crate::leanh::LeanObject,
    mut v_a_1902_: *mut crate::leanh::LeanObject,
    mut v_a_1903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1904_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(
            v_u_1895_,
            v_type_1896_,
            v_a_1897_,
            v_a_1898_,
            v_a_1899_,
            v_a_1900_,
            v_a_1901_,
            v_a_1902_,
        );
    crate::leanh::lean_dec(v_a_1902_);
    crate::leanh::lean_dec_ref(v_a_1901_);
    crate::leanh::lean_dec(v_a_1900_);
    crate::leanh::lean_dec_ref(v_a_1899_);
    crate::leanh::lean_dec(v_a_1898_);
    crate::leanh::lean_dec_ref(v_a_1897_);
    return v_res_1904_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0(
    mut v___x_1905_: *mut crate::leanh::LeanObject,
    mut v_s_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_1907_ = crate::leanh::lean_ctor_get(v_s_1906_, 0);
                v_rings_1908_ = crate::leanh::lean_ctor_get(v_s_1906_, 1);
                v_semirings_1909_ = crate::leanh::lean_ctor_get(v_s_1906_, 2);
                v_ncRings_1910_ = crate::leanh::lean_ctor_get(v_s_1906_, 3);
                v_ncSemirings_1911_ = crate::leanh::lean_ctor_get(v_s_1906_, 4);
                v_typeClassify_1912_ = crate::leanh::lean_ctor_get(v_s_1906_, 5);
                v_isSharedCheck_1920_ = (!crate::leanh::lean_is_exclusive(v_s_1906_)) as u8;
                if v_isSharedCheck_1920_ == 0 {
                    v___x_1914_ = v_s_1906_;
                    v_isShared_1915_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_1912_);
                    crate::leanh::lean_inc(v_ncSemirings_1911_);
                    crate::leanh::lean_inc(v_ncRings_1910_);
                    crate::leanh::lean_inc(v_semirings_1909_);
                    crate::leanh::lean_inc(v_rings_1908_);
                    crate::leanh::lean_inc(v_exp_1907_);
                    crate::leanh::lean_dec(v_s_1906_);
                    v___x_1914_ = crate::leanh::lean_box(0);
                    v_isShared_1915_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1916_ = lean_array_push(v_rings_1908_, v___x_1905_);
                if v_isShared_1915_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1914_, 1, v___x_1916_);
                    v___x_1918_ = v___x_1914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_exp_1907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_semirings_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_ncRings_1910_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_ncSemirings_1911_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_typeClassify_1912_);
                    v___x_1918_ = v_reuseFailAlloc_1919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1918_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(
    mut v_type_1950_: *mut crate::leanh::LeanObject,
    mut v_a_1951_: *mut crate::leanh::LeanObject,
    mut v_a_1952_: *mut crate::leanh::LeanObject,
    mut v_a_1953_: *mut crate::leanh::LeanObject,
    mut v_a_1954_: *mut crate::leanh::LeanObject,
    mut v_a_1955_: *mut crate::leanh::LeanObject,
    mut v_a_1956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_val_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_unused_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_a_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v_a_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_a_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v___x_2042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_a_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_isSharedCheck_2053_: u8 = 0;
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_1950_);
                v___x_1958_ = l_Lean_Meta_getDecLevel(
                    v_type_1950_,
                    v_a_1953_,
                    v_a_1954_,
                    v_a_1955_,
                    v_a_1956_,
                );
                if crate::leanh::lean_obj_tag(v___x_1958_) == 0 {
                    v_a_1959_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                    crate::leanh::lean_inc_n(v_a_1959_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1958_, 1);
                    v___x_1960_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1;
                    v___x_1961_ = crate::leanh::lean_box(0);
                    v___x_1962_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1962_, 0, v_a_1959_);
                    crate::leanh::lean_ctor_set(v___x_1962_, 1, v___x_1961_);
                    crate::leanh::lean_inc_ref(v___x_1962_);
                    v___x_1963_ = l_Lean_mkConst(v___x_1960_, v___x_1962_);
                    crate::leanh::lean_inc_ref(v_type_1950_);
                    v___x_1964_ = l_Lean_Expr_app___override(v___x_1963_, v_type_1950_);
                    v___x_1965_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_1964_,
                        v_a_1953_,
                        v_a_1954_,
                        v_a_1955_,
                        v_a_1956_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1965_) == 0 {
                        v_a_1966_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                        v_isSharedCheck_2058_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v___x_1968_ = v___x_1965_;
                            v_isShared_1969_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1966_);
                            crate::leanh::lean_dec(v___x_1965_);
                            v___x_1968_ = crate::leanh::lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_1962_, 2);
                        crate::leanh::lean_dec(v_a_1959_);
                        crate::leanh::lean_dec_ref(v_type_1950_);
                        v_a_2059_ = crate::leanh::lean_ctor_get(v___x_1965_, 0);
                        v_isSharedCheck_2066_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1965_)) as u8;
                        if v_isSharedCheck_2066_ == 0 {
                            v___x_2061_ = v___x_1965_;
                            v_isShared_2062_ = v_isSharedCheck_2066_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2059_);
                            crate::leanh::lean_dec(v___x_1965_);
                            v___x_2061_ = crate::leanh::lean_box(0);
                            v_isShared_2062_ = v_isSharedCheck_2066_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_1950_);
                    v_a_2067_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                    v_isSharedCheck_2074_ = (!crate::leanh::lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_1958_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2067_);
                        crate::leanh::lean_dec(v___x_1958_);
                        v___x_2069_ = crate::leanh::lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1966_) == 1 {
                    crate::leanh::lean_del_object(v___x_1968_);
                    v_val_1970_ = crate::leanh::lean_ctor_get(v_a_1966_, 0);
                    v_isSharedCheck_2053_ = (!crate::leanh::lean_is_exclusive(v_a_1966_)) as u8;
                    if v_isSharedCheck_2053_ == 0 {
                        v___x_1972_ = v_a_1966_;
                        v_isShared_1973_ = v_isSharedCheck_2053_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1970_);
                        crate::leanh::lean_dec(v_a_1966_);
                        v___x_1972_ = crate::leanh::lean_box(0);
                        v_isShared_1973_ = v_isSharedCheck_2053_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1966_);
                    crate::leanh::lean_dec_ref_known(v___x_1962_, 2);
                    crate::leanh::lean_dec(v_a_1959_);
                    crate::leanh::lean_dec_ref(v_type_1950_);
                    v___x_2054_ = crate::leanh::lean_box(0);
                    if v_isShared_1969_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1968_, 0, v___x_2054_);
                        v___x_2056_ = v___x_1968_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2057_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                        v___x_2056_ = v_reuseFailAlloc_2057_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1974_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3;
                crate::leanh::lean_inc_ref_n(v___x_1962_, 3);
                v___x_1975_ = l_Lean_mkConst(v___x_1974_, v___x_1962_);
                crate::leanh::lean_inc(v_val_1970_);
                crate::leanh::lean_inc_ref_n(v_type_1950_, 4);
                v___x_1976_ = l_Lean_mkAppB(v___x_1975_, v_type_1950_, v_val_1970_);
                v___x_1977_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6;
                v___x_1978_ = l_Lean_mkConst(v___x_1977_, v___x_1962_);
                crate::leanh::lean_inc_ref(v___x_1976_);
                v___x_1979_ = l_Lean_mkAppB(v___x_1978_, v_type_1950_, v___x_1976_);
                v___x_1980_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8;
                v___x_1981_ = l_Lean_mkConst(v___x_1980_, v___x_1962_);
                crate::leanh::lean_inc_ref_n(v___x_1979_, 2);
                v___x_1982_ = l_Lean_mkAppB(v___x_1981_, v_type_1950_, v___x_1979_);
                crate::leanh::lean_inc(v_a_1959_);
                v___x_1983_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_1959_, v_type_1950_, v___x_1979_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
                if crate::leanh::lean_obj_tag(v___x_1983_) == 0 {
                    v_a_1984_ = crate::leanh::lean_ctor_get(v___x_1983_, 0);
                    crate::leanh::lean_inc(v_a_1984_);
                    crate::leanh::lean_dec_ref_known(v___x_1983_, 1);
                    crate::leanh::lean_inc_ref(v_type_1950_);
                    crate::leanh::lean_inc(v_a_1959_);
                    v___x_1985_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_a_1959_, v_type_1950_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
                    if crate::leanh::lean_obj_tag(v___x_1985_) == 0 {
                        v_a_1986_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                        crate::leanh::lean_inc(v_a_1986_);
                        crate::leanh::lean_dec_ref_known(v___x_1985_, 1);
                        v___x_1987_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10;
                        v___x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1962_);
                        crate::leanh::lean_inc_ref(v_type_1950_);
                        v___x_1989_ = l_Lean_Expr_app___override(v___x_1988_, v_type_1950_);
                        v___x_1990_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_1989_,
                            v_a_1953_,
                            v_a_1954_,
                            v_a_1955_,
                            v_a_1956_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1990_) == 0 {
                            v_a_1991_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                            crate::leanh::lean_inc(v_a_1991_);
                            crate::leanh::lean_dec_ref_known(v___x_1990_, 1);
                            v___x_1992_ =
                                l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1952_, v_a_1955_);
                            if crate::leanh::lean_obj_tag(v___x_1992_) == 0 {
                                v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                                crate::leanh::lean_inc(v_a_1993_);
                                crate::leanh::lean_dec_ref_known(v___x_1992_, 1);
                                v_rings_1994_ = crate::leanh::lean_ctor_get(v_a_1993_, 1);
                                crate::leanh::lean_inc_ref(v_rings_1994_);
                                crate::leanh::lean_dec(v_a_1993_);
                                v___x_1995_ = crate::leanh::lean_box(0);
                                v___x_1996_ = lean_array_get_size(v_rings_1994_);
                                crate::leanh::lean_dec_ref(v_rings_1994_);
                                v___x_1997_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1997_, 0, v___x_1996_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 1, v_type_1950_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 2, v_a_1959_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 3, v___x_1976_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 4, v___x_1979_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 5, v_a_1984_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 6, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 7, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 8, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 9, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 10, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 11, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 12, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1997_, 13, v___x_1995_);
                                v___x_1998_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1998_, 0, v___x_1997_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 1, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 2, v___x_1995_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 3, v___x_1982_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 4, v_val_1970_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 5, v_a_1986_);
                                crate::leanh::lean_ctor_set(v___x_1998_, 6, v_a_1991_);
                                v___f_1999_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                                crate::leanh::lean_closure_set(v___f_1999_, 0, v___x_1998_);
                                v___x_2000_ = l_Lean_Meta_Sym_Arith_arithExt;
                                v___x_2001_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2000_, v___f_1999_, v_a_1952_);
                                if crate::leanh::lean_obj_tag(v___x_2001_) == 0 {
                                    v_isSharedCheck_2011_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2001_)) as u8;
                                    if v_isSharedCheck_2011_ == 0 {
                                        v_unused_2012_ =
                                            crate::leanh::lean_ctor_get(v___x_2001_, 0);
                                        crate::leanh::lean_dec(v_unused_2012_);
                                        v___x_2003_ = v___x_2001_;
                                        v_isShared_2004_ = v_isSharedCheck_2011_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_2001_);
                                        v___x_2003_ = crate::leanh::lean_box(0);
                                        v_isShared_2004_ = v_isSharedCheck_2011_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_del_object(v___x_1972_);
                                    v_a_2013_ = crate::leanh::lean_ctor_get(v___x_2001_, 0);
                                    v_isSharedCheck_2020_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2001_)) as u8;
                                    if v_isSharedCheck_2020_ == 0 {
                                        v___x_2015_ = v___x_2001_;
                                        v_isShared_2016_ = v_isSharedCheck_2020_;
                                        state = 6;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2013_);
                                        crate::leanh::lean_dec(v___x_2001_);
                                        v___x_2015_ = crate::leanh::lean_box(0);
                                        v_isShared_2016_ = v_isSharedCheck_2020_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_1991_);
                                crate::leanh::lean_dec(v_a_1986_);
                                crate::leanh::lean_dec(v_a_1984_);
                                crate::leanh::lean_dec_ref(v___x_1982_);
                                crate::leanh::lean_dec_ref(v___x_1979_);
                                crate::leanh::lean_dec_ref(v___x_1976_);
                                crate::leanh::lean_del_object(v___x_1972_);
                                crate::leanh::lean_dec(v_val_1970_);
                                crate::leanh::lean_dec(v_a_1959_);
                                crate::leanh::lean_dec_ref(v_type_1950_);
                                v_a_2021_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                                v_isSharedCheck_2028_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                                if v_isSharedCheck_2028_ == 0 {
                                    v___x_2023_ = v___x_1992_;
                                    v_isShared_2024_ = v_isSharedCheck_2028_;
                                    state = 8;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2021_);
                                    crate::leanh::lean_dec(v___x_1992_);
                                    v___x_2023_ = crate::leanh::lean_box(0);
                                    v_isShared_2024_ = v_isSharedCheck_2028_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1986_);
                            crate::leanh::lean_dec(v_a_1984_);
                            crate::leanh::lean_dec_ref(v___x_1982_);
                            crate::leanh::lean_dec_ref(v___x_1979_);
                            crate::leanh::lean_dec_ref(v___x_1976_);
                            crate::leanh::lean_del_object(v___x_1972_);
                            crate::leanh::lean_dec(v_val_1970_);
                            crate::leanh::lean_dec(v_a_1959_);
                            crate::leanh::lean_dec_ref(v_type_1950_);
                            v_a_2029_ = crate::leanh::lean_ctor_get(v___x_1990_, 0);
                            v_isSharedCheck_2036_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1990_)) as u8;
                            if v_isSharedCheck_2036_ == 0 {
                                v___x_2031_ = v___x_1990_;
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2029_);
                                crate::leanh::lean_dec(v___x_1990_);
                                v___x_2031_ = crate::leanh::lean_box(0);
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1984_);
                        crate::leanh::lean_dec_ref(v___x_1982_);
                        crate::leanh::lean_dec_ref(v___x_1979_);
                        crate::leanh::lean_dec_ref(v___x_1976_);
                        crate::leanh::lean_del_object(v___x_1972_);
                        crate::leanh::lean_dec(v_val_1970_);
                        crate::leanh::lean_dec_ref_known(v___x_1962_, 2);
                        crate::leanh::lean_dec(v_a_1959_);
                        crate::leanh::lean_dec_ref(v_type_1950_);
                        v_a_2037_ = crate::leanh::lean_ctor_get(v___x_1985_, 0);
                        v_isSharedCheck_2044_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1985_)) as u8;
                        if v_isSharedCheck_2044_ == 0 {
                            v___x_2039_ = v___x_1985_;
                            v_isShared_2040_ = v_isSharedCheck_2044_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2037_);
                            crate::leanh::lean_dec(v___x_1985_);
                            v___x_2039_ = crate::leanh::lean_box(0);
                            v_isShared_2040_ = v_isSharedCheck_2044_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_1982_);
                    crate::leanh::lean_dec_ref(v___x_1979_);
                    crate::leanh::lean_dec_ref(v___x_1976_);
                    crate::leanh::lean_del_object(v___x_1972_);
                    crate::leanh::lean_dec(v_val_1970_);
                    crate::leanh::lean_dec_ref_known(v___x_1962_, 2);
                    crate::leanh::lean_dec(v_a_1959_);
                    crate::leanh::lean_dec_ref(v_type_1950_);
                    v_a_2045_ = crate::leanh::lean_ctor_get(v___x_1983_, 0);
                    v_isSharedCheck_2052_ = (!crate::leanh::lean_is_exclusive(v___x_1983_)) as u8;
                    if v_isSharedCheck_2052_ == 0 {
                        v___x_2047_ = v___x_1983_;
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2045_);
                        crate::leanh::lean_dec(v___x_1983_);
                        v___x_2047_ = crate::leanh::lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1973_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1972_, 0, v___x_1996_);
                    v___x_2006_ = v___x_1972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1996_);
                    v___x_2006_ = v_reuseFailAlloc_2010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2004_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2003_, 0, v___x_2006_);
                    v___x_2008_ = v___x_2003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
                    v___x_2008_ = v_reuseFailAlloc_2009_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2008_;
            }
            6 => {
                if v_isShared_2016_ == 0 {
                    v___x_2018_ = v___x_2015_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
                    v___x_2018_ = v_reuseFailAlloc_2019_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2018_;
            }
            8 => {
                if v_isShared_2024_ == 0 {
                    v___x_2026_ = v___x_2023_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2027_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
                    v___x_2026_ = v_reuseFailAlloc_2027_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2026_;
            }
            10 => {
                if v_isShared_2032_ == 0 {
                    v___x_2034_ = v___x_2031_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
                    v___x_2034_ = v_reuseFailAlloc_2035_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2034_;
            }
            12 => {
                if v_isShared_2040_ == 0 {
                    v___x_2042_ = v___x_2039_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2043_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
                    v___x_2042_ = v_reuseFailAlloc_2043_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2042_;
            }
            14 => {
                if v_isShared_2048_ == 0 {
                    v___x_2050_ = v___x_2047_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2051_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
                    v___x_2050_ = v_reuseFailAlloc_2051_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2050_;
            }
            16 => {
                return v___x_2056_;
            }
            17 => {
                if v_isShared_2062_ == 0 {
                    v___x_2064_ = v___x_2061_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2065_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
                    v___x_2064_ = v_reuseFailAlloc_2065_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2064_;
            }
            19 => {
                if v_isShared_2070_ == 0 {
                    v___x_2072_ = v___x_2069_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2073_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
                    v___x_2072_ = v_reuseFailAlloc_2073_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2072_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___boxed(
    mut v_type_2075_: *mut crate::leanh::LeanObject,
    mut v_a_2076_: *mut crate::leanh::LeanObject,
    mut v_a_2077_: *mut crate::leanh::LeanObject,
    mut v_a_2078_: *mut crate::leanh::LeanObject,
    mut v_a_2079_: *mut crate::leanh::LeanObject,
    mut v_a_2080_: *mut crate::leanh::LeanObject,
    mut v_a_2081_: *mut crate::leanh::LeanObject,
    mut v_a_2082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2083_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(
        v_type_2075_,
        v_a_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
        v_a_2081_,
    );
    crate::leanh::lean_dec(v_a_2081_);
    crate::leanh::lean_dec_ref(v_a_2080_);
    crate::leanh::lean_dec(v_a_2079_);
    crate::leanh::lean_dec_ref(v_a_2078_);
    crate::leanh::lean_dec(v_a_2077_);
    crate::leanh::lean_dec_ref(v_a_2076_);
    return v_res_2083_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(
    mut v___x_2084_: *mut crate::leanh::LeanObject,
    mut v_s_2085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2086_ = crate::leanh::lean_ctor_get(v_s_2085_, 0);
                v_rings_2087_ = crate::leanh::lean_ctor_get(v_s_2085_, 1);
                v_semirings_2088_ = crate::leanh::lean_ctor_get(v_s_2085_, 2);
                v_ncRings_2089_ = crate::leanh::lean_ctor_get(v_s_2085_, 3);
                v_ncSemirings_2090_ = crate::leanh::lean_ctor_get(v_s_2085_, 4);
                v_typeClassify_2091_ = crate::leanh::lean_ctor_get(v_s_2085_, 5);
                v_isSharedCheck_2099_ = (!crate::leanh::lean_is_exclusive(v_s_2085_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2093_ = v_s_2085_;
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_2091_);
                    crate::leanh::lean_inc(v_ncSemirings_2090_);
                    crate::leanh::lean_inc(v_ncRings_2089_);
                    crate::leanh::lean_inc(v_semirings_2088_);
                    crate::leanh::lean_inc(v_rings_2087_);
                    crate::leanh::lean_inc(v_exp_2086_);
                    crate::leanh::lean_dec(v_s_2085_);
                    v___x_2093_ = crate::leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2095_ = lean_array_push(v_ncRings_2089_, v___x_2084_);
                if v_isShared_2094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2093_, 3, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_exp_2086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_rings_2087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_semirings_2088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 3, v___x_2095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_ncSemirings_2090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2098_, 5, v_typeClassify_2091_);
                    v___x_2097_ = v_reuseFailAlloc_2098_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(
    mut v_type_2104_: *mut crate::leanh::LeanObject,
    mut v_a_2105_: *mut crate::leanh::LeanObject,
    mut v_a_2106_: *mut crate::leanh::LeanObject,
    mut v_a_2107_: *mut crate::leanh::LeanObject,
    mut v_a_2108_: *mut crate::leanh::LeanObject,
    mut v_a_2109_: *mut crate::leanh::LeanObject,
    mut v_a_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v_val_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v___x_2128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v_unused_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_a_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_a_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v___x_2178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_a_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_a_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2104_);
                v___x_2112_ = l_Lean_Meta_getDecLevel(
                    v_type_2104_,
                    v_a_2107_,
                    v_a_2108_,
                    v_a_2109_,
                    v_a_2110_,
                );
                if crate::leanh::lean_obj_tag(v___x_2112_) == 0 {
                    v_a_2113_ = crate::leanh::lean_ctor_get(v___x_2112_, 0);
                    crate::leanh::lean_inc_n(v_a_2113_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2112_, 1);
                    v___x_2114_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0;
                    v___x_2115_ = crate::leanh::lean_box(0);
                    v___x_2116_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2116_, 0, v_a_2113_);
                    crate::leanh::lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                    crate::leanh::lean_inc_ref(v___x_2116_);
                    v___x_2117_ = l_Lean_mkConst(v___x_2114_, v___x_2116_);
                    crate::leanh::lean_inc_ref(v_type_2104_);
                    v___x_2118_ = l_Lean_Expr_app___override(v___x_2117_, v_type_2104_);
                    v___x_2119_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2118_,
                        v_a_2107_,
                        v_a_2108_,
                        v_a_2109_,
                        v_a_2110_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2119_) == 0 {
                        v_a_2120_ = crate::leanh::lean_ctor_get(v___x_2119_, 0);
                        v_isSharedCheck_2182_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2119_)) as u8;
                        if v_isSharedCheck_2182_ == 0 {
                            v___x_2122_ = v___x_2119_;
                            v_isShared_2123_ = v_isSharedCheck_2182_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2120_);
                            crate::leanh::lean_dec(v___x_2119_);
                            v___x_2122_ = crate::leanh::lean_box(0);
                            v_isShared_2123_ = v_isSharedCheck_2182_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2116_, 2);
                        crate::leanh::lean_dec(v_a_2113_);
                        crate::leanh::lean_dec_ref(v_type_2104_);
                        v_a_2183_ = crate::leanh::lean_ctor_get(v___x_2119_, 0);
                        v_isSharedCheck_2190_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2119_)) as u8;
                        if v_isSharedCheck_2190_ == 0 {
                            v___x_2185_ = v___x_2119_;
                            v_isShared_2186_ = v_isSharedCheck_2190_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2183_);
                            crate::leanh::lean_dec(v___x_2119_);
                            v___x_2185_ = crate::leanh::lean_box(0);
                            v_isShared_2186_ = v_isSharedCheck_2190_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v_a_2191_ = crate::leanh::lean_ctor_get(v___x_2112_, 0);
                    v_isSharedCheck_2198_ = (!crate::leanh::lean_is_exclusive(v___x_2112_)) as u8;
                    if v_isSharedCheck_2198_ == 0 {
                        v___x_2193_ = v___x_2112_;
                        v_isShared_2194_ = v_isSharedCheck_2198_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2191_);
                        crate::leanh::lean_dec(v___x_2112_);
                        v___x_2193_ = crate::leanh::lean_box(0);
                        v_isShared_2194_ = v_isSharedCheck_2198_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2120_) == 1 {
                    crate::leanh::lean_del_object(v___x_2122_);
                    v_val_2124_ = crate::leanh::lean_ctor_get(v_a_2120_, 0);
                    v_isSharedCheck_2177_ = (!crate::leanh::lean_is_exclusive(v_a_2120_)) as u8;
                    if v_isSharedCheck_2177_ == 0 {
                        v___x_2126_ = v_a_2120_;
                        v_isShared_2127_ = v_isSharedCheck_2177_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2124_);
                        crate::leanh::lean_dec(v_a_2120_);
                        v___x_2126_ = crate::leanh::lean_box(0);
                        v_isShared_2127_ = v_isSharedCheck_2177_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2120_);
                    crate::leanh::lean_dec_ref_known(v___x_2116_, 2);
                    crate::leanh::lean_dec(v_a_2113_);
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v___x_2178_ = crate::leanh::lean_box(0);
                    if v_isShared_2123_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2122_, 0, v___x_2178_);
                        v___x_2180_ = v___x_2122_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
                        v___x_2180_ = v_reuseFailAlloc_2181_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2128_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6;
                v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2116_);
                crate::leanh::lean_inc(v_val_2124_);
                crate::leanh::lean_inc_ref_n(v_type_2104_, 2);
                v___x_2130_ = l_Lean_mkAppB(v___x_2129_, v_type_2104_, v_val_2124_);
                crate::leanh::lean_inc_ref(v___x_2130_);
                crate::leanh::lean_inc(v_a_2113_);
                v___x_2131_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_2113_, v_type_2104_, v___x_2130_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
                if crate::leanh::lean_obj_tag(v___x_2131_) == 0 {
                    v_a_2132_ = crate::leanh::lean_ctor_get(v___x_2131_, 0);
                    crate::leanh::lean_inc(v_a_2132_);
                    crate::leanh::lean_dec_ref_known(v___x_2131_, 1);
                    v___x_2133_ =
                        l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2106_, v_a_2109_);
                    if crate::leanh::lean_obj_tag(v___x_2133_) == 0 {
                        v_a_2134_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                        crate::leanh::lean_inc(v_a_2134_);
                        crate::leanh::lean_dec_ref_known(v___x_2133_, 1);
                        v_ncRings_2135_ = crate::leanh::lean_ctor_get(v_a_2134_, 3);
                        crate::leanh::lean_inc_ref(v_ncRings_2135_);
                        crate::leanh::lean_dec(v_a_2134_);
                        v___x_2136_ = lean_array_get_size(v_ncRings_2135_);
                        crate::leanh::lean_dec_ref(v_ncRings_2135_);
                        v___x_2137_ = crate::leanh::lean_box(0);
                        v___x_2138_ = crate::leanh::lean_alloc_ctor(0, 14, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2138_, 0, v___x_2136_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 1, v_type_2104_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 2, v_a_2113_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 3, v_val_2124_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 4, v___x_2130_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 5, v_a_2132_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 6, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 7, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 8, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 9, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 10, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 11, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 12, v___x_2137_);
                        crate::leanh::lean_ctor_set(v___x_2138_, 13, v___x_2137_);
                        v___f_2139_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                        crate::leanh::lean_closure_set(v___f_2139_, 0, v___x_2138_);
                        v___x_2140_ = l_Lean_Meta_Sym_Arith_arithExt;
                        v___x_2141_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2140_, v___f_2139_, v_a_2106_);
                        if crate::leanh::lean_obj_tag(v___x_2141_) == 0 {
                            v_isSharedCheck_2151_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2141_)) as u8;
                            if v_isSharedCheck_2151_ == 0 {
                                v_unused_2152_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                                crate::leanh::lean_dec(v_unused_2152_);
                                v___x_2143_ = v___x_2141_;
                                v_isShared_2144_ = v_isSharedCheck_2151_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2141_);
                                v___x_2143_ = crate::leanh::lean_box(0);
                                v_isShared_2144_ = v_isSharedCheck_2151_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2126_);
                            v_a_2153_ = crate::leanh::lean_ctor_get(v___x_2141_, 0);
                            v_isSharedCheck_2160_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2141_)) as u8;
                            if v_isSharedCheck_2160_ == 0 {
                                v___x_2155_ = v___x_2141_;
                                v_isShared_2156_ = v_isSharedCheck_2160_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2153_);
                                crate::leanh::lean_dec(v___x_2141_);
                                v___x_2155_ = crate::leanh::lean_box(0);
                                v_isShared_2156_ = v_isSharedCheck_2160_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2132_);
                        crate::leanh::lean_dec_ref(v___x_2130_);
                        crate::leanh::lean_del_object(v___x_2126_);
                        crate::leanh::lean_dec(v_val_2124_);
                        crate::leanh::lean_dec(v_a_2113_);
                        crate::leanh::lean_dec_ref(v_type_2104_);
                        v_a_2161_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                        v_isSharedCheck_2168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2133_)) as u8;
                        if v_isSharedCheck_2168_ == 0 {
                            v___x_2163_ = v___x_2133_;
                            v_isShared_2164_ = v_isSharedCheck_2168_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2161_);
                            crate::leanh::lean_dec(v___x_2133_);
                            v___x_2163_ = crate::leanh::lean_box(0);
                            v_isShared_2164_ = v_isSharedCheck_2168_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_2130_);
                    crate::leanh::lean_del_object(v___x_2126_);
                    crate::leanh::lean_dec(v_val_2124_);
                    crate::leanh::lean_dec(v_a_2113_);
                    crate::leanh::lean_dec_ref(v_type_2104_);
                    v_a_2169_ = crate::leanh::lean_ctor_get(v___x_2131_, 0);
                    v_isSharedCheck_2176_ = (!crate::leanh::lean_is_exclusive(v___x_2131_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2171_ = v___x_2131_;
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2169_);
                        crate::leanh::lean_dec(v___x_2131_);
                        v___x_2171_ = crate::leanh::lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2127_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2126_, 0, v___x_2136_);
                    v___x_2146_ = v___x_2126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2150_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2136_);
                    v___x_2146_ = v_reuseFailAlloc_2150_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2143_, 0, v___x_2146_);
                    v___x_2148_ = v___x_2143_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
                    v___x_2148_ = v_reuseFailAlloc_2149_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2148_;
            }
            6 => {
                if v_isShared_2156_ == 0 {
                    v___x_2158_ = v___x_2155_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2159_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
                    v___x_2158_ = v_reuseFailAlloc_2159_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2158_;
            }
            8 => {
                if v_isShared_2164_ == 0 {
                    v___x_2166_ = v___x_2163_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
                    v___x_2166_ = v_reuseFailAlloc_2167_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2166_;
            }
            10 => {
                if v_isShared_2172_ == 0 {
                    v___x_2174_ = v___x_2171_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
                    v___x_2174_ = v_reuseFailAlloc_2175_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2174_;
            }
            12 => {
                return v___x_2180_;
            }
            13 => {
                if v_isShared_2186_ == 0 {
                    v___x_2188_ = v___x_2185_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
                    v___x_2188_ = v_reuseFailAlloc_2189_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2188_;
            }
            15 => {
                if v_isShared_2194_ == 0 {
                    v___x_2196_ = v___x_2193_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2197_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
                    v___x_2196_ = v_reuseFailAlloc_2197_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2196_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___boxed(
    mut v_type_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2207_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(
            v_type_2199_,
            v_a_2200_,
            v_a_2201_,
            v_a_2202_,
            v_a_2203_,
            v_a_2204_,
            v_a_2205_,
        );
    crate::leanh::lean_dec(v_a_2205_);
    crate::leanh::lean_dec_ref(v_a_2204_);
    crate::leanh::lean_dec(v_a_2203_);
    crate::leanh::lean_dec_ref(v_a_2202_);
    crate::leanh::lean_dec(v_a_2201_);
    crate::leanh::lean_dec_ref(v_a_2200_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_2208_: *mut crate::leanh::LeanObject,
    mut v_x_2209_: *mut crate::leanh::LeanObject,
    mut v_x_2210_: *mut crate::leanh::LeanObject,
    mut v_x_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2212_ = crate::leanh::lean_ctor_get(v_x_2208_, 0);
                v_vs_2213_ = crate::leanh::lean_ctor_get(v_x_2208_, 1);
                v_isSharedCheck_2237_ = (!crate::leanh::lean_is_exclusive(v_x_2208_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v___x_2215_ = v_x_2208_;
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2213_);
                    crate::leanh::lean_inc(v_ks_2212_);
                    crate::leanh::lean_dec(v_x_2208_);
                    v___x_2215_ = crate::leanh::lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = lean_array_get_size(v_ks_2212_);
                v___x_2218_ = lean_nat_dec_lt(v_x_2209_, v___x_2217_);
                if v___x_2218_ == 0 {
                    crate::leanh::lean_dec(v_x_2209_);
                    v___x_2219_ = lean_array_push(v_ks_2212_, v_x_2210_);
                    v___x_2220_ = lean_array_push(v_vs_2213_, v_x_2211_);
                    if v_isShared_2216_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2220_);
                        crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2219_);
                        v___x_2222_ = v___x_2215_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2223_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2220_);
                        v___x_2222_ = v_reuseFailAlloc_2223_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2224_ = lean_array_fget_borrowed(v_ks_2212_, v_x_2209_);
                    v___x_2225_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_2210_,
                            v_k_x27_2224_,
                        );
                    if v___x_2225_ == 0 {
                        if v_isShared_2216_ == 0 {
                            v___x_2227_ = v___x_2215_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2231_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_ks_2212_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_vs_2213_);
                            v___x_2227_ = v_reuseFailAlloc_2231_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2232_ = lean_array_fset(v_ks_2212_, v_x_2209_, v_x_2210_);
                        v___x_2233_ = lean_array_fset(v_vs_2213_, v_x_2209_, v_x_2211_);
                        crate::leanh::lean_dec(v_x_2209_);
                        if v_isShared_2216_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2215_, 1, v___x_2233_);
                            crate::leanh::lean_ctor_set(v___x_2215_, 0, v___x_2232_);
                            v___x_2235_ = v___x_2215_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2236_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
                            v___x_2235_ = v_reuseFailAlloc_2236_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2222_;
            }
            3 => {
                v___x_2228_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2229_ = lean_nat_add(v_x_2209_, v___x_2228_);
                crate::leanh::lean_dec(v_x_2209_);
                v_x_2208_ = v___x_2227_;
                v_x_2209_ = v___x_2229_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_2238_: *mut crate::leanh::LeanObject,
    mut v_k_2239_: *mut crate::leanh::LeanObject,
    mut v_v_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2241_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2242_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_2238_, v___x_2241_, v_k_2239_, v_v_2240_);
    return v___x_2242_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut v___x_2245_: usize = 0;
    v___x_2243_ = 5usize;
    v___x_2244_ = 1usize;
    v___x_2245_ = lean_usize_shift_left(v___x_2244_, v___x_2243_);
    return v___x_2245_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_2246_: usize = 0;
    let mut v___x_2247_: usize = 0;
    let mut v___x_2248_: usize = 0;
    v___x_2246_ = 1usize;
    v___x_2247_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_2248_ = lean_usize_sub(v___x_2247_, v___x_2246_);
    return v___x_2248_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: usize,
    mut v_x_2252_: usize,
    mut v_x_2253_: *mut crate::leanh::LeanObject,
    mut v_x_2254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: usize = 0;
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v_j_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_v_2266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_node_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: u8 = 0;
    let mut v_ks_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2250_) == 0 {
                    v_es_2255_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                    v___x_2256_ = 5usize;
                    v___x_2257_ = 1usize;
                    v___x_2258_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2259_ = lean_usize_land(v_x_2251_, v___x_2258_);
                    v_j_2260_ = lean_usize_to_nat(v___x_2259_);
                    v___x_2261_ = lean_array_get_size(v_es_2255_);
                    v___x_2262_ = lean_nat_dec_lt(v_j_2260_, v___x_2261_);
                    if v___x_2262_ == 0 {
                        crate::leanh::lean_dec(v_j_2260_);
                        crate::leanh::lean_dec(v_x_2254_);
                        crate::leanh::lean_dec_ref(v_x_2253_);
                        return v_x_2250_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2255_);
                        v_isSharedCheck_2299_ = (!crate::leanh::lean_is_exclusive(v_x_2250_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                            crate::leanh::lean_dec(v_unused_2300_);
                            v___x_2264_ = v_x_2250_;
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2250_);
                            v___x_2264_ = crate::leanh::lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2301_ = crate::leanh::lean_ctor_get(v_x_2250_, 0);
                    v_vs_2302_ = crate::leanh::lean_ctor_get(v_x_2250_, 1);
                    v_isSharedCheck_2322_ = (!crate::leanh::lean_is_exclusive(v_x_2250_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2304_ = v_x_2250_;
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2302_);
                        crate::leanh::lean_inc(v_ks_2301_);
                        crate::leanh::lean_dec(v_x_2250_);
                        v___x_2304_ = crate::leanh::lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2266_ = lean_array_fget(v_es_2255_, v_j_2260_);
                v___x_2267_ = crate::leanh::lean_box(0);
                v_xs_x27_2268_ = lean_array_fset(v_es_2255_, v_j_2260_, v___x_2267_);
                match crate::leanh::lean_obj_tag(v_v_2266_) {
                    0 => {
                        v_key_2275_ = crate::leanh::lean_ctor_get(v_v_2266_, 0);
                        v_val_2276_ = crate::leanh::lean_ctor_get(v_v_2266_, 1);
                        v_isSharedCheck_2286_ = (!crate::leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2286_ == 0 {
                            v___x_2278_ = v_v_2266_;
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2276_);
                            crate::leanh::lean_inc(v_key_2275_);
                            crate::leanh::lean_dec(v_v_2266_);
                            v___x_2278_ = crate::leanh::lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2287_ = crate::leanh::lean_ctor_get(v_v_2266_, 0);
                        v_isSharedCheck_2297_ = (!crate::leanh::lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2289_ = v_v_2266_;
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2287_);
                            crate::leanh::lean_dec(v_v_2266_);
                            v___x_2289_ = crate::leanh::lean_box(0);
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2298_, 0, v_x_2253_);
                        crate::leanh::lean_ctor_set(v___x_2298_, 1, v_x_2254_);
                        v___y_2270_ = v___x_2298_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2271_ = lean_array_fset(v_xs_x27_2268_, v_j_2260_, v___y_2270_);
                crate::leanh::lean_dec(v_j_2260_);
                if v_isShared_2265_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2264_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                    v___x_2273_ = v_reuseFailAlloc_2274_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2273_;
            }
            4 => {
                v___x_2280_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_2253_,
                        v_key_2275_,
                    );
                if v___x_2280_ == 0 {
                    crate::leanh::lean_del_object(v___x_2278_);
                    v___x_2281_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2275_,
                        v_val_2276_,
                        v_x_2253_,
                        v_x_2254_,
                    );
                    v___x_2282_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
                    v___y_2270_ = v___x_2282_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2276_);
                    crate::leanh::lean_dec(v_key_2275_);
                    if v_isShared_2279_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2278_, 1, v_x_2254_);
                        crate::leanh::lean_ctor_set(v___x_2278_, 0, v_x_2253_);
                        v___x_2284_ = v___x_2278_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2285_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_x_2253_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_x_2254_);
                        v___x_2284_ = v_reuseFailAlloc_2285_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2270_ = v___x_2284_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2291_ = lean_usize_shift_right(v_x_2251_, v___x_2256_);
                v___x_2292_ = lean_usize_add(v_x_2252_, v___x_2257_);
                v___x_2293_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_node_2287_, v___x_2291_, v___x_2292_, v_x_2253_, v_x_2254_);
                if v_isShared_2290_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2289_, 0, v___x_2293_);
                    v___x_2295_ = v___x_2289_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
                    v___x_2295_ = v_reuseFailAlloc_2296_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2270_ = v___x_2295_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2305_ == 0 {
                    v___x_2307_ = v___x_2304_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2321_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_ks_2301_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_vs_2302_);
                    v___x_2307_ = v_reuseFailAlloc_2321_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2308_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v___x_2307_, v_x_2253_, v_x_2254_);
                v___x_2316_ = 7usize;
                v___x_2317_ = lean_usize_dec_le(v___x_2316_, v_x_2252_);
                if v___x_2317_ == 0 {
                    v___x_2318_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2308_);
                    v___x_2319_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
                    crate::leanh::lean_dec(v___x_2318_);
                    v___y_2310_ = v___x_2320_;
                    state = 10;
                    continue;
                } else {
                    v___y_2310_ = v___x_2317_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2310_ == 0 {
                    v_ks_2311_ = crate::leanh::lean_ctor_get(v_newNode_2308_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2311_);
                    v_vs_2312_ = crate::leanh::lean_ctor_get(v_newNode_2308_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2312_);
                    crate::leanh::lean_dec_ref(v_newNode_2308_);
                    v___x_2313_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2314_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_2252_, v_ks_2311_, v_vs_2312_, v___x_2313_, v___x_2314_);
                    crate::leanh::lean_dec_ref(v_vs_2312_);
                    crate::leanh::lean_dec_ref(v_ks_2311_);
                    return v___x_2315_;
                } else {
                    return v_newNode_2308_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_2323_: usize,
    mut v_keys_2324_: *mut crate::leanh::LeanObject,
    mut v_vals_2325_: *mut crate::leanh::LeanObject,
    mut v_i_2326_: *mut crate::leanh::LeanObject,
    mut v_entries_2327_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v_k_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_h_2333_: usize = 0;
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v_h_2339_: usize = 0;
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2328_ = lean_array_get_size(v_keys_2324_);
                v___x_2329_ = lean_nat_dec_lt(v_i_2326_, v___x_2328_);
                if v___x_2329_ == 0 {
                    crate::leanh::lean_dec(v_i_2326_);
                    return v_entries_2327_;
                } else {
                    v_k_2330_ = lean_array_fget_borrowed(v_keys_2324_, v_i_2326_);
                    v_v_2331_ = lean_array_fget_borrowed(v_vals_2325_, v_i_2326_);
                    v___x_2332_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2330_);
                    v_h_2333_ = lean_uint64_to_usize(v___x_2332_);
                    v___x_2334_ = 5usize;
                    v___x_2335_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2336_ = 1usize;
                    v___x_2337_ = lean_usize_sub(v_depth_2323_, v___x_2336_);
                    v___x_2338_ = lean_usize_mul(v___x_2334_, v___x_2337_);
                    v_h_2339_ = lean_usize_shift_right(v_h_2333_, v___x_2338_);
                    v___x_2340_ = lean_nat_add(v_i_2326_, v___x_2335_);
                    crate::leanh::lean_dec(v_i_2326_);
                    crate::leanh::lean_inc(v_v_2331_);
                    crate::leanh::lean_inc(v_k_2330_);
                    v___x_2341_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_entries_2327_, v_h_2339_, v_depth_2323_, v_k_2330_, v_v_2331_);
                    v_i_2326_ = v___x_2340_;
                    v_entries_2327_ = v___x_2341_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_2343_: *mut crate::leanh::LeanObject,
    mut v_keys_2344_: *mut crate::leanh::LeanObject,
    mut v_vals_2345_: *mut crate::leanh::LeanObject,
    mut v_i_2346_: *mut crate::leanh::LeanObject,
    mut v_entries_2347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2348_: usize = 0;
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2348_ = crate::leanh::lean_unbox_usize(v_depth_2343_);
    crate::leanh::lean_dec(v_depth_2343_);
    v_res_2349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2348_, v_keys_2344_, v_vals_2345_, v_i_2346_, v_entries_2347_);
    crate::leanh::lean_dec_ref(v_vals_2345_);
    crate::leanh::lean_dec_ref(v_keys_2344_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_2350_: *mut crate::leanh::LeanObject,
    mut v_x_2351_: *mut crate::leanh::LeanObject,
    mut v_x_2352_: *mut crate::leanh::LeanObject,
    mut v_x_2353_: *mut crate::leanh::LeanObject,
    mut v_x_2354_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2086__boxed_2355_: usize = 0;
    let mut v_x_2087__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2086__boxed_2355_ = crate::leanh::lean_unbox_usize(v_x_2351_);
    crate::leanh::lean_dec(v_x_2351_);
    v_x_2087__boxed_2356_ = crate::leanh::lean_unbox_usize(v_x_2352_);
    crate::leanh::lean_dec(v_x_2352_);
    v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2350_, v_x_2086__boxed_2355_, v_x_2087__boxed_2356_, v_x_2353_, v_x_2354_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(
    mut v_x_2358_: *mut crate::leanh::LeanObject,
    mut v_x_2359_: *mut crate::leanh::LeanObject,
    mut v_x_2360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2361_: u64 = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2361_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2359_);
    v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
    v___x_2363_ = 1usize;
    v___x_2364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2358_, v___x_2362_, v___x_2363_, v_x_2359_, v_x_2360_);
    return v___x_2364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(
    mut v_type_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v_s_2367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2368_ = crate::leanh::lean_ctor_get(v_s_2367_, 0);
                v_rings_2369_ = crate::leanh::lean_ctor_get(v_s_2367_, 1);
                v_semirings_2370_ = crate::leanh::lean_ctor_get(v_s_2367_, 2);
                v_ncRings_2371_ = crate::leanh::lean_ctor_get(v_s_2367_, 3);
                v_ncSemirings_2372_ = crate::leanh::lean_ctor_get(v_s_2367_, 4);
                v_typeClassify_2373_ = crate::leanh::lean_ctor_get(v_s_2367_, 5);
                v_isSharedCheck_2381_ = (!crate::leanh::lean_is_exclusive(v_s_2367_)) as u8;
                if v_isSharedCheck_2381_ == 0 {
                    v___x_2375_ = v_s_2367_;
                    v_isShared_2376_ = v_isSharedCheck_2381_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_2373_);
                    crate::leanh::lean_inc(v_ncSemirings_2372_);
                    crate::leanh::lean_inc(v_ncRings_2371_);
                    crate::leanh::lean_inc(v_semirings_2370_);
                    crate::leanh::lean_inc(v_rings_2369_);
                    crate::leanh::lean_inc(v_exp_2368_);
                    crate::leanh::lean_dec(v_s_2367_);
                    v___x_2375_ = crate::leanh::lean_box(0);
                    v_isShared_2376_ = v_isSharedCheck_2381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2377_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2373_, v_type_2365_, v___y_2366_);
                if v_isShared_2376_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2375_, 5, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_exp_2368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_rings_2369_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_semirings_2370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_ncRings_2371_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_ncSemirings_2372_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2380_, 5, v___x_2377_);
                    v___x_2379_ = v_reuseFailAlloc_2380_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2382_: *mut crate::leanh::LeanObject,
    mut v_vals_2383_: *mut crate::leanh::LeanObject,
    mut v_i_2384_: *mut crate::leanh::LeanObject,
    mut v_k_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = lean_array_get_size(v_keys_2382_);
                v___x_2387_ = lean_nat_dec_lt(v_i_2384_, v___x_2386_);
                if v___x_2387_ == 0 {
                    crate::leanh::lean_dec(v_i_2384_);
                    v___x_2388_ = crate::leanh::lean_box(0);
                    return v___x_2388_;
                } else {
                    v_k_x27_2389_ = lean_array_fget_borrowed(v_keys_2382_, v_i_2384_);
                    v___x_2390_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2385_,
                            v_k_x27_2389_,
                        );
                    if v___x_2390_ == 0 {
                        v___x_2391_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2392_ = lean_nat_add(v_i_2384_, v___x_2391_);
                        crate::leanh::lean_dec(v_i_2384_);
                        v_i_2384_ = v___x_2392_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2394_ = lean_array_fget_borrowed(v_vals_2383_, v_i_2384_);
                        crate::leanh::lean_dec(v_i_2384_);
                        crate::leanh::lean_inc(v___x_2394_);
                        v___x_2395_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2395_, 0, v___x_2394_);
                        return v___x_2395_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2396_: *mut crate::leanh::LeanObject,
    mut v_vals_2397_: *mut crate::leanh::LeanObject,
    mut v_i_2398_: *mut crate::leanh::LeanObject,
    mut v_k_2399_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2400_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2396_, v_vals_2397_, v_i_2398_, v_k_2399_);
    crate::leanh::lean_dec_ref(v_k_2399_);
    crate::leanh::lean_dec_ref(v_vals_2397_);
    crate::leanh::lean_dec_ref(v_keys_2396_);
    return v_res_2400_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(
    mut v_x_2401_: *mut crate::leanh::LeanObject,
    mut v_x_2402_: usize,
    mut v_x_2403_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: usize = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v_j_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: usize = 0;
    let mut v___x_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2401_) == 0 {
                    v_es_2404_ = crate::leanh::lean_ctor_get(v_x_2401_, 0);
                    v___x_2405_ = crate::leanh::lean_box(2);
                    v___x_2406_ = 5usize;
                    v___x_2407_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2408_ = lean_usize_land(v_x_2402_, v___x_2407_);
                    v_j_2409_ = lean_usize_to_nat(v___x_2408_);
                    v___x_2410_ = lean_array_get_borrowed(v___x_2405_, v_es_2404_, v_j_2409_);
                    crate::leanh::lean_dec(v_j_2409_);
                    match crate::leanh::lean_obj_tag(v___x_2410_) {
                        0 => {
                            v_key_2411_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                            v_val_2412_ = crate::leanh::lean_ctor_get(v___x_2410_, 1);
                            v___x_2413_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2403_, v_key_2411_);
                            if v___x_2413_ == 0 {
                                v___x_2414_ = crate::leanh::lean_box(0);
                                return v___x_2414_;
                            } else {
                                crate::leanh::lean_inc(v_val_2412_);
                                v___x_2415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2415_, 0, v_val_2412_);
                                return v___x_2415_;
                            }
                        }
                        1 => {
                            v_node_2416_ = crate::leanh::lean_ctor_get(v___x_2410_, 0);
                            v___x_2417_ = lean_usize_shift_right(v_x_2402_, v___x_2406_);
                            v_x_2401_ = v_node_2416_;
                            v_x_2402_ = v___x_2417_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2419_ = crate::leanh::lean_box(0);
                            return v___x_2419_;
                        }
                    }
                } else {
                    v_ks_2420_ = crate::leanh::lean_ctor_get(v_x_2401_, 0);
                    v_vs_2421_ = crate::leanh::lean_ctor_get(v_x_2401_, 1);
                    v___x_2422_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2423_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2420_, v_vs_2421_, v___x_2422_, v_x_2403_);
                    return v___x_2423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2424_: *mut crate::leanh::LeanObject,
    mut v_x_2425_: *mut crate::leanh::LeanObject,
    mut v_x_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2304__boxed_2427_: usize = 0;
    let mut v_res_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2304__boxed_2427_ = crate::leanh::lean_unbox_usize(v_x_2425_);
    crate::leanh::lean_dec(v_x_2425_);
    v_res_2428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2424_, v_x_2304__boxed_2427_, v_x_2426_);
    crate::leanh::lean_dec_ref(v_x_2426_);
    crate::leanh::lean_dec_ref(v_x_2424_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(
    mut v_x_2429_: *mut crate::leanh::LeanObject,
    mut v_x_2430_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2431_: u64 = 0;
    let mut v___x_2432_: usize = 0;
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2430_);
    v___x_2432_ = lean_uint64_to_usize(v___x_2431_);
    v___x_2433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2429_, v___x_2432_, v_x_2430_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(
    mut v_x_2434_: *mut crate::leanh::LeanObject,
    mut v_x_2435_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_2434_, v_x_2435_);
    crate::leanh::lean_dec_ref(v_x_2435_);
    crate::leanh::lean_dec_ref(v_x_2434_);
    return v_res_2436_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(
    mut v_type_2437_: *mut crate::leanh::LeanObject,
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v_typeClassify_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v_id_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2472_: u8 = 0;
    let mut v___y_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_unused_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2499_: u8 = 0;
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_a_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2504_: u8 = 0;
    let mut v___x_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2439_, v_a_2442_);
                if crate::leanh::lean_obj_tag(v___x_2445_) == 0 {
                    v_a_2446_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2500_ = (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2500_ == 0 {
                        v___x_2448_ = v___x_2445_;
                        v_isShared_2449_ = v_isSharedCheck_2500_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2446_);
                        crate::leanh::lean_dec(v___x_2445_);
                        v___x_2448_ = crate::leanh::lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2500_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2437_);
                    v_a_2501_ = crate::leanh::lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2508_ = (!crate::leanh::lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2503_ = v___x_2445_;
                        v_isShared_2504_ = v_isSharedCheck_2508_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2501_);
                        crate::leanh::lean_dec(v___x_2445_);
                        v___x_2503_ = crate::leanh::lean_box(0);
                        v_isShared_2504_ = v_isSharedCheck_2508_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_typeClassify_2450_ = crate::leanh::lean_ctor_get(v_a_2446_, 5);
                crate::leanh::lean_inc_ref(v_typeClassify_2450_);
                crate::leanh::lean_dec(v_a_2446_);
                v___x_2451_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2450_, v_type_2437_);
                crate::leanh::lean_dec_ref(v_typeClassify_2450_);
                if crate::leanh::lean_obj_tag(v___x_2451_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2437_);
                    v_val_2452_ = crate::leanh::lean_ctor_get(v___x_2451_, 0);
                    v_isSharedCheck_2467_ = (!crate::leanh::lean_is_exclusive(v___x_2451_)) as u8;
                    if v_isSharedCheck_2467_ == 0 {
                        v___x_2454_ = v___x_2451_;
                        v_isShared_2455_ = v_isSharedCheck_2467_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2452_);
                        crate::leanh::lean_dec(v___x_2451_);
                        v___x_2454_ = crate::leanh::lean_box(0);
                        v_isShared_2455_ = v_isSharedCheck_2467_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2451_);
                    crate::leanh::lean_del_object(v___x_2448_);
                    crate::leanh::lean_inc_ref(v_type_2437_);
                    v___x_2468_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
                    if crate::leanh::lean_obj_tag(v___x_2468_) == 0 {
                        v_a_2469_ = crate::leanh::lean_ctor_get(v___x_2468_, 0);
                        v_isSharedCheck_2499_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2468_)) as u8;
                        if v_isSharedCheck_2499_ == 0 {
                            v___x_2471_ = v___x_2468_;
                            v_isShared_2472_ = v_isSharedCheck_2499_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2469_);
                            crate::leanh::lean_dec(v___x_2468_);
                            v___x_2471_ = crate::leanh::lean_box(0);
                            v_isShared_2472_ = v_isSharedCheck_2499_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_2437_);
                        return v___x_2468_;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_val_2452_) == 0 {
                    v_id_2456_ = crate::leanh::lean_ctor_get(v_val_2452_, 0);
                    crate::leanh::lean_inc(v_id_2456_);
                    crate::leanh::lean_dec_ref_known(v_val_2452_, 1);
                    if v_isShared_2455_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2454_, 0, v_id_2456_);
                        v___x_2458_ = v___x_2454_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2462_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_id_2456_);
                        v___x_2458_ = v_reuseFailAlloc_2462_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2454_);
                    crate::leanh::lean_dec(v_val_2452_);
                    v___x_2463_ = crate::leanh::lean_box(0);
                    if v_isShared_2449_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2463_);
                        v___x_2465_ = v___x_2448_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
                        v___x_2465_ = v_reuseFailAlloc_2466_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2448_, 0, v___x_2458_);
                    v___x_2460_ = v___x_2448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
                    v___x_2460_ = v_reuseFailAlloc_2461_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2460_;
            }
            5 => {
                return v___x_2465_;
            }
            6 => {
                if crate::leanh::lean_obj_tag(v_a_2469_) == 0 {
                    crate::leanh::lean_del_object(v___x_2471_);
                    v___x_2494_ = crate::leanh::lean_box(4);
                    v___y_2474_ = v___x_2494_;
                    state = 7;
                    continue;
                } else {
                    v_val_2495_ = crate::leanh::lean_ctor_get(v_a_2469_, 0);
                    crate::leanh::lean_inc(v_val_2495_);
                    if v_isShared_2472_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2471_, 0, v_val_2495_);
                        v___x_2497_ = v___x_2471_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2498_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_val_2495_);
                        v___x_2497_ = v_reuseFailAlloc_2498_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                v___f_2475_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0 as *mut core::ffi::c_void, 3, 2);
                crate::leanh::lean_closure_set(v___f_2475_, 0, v_type_2437_);
                crate::leanh::lean_closure_set(v___f_2475_, 1, v___y_2474_);
                v___x_2476_ = l_Lean_Meta_Sym_Arith_arithExt;
                v___x_2477_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2476_, v___f_2475_, v_a_2439_);
                if crate::leanh::lean_obj_tag(v___x_2477_) == 0 {
                    v_isSharedCheck_2484_ = (!crate::leanh::lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2484_ == 0 {
                        v_unused_2485_ = crate::leanh::lean_ctor_get(v___x_2477_, 0);
                        crate::leanh::lean_dec(v_unused_2485_);
                        v___x_2479_ = v___x_2477_;
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2477_);
                        v___x_2479_ = crate::leanh::lean_box(0);
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2469_);
                    v_a_2486_ = crate::leanh::lean_ctor_get(v___x_2477_, 0);
                    v_isSharedCheck_2493_ = (!crate::leanh::lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2488_ = v___x_2477_;
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2486_);
                        crate::leanh::lean_dec(v___x_2477_);
                        v___x_2488_ = crate::leanh::lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2480_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2479_, 0, v_a_2469_);
                    v___x_2482_ = v___x_2479_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2469_);
                    v___x_2482_ = v_reuseFailAlloc_2483_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2482_;
            }
            10 => {
                if v_isShared_2489_ == 0 {
                    v___x_2491_ = v___x_2488_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
                    v___x_2491_ = v_reuseFailAlloc_2492_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2491_;
            }
            12 => {
                v___y_2474_ = v___x_2497_;
                state = 7;
                continue;
            }
            13 => {
                if v_isShared_2504_ == 0 {
                    v___x_2506_ = v___x_2503_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
                    v___x_2506_ = v_reuseFailAlloc_2507_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2506_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___boxed(
    mut v_type_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
    mut v_a_2514_: *mut crate::leanh::LeanObject,
    mut v_a_2515_: *mut crate::leanh::LeanObject,
    mut v_a_2516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2517_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(
            v_type_2509_,
            v_a_2510_,
            v_a_2511_,
            v_a_2512_,
            v_a_2513_,
            v_a_2514_,
            v_a_2515_,
        );
    crate::leanh::lean_dec(v_a_2515_);
    crate::leanh::lean_dec_ref(v_a_2514_);
    crate::leanh::lean_dec(v_a_2513_);
    crate::leanh::lean_dec_ref(v_a_2512_);
    crate::leanh::lean_dec(v_a_2511_);
    crate::leanh::lean_dec_ref(v_a_2510_);
    return v_res_2517_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(
    mut v_00_u03b2_2518_: *mut crate::leanh::LeanObject,
    mut v_x_2519_: *mut crate::leanh::LeanObject,
    mut v_x_2520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_2519_, v_x_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(
    mut v_00_u03b2_2522_: *mut crate::leanh::LeanObject,
    mut v_x_2523_: *mut crate::leanh::LeanObject,
    mut v_x_2524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_2522_, v_x_2523_, v_x_2524_);
    crate::leanh::lean_dec_ref(v_x_2524_);
    crate::leanh::lean_dec_ref(v_x_2523_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(
    mut v_00_u03b2_2526_: *mut crate::leanh::LeanObject,
    mut v_x_2527_: *mut crate::leanh::LeanObject,
    mut v_x_2528_: *mut crate::leanh::LeanObject,
    mut v_x_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_2527_, v_x_2528_, v_x_2529_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(
    mut v_00_u03b2_2531_: *mut crate::leanh::LeanObject,
    mut v_x_2532_: *mut crate::leanh::LeanObject,
    mut v_x_2533_: usize,
    mut v_x_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2532_, v_x_2533_, v_x_2534_);
    return v___x_2535_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2536_: *mut crate::leanh::LeanObject,
    mut v_x_2537_: *mut crate::leanh::LeanObject,
    mut v_x_2538_: *mut crate::leanh::LeanObject,
    mut v_x_2539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2512__boxed_2540_: usize = 0;
    let mut v_res_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2512__boxed_2540_ = crate::leanh::lean_unbox_usize(v_x_2538_);
    crate::leanh::lean_dec(v_x_2538_);
    v_res_2541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_2536_, v_x_2537_, v_x_2512__boxed_2540_, v_x_2539_);
    crate::leanh::lean_dec_ref(v_x_2539_);
    crate::leanh::lean_dec_ref(v_x_2537_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(
    mut v_00_u03b2_2542_: *mut crate::leanh::LeanObject,
    mut v_x_2543_: *mut crate::leanh::LeanObject,
    mut v_x_2544_: usize,
    mut v_x_2545_: usize,
    mut v_x_2546_: *mut crate::leanh::LeanObject,
    mut v_x_2547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2543_, v_x_2544_, v_x_2545_, v_x_2546_, v_x_2547_);
    return v___x_2548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2549_: *mut crate::leanh::LeanObject,
    mut v_x_2550_: *mut crate::leanh::LeanObject,
    mut v_x_2551_: *mut crate::leanh::LeanObject,
    mut v_x_2552_: *mut crate::leanh::LeanObject,
    mut v_x_2553_: *mut crate::leanh::LeanObject,
    mut v_x_2554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2523__boxed_2555_: usize = 0;
    let mut v_x_2524__boxed_2556_: usize = 0;
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2523__boxed_2555_ = crate::leanh::lean_unbox_usize(v_x_2551_);
    crate::leanh::lean_dec(v_x_2551_);
    v_x_2524__boxed_2556_ = crate::leanh::lean_unbox_usize(v_x_2552_);
    crate::leanh::lean_dec(v_x_2552_);
    v_res_2557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_2549_, v_x_2550_, v_x_2523__boxed_2555_, v_x_2524__boxed_2556_, v_x_2553_, v_x_2554_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2558_: *mut crate::leanh::LeanObject,
    mut v_keys_2559_: *mut crate::leanh::LeanObject,
    mut v_vals_2560_: *mut crate::leanh::LeanObject,
    mut v_heq_2561_: *mut crate::leanh::LeanObject,
    mut v_i_2562_: *mut crate::leanh::LeanObject,
    mut v_k_2563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2559_, v_vals_2560_, v_i_2562_, v_k_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2565_: *mut crate::leanh::LeanObject,
    mut v_keys_2566_: *mut crate::leanh::LeanObject,
    mut v_vals_2567_: *mut crate::leanh::LeanObject,
    mut v_heq_2568_: *mut crate::leanh::LeanObject,
    mut v_i_2569_: *mut crate::leanh::LeanObject,
    mut v_k_2570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2565_, v_keys_2566_, v_vals_2567_, v_heq_2568_, v_i_2569_, v_k_2570_);
    crate::leanh::lean_dec_ref(v_k_2570_);
    crate::leanh::lean_dec_ref(v_vals_2567_);
    crate::leanh::lean_dec_ref(v_keys_2566_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2572_: *mut crate::leanh::LeanObject,
    mut v_n_2573_: *mut crate::leanh::LeanObject,
    mut v_k_2574_: *mut crate::leanh::LeanObject,
    mut v_v_2575_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_2573_, v_k_2574_, v_v_2575_);
    return v___x_2576_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2577_: *mut crate::leanh::LeanObject,
    mut v_depth_2578_: usize,
    mut v_keys_2579_: *mut crate::leanh::LeanObject,
    mut v_vals_2580_: *mut crate::leanh::LeanObject,
    mut v_heq_2581_: *mut crate::leanh::LeanObject,
    mut v_i_2582_: *mut crate::leanh::LeanObject,
    mut v_entries_2583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2578_, v_keys_2579_, v_vals_2580_, v_i_2582_, v_entries_2583_);
    return v___x_2584_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2585_: *mut crate::leanh::LeanObject,
    mut v_depth_2586_: *mut crate::leanh::LeanObject,
    mut v_keys_2587_: *mut crate::leanh::LeanObject,
    mut v_vals_2588_: *mut crate::leanh::LeanObject,
    mut v_heq_2589_: *mut crate::leanh::LeanObject,
    mut v_i_2590_: *mut crate::leanh::LeanObject,
    mut v_entries_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2592_: usize = 0;
    let mut v_res_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2592_ = crate::leanh::lean_unbox_usize(v_depth_2586_);
    crate::leanh::lean_dec(v_depth_2586_);
    v_res_2593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2585_, v_depth_boxed_2592_, v_keys_2587_, v_vals_2588_, v_heq_2589_, v_i_2590_, v_entries_2591_);
    crate::leanh::lean_dec_ref(v_vals_2588_);
    crate::leanh::lean_dec_ref(v_keys_2587_);
    return v_res_2593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2594_: *mut crate::leanh::LeanObject,
    mut v_x_2595_: *mut crate::leanh::LeanObject,
    mut v_x_2596_: *mut crate::leanh::LeanObject,
    mut v_x_2597_: *mut crate::leanh::LeanObject,
    mut v_x_2598_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2599_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2595_, v_x_2596_, v_x_2597_, v_x_2598_);
    return v___x_2599_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(
    mut v___x_2600_: *mut crate::leanh::LeanObject,
    mut v_s_2601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2602_ = crate::leanh::lean_ctor_get(v_s_2601_, 0);
                v_rings_2603_ = crate::leanh::lean_ctor_get(v_s_2601_, 1);
                v_semirings_2604_ = crate::leanh::lean_ctor_get(v_s_2601_, 2);
                v_ncRings_2605_ = crate::leanh::lean_ctor_get(v_s_2601_, 3);
                v_ncSemirings_2606_ = crate::leanh::lean_ctor_get(v_s_2601_, 4);
                v_typeClassify_2607_ = crate::leanh::lean_ctor_get(v_s_2601_, 5);
                v_isSharedCheck_2615_ = (!crate::leanh::lean_is_exclusive(v_s_2601_)) as u8;
                if v_isSharedCheck_2615_ == 0 {
                    v___x_2609_ = v_s_2601_;
                    v_isShared_2610_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_2607_);
                    crate::leanh::lean_inc(v_ncSemirings_2606_);
                    crate::leanh::lean_inc(v_ncRings_2605_);
                    crate::leanh::lean_inc(v_semirings_2604_);
                    crate::leanh::lean_inc(v_rings_2603_);
                    crate::leanh::lean_inc(v_exp_2602_);
                    crate::leanh::lean_dec(v_s_2601_);
                    v___x_2609_ = crate::leanh::lean_box(0);
                    v_isShared_2610_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2611_ = lean_array_push(v_semirings_2604_, v___x_2600_);
                if v_isShared_2610_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2609_, 2, v___x_2611_);
                    v___x_2613_ = v___x_2609_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_exp_2602_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_rings_2603_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 2, v___x_2611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_ncRings_2605_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 4, v_ncSemirings_2606_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2614_, 5, v_typeClassify_2607_);
                    v___x_2613_ = v_reuseFailAlloc_2614_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2613_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(
    mut v_val_2616_: *mut crate::leanh::LeanObject,
    mut v___x_2617_: *mut crate::leanh::LeanObject,
    mut v_s_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v_v_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toRing_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_unused_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_unused_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2619_ = crate::leanh::lean_ctor_get(v_s_2618_, 0);
                v_rings_2620_ = crate::leanh::lean_ctor_get(v_s_2618_, 1);
                v_semirings_2621_ = crate::leanh::lean_ctor_get(v_s_2618_, 2);
                v_ncRings_2622_ = crate::leanh::lean_ctor_get(v_s_2618_, 3);
                v_ncSemirings_2623_ = crate::leanh::lean_ctor_get(v_s_2618_, 4);
                v_typeClassify_2624_ = crate::leanh::lean_ctor_get(v_s_2618_, 5);
                v___x_2625_ = lean_array_get_size(v_rings_2620_);
                v___x_2626_ = lean_nat_dec_lt(v_val_2616_, v___x_2625_);
                if v___x_2626_ == 0 {
                    crate::leanh::lean_dec(v___x_2617_);
                    return v_s_2618_;
                } else {
                    crate::leanh::lean_inc_ref(v_typeClassify_2624_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_2623_);
                    crate::leanh::lean_inc_ref(v_ncRings_2622_);
                    crate::leanh::lean_inc_ref(v_semirings_2621_);
                    crate::leanh::lean_inc_ref(v_rings_2620_);
                    crate::leanh::lean_inc(v_exp_2619_);
                    v_isSharedCheck_2652_ = (!crate::leanh::lean_is_exclusive(v_s_2618_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v_unused_2653_ = crate::leanh::lean_ctor_get(v_s_2618_, 5);
                        crate::leanh::lean_dec(v_unused_2653_);
                        v_unused_2654_ = crate::leanh::lean_ctor_get(v_s_2618_, 4);
                        crate::leanh::lean_dec(v_unused_2654_);
                        v_unused_2655_ = crate::leanh::lean_ctor_get(v_s_2618_, 3);
                        crate::leanh::lean_dec(v_unused_2655_);
                        v_unused_2656_ = crate::leanh::lean_ctor_get(v_s_2618_, 2);
                        crate::leanh::lean_dec(v_unused_2656_);
                        v_unused_2657_ = crate::leanh::lean_ctor_get(v_s_2618_, 1);
                        crate::leanh::lean_dec(v_unused_2657_);
                        v_unused_2658_ = crate::leanh::lean_ctor_get(v_s_2618_, 0);
                        crate::leanh::lean_dec(v_unused_2658_);
                        v___x_2628_ = v_s_2618_;
                        v_isShared_2629_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_2618_);
                        v___x_2628_ = crate::leanh::lean_box(0);
                        v_isShared_2629_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2630_ = lean_array_fget(v_rings_2620_, v_val_2616_);
                v_toRing_2631_ = crate::leanh::lean_ctor_get(v_v_2630_, 0);
                v_invFn_x3f_2632_ = crate::leanh::lean_ctor_get(v_v_2630_, 1);
                v_commSemiringInst_2633_ = crate::leanh::lean_ctor_get(v_v_2630_, 3);
                v_commRingInst_2634_ = crate::leanh::lean_ctor_get(v_v_2630_, 4);
                v_noZeroDivInst_x3f_2635_ = crate::leanh::lean_ctor_get(v_v_2630_, 5);
                v_fieldInst_x3f_2636_ = crate::leanh::lean_ctor_get(v_v_2630_, 6);
                v_isSharedCheck_2650_ = (!crate::leanh::lean_is_exclusive(v_v_2630_)) as u8;
                if v_isSharedCheck_2650_ == 0 {
                    v_unused_2651_ = crate::leanh::lean_ctor_get(v_v_2630_, 2);
                    crate::leanh::lean_dec(v_unused_2651_);
                    v___x_2638_ = v_v_2630_;
                    v_isShared_2639_ = v_isSharedCheck_2650_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fieldInst_x3f_2636_);
                    crate::leanh::lean_inc(v_noZeroDivInst_x3f_2635_);
                    crate::leanh::lean_inc(v_commRingInst_2634_);
                    crate::leanh::lean_inc(v_commSemiringInst_2633_);
                    crate::leanh::lean_inc(v_invFn_x3f_2632_);
                    crate::leanh::lean_inc(v_toRing_2631_);
                    crate::leanh::lean_dec(v_v_2630_);
                    v___x_2638_ = crate::leanh::lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = crate::leanh::lean_box(0);
                v_xs_x27_2641_ = lean_array_fset(v_rings_2620_, v_val_2616_, v___x_2640_);
                v___x_2642_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2617_);
                if v_isShared_2639_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2638_, 2, v___x_2642_);
                    v___x_2644_ = v___x_2638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = crate::leanh::lean_alloc_ctor(0, 7, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_toRing_2631_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_invFn_x3f_2632_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 2, v___x_2642_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2649_,
                        3,
                        v_commSemiringInst_2633_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_commRingInst_2634_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2649_,
                        5,
                        v_noZeroDivInst_x3f_2635_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2649_, 6, v_fieldInst_x3f_2636_);
                    v___x_2644_ = v_reuseFailAlloc_2649_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2645_ = lean_array_fset(v_xs_x27_2641_, v_val_2616_, v___x_2644_);
                if v_isShared_2629_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2628_, 1, v___x_2645_);
                    v___x_2647_ = v___x_2628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2648_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_exp_2619_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_semirings_2621_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_ncRings_2622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_ncSemirings_2623_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2648_, 5, v_typeClassify_2624_);
                    v___x_2647_ = v_reuseFailAlloc_2648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed(
    mut v_val_2659_: *mut crate::leanh::LeanObject,
    mut v___x_2660_: *mut crate::leanh::LeanObject,
    mut v_s_2661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2662_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(v_val_2659_, v___x_2660_, v_s_2661_);
    crate::leanh::lean_dec(v_val_2659_);
    return v_res_2662_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2682_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6;
    v___x_2683_ = l_Lean_stringToMessageData(v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(
    mut v_type_2684_: *mut crate::leanh::LeanObject,
    mut v_a_2685_: *mut crate::leanh::LeanObject,
    mut v_a_2686_: *mut crate::leanh::LeanObject,
    mut v_a_2687_: *mut crate::leanh::LeanObject,
    mut v_a_2688_: *mut crate::leanh::LeanObject,
    mut v_a_2689_: *mut crate::leanh::LeanObject,
    mut v_a_2690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v_val_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v___x_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_unused_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2754_: u8 = 0;
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2770_: u8 = 0;
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: u8 = 0;
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2782_: u8 = 0;
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2786_: u8 = 0;
    let mut v_a_2787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut v_a_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2802_: u8 = 0;
    let mut v_a_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut v_a_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2819_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_a_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2684_);
                v___x_2695_ = l_Lean_Meta_getDecLevel(
                    v_type_2684_,
                    v_a_2687_,
                    v_a_2688_,
                    v_a_2689_,
                    v_a_2690_,
                );
                if crate::leanh::lean_obj_tag(v___x_2695_) == 0 {
                    v_a_2696_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                    crate::leanh::lean_inc_n(v_a_2696_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2695_, 1);
                    v___x_2697_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1;
                    v___x_2698_ = crate::leanh::lean_box(0);
                    v___x_2699_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2699_, 0, v_a_2696_);
                    crate::leanh::lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                    crate::leanh::lean_inc_ref(v___x_2699_);
                    v___x_2700_ = l_Lean_mkConst(v___x_2697_, v___x_2699_);
                    crate::leanh::lean_inc_ref(v_type_2684_);
                    v___x_2701_ = l_Lean_Expr_app___override(v___x_2700_, v_type_2684_);
                    v___x_2702_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2701_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2702_) == 0 {
                        v_a_2703_ = crate::leanh::lean_ctor_get(v___x_2702_, 0);
                        v_isSharedCheck_2815_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2702_)) as u8;
                        if v_isSharedCheck_2815_ == 0 {
                            v___x_2705_ = v___x_2702_;
                            v_isShared_2706_ = v_isSharedCheck_2815_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2703_);
                            crate::leanh::lean_dec(v___x_2702_);
                            v___x_2705_ = crate::leanh::lean_box(0);
                            v_isShared_2706_ = v_isSharedCheck_2815_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_2699_, 2);
                        crate::leanh::lean_dec(v_a_2696_);
                        crate::leanh::lean_dec_ref(v_type_2684_);
                        v_a_2816_ = crate::leanh::lean_ctor_get(v___x_2702_, 0);
                        v_isSharedCheck_2823_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2702_)) as u8;
                        if v_isSharedCheck_2823_ == 0 {
                            v___x_2818_ = v___x_2702_;
                            v_isShared_2819_ = v_isSharedCheck_2823_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2816_);
                            crate::leanh::lean_dec(v___x_2702_);
                            v___x_2818_ = crate::leanh::lean_box(0);
                            v_isShared_2819_ = v_isSharedCheck_2823_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2684_);
                    v_a_2824_ = crate::leanh::lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2831_ = (!crate::leanh::lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v___x_2826_ = v___x_2695_;
                        v_isShared_2827_ = v_isSharedCheck_2831_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2824_);
                        crate::leanh::lean_dec(v___x_2695_);
                        v___x_2826_ = crate::leanh::lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2831_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2693_ = crate::leanh::lean_box(0);
                v___x_2694_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2694_, 0, v___x_2693_);
                return v___x_2694_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2703_) == 1 {
                    crate::leanh::lean_del_object(v___x_2705_);
                    v_val_2707_ = crate::leanh::lean_ctor_get(v_a_2703_, 0);
                    crate::leanh::lean_inc_n(v_val_2707_, 2);
                    crate::leanh::lean_dec_ref_known(v_a_2703_, 1);
                    v___x_2708_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2;
                    crate::leanh::lean_inc_ref(v___x_2699_);
                    v___x_2709_ = l_Lean_mkConst(v___x_2708_, v___x_2699_);
                    crate::leanh::lean_inc_ref_n(v_type_2684_, 2);
                    v___x_2710_ = l_Lean_mkAppB(v___x_2709_, v_type_2684_, v_val_2707_);
                    v___x_2711_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5;
                    v___x_2712_ = l_Lean_mkConst(v___x_2711_, v___x_2699_);
                    crate::leanh::lean_inc_ref(v___x_2710_);
                    v___x_2713_ = l_Lean_mkAppB(v___x_2712_, v_type_2684_, v___x_2710_);
                    v___x_2714_ = l_Lean_Meta_Sym_canon(
                        v___x_2713_,
                        v_a_2685_,
                        v_a_2686_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2714_) == 0 {
                        v_a_2715_ = crate::leanh::lean_ctor_get(v___x_2714_, 0);
                        crate::leanh::lean_inc(v_a_2715_);
                        crate::leanh::lean_dec_ref_known(v___x_2714_, 1);
                        v___x_2716_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2715_, v_a_2686_);
                        if crate::leanh::lean_obj_tag(v___x_2716_) == 0 {
                            v_a_2717_ = crate::leanh::lean_ctor_get(v___x_2716_, 0);
                            crate::leanh::lean_inc_n(v_a_2717_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_2716_, 1);
                            v___x_2718_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_2717_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
                            if crate::leanh::lean_obj_tag(v___x_2718_) == 0 {
                                v_a_2719_ = crate::leanh::lean_ctor_get(v___x_2718_, 0);
                                crate::leanh::lean_inc(v_a_2719_);
                                crate::leanh::lean_dec_ref_known(v___x_2718_, 1);
                                if crate::leanh::lean_obj_tag(v_a_2719_) == 1 {
                                    crate::leanh::lean_dec(v_a_2717_);
                                    v_val_2720_ = crate::leanh::lean_ctor_get(v_a_2719_, 0);
                                    v_isSharedCheck_2771_ =
                                        (!crate::leanh::lean_is_exclusive(v_a_2719_)) as u8;
                                    if v_isSharedCheck_2771_ == 0 {
                                        v___x_2722_ = v_a_2719_;
                                        v_isShared_2723_ = v_isSharedCheck_2771_;
                                        state = 3;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_val_2720_);
                                        crate::leanh::lean_dec(v_a_2719_);
                                        v___x_2722_ = crate::leanh::lean_box(0);
                                        v_isShared_2723_ = v_isSharedCheck_2771_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_2719_);
                                    crate::leanh::lean_dec_ref(v___x_2710_);
                                    crate::leanh::lean_dec(v_val_2707_);
                                    crate::leanh::lean_dec(v_a_2696_);
                                    crate::leanh::lean_dec_ref(v_type_2684_);
                                    v___x_2772_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2685_);
                                    if crate::leanh::lean_obj_tag(v___x_2772_) == 0 {
                                        v_a_2773_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                                        crate::leanh::lean_inc(v_a_2773_);
                                        crate::leanh::lean_dec_ref_known(v___x_2772_, 1);
                                        v___x_2774_ = (crate::leanh::lean_unbox(v_a_2773_) as u8);
                                        crate::leanh::lean_dec(v_a_2773_);
                                        if v___x_2774_ == 0 {
                                            crate::leanh::lean_dec(v_a_2717_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_2775_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7);
                                            v___x_2776_ = l_Lean_indentExpr(v_a_2717_);
                                            v___x_2777_ =
                                                crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2777_,
                                                0,
                                                v___x_2775_,
                                            );
                                            crate::leanh::lean_ctor_set(
                                                v___x_2777_,
                                                1,
                                                v___x_2776_,
                                            );
                                            v___x_2778_ = l_Lean_Meta_Sym_reportIssue(
                                                v___x_2777_,
                                                v_a_2685_,
                                                v_a_2686_,
                                                v_a_2687_,
                                                v_a_2688_,
                                                v_a_2689_,
                                                v_a_2690_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_2778_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_2778_, 1);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_a_2779_ =
                                                    crate::leanh::lean_ctor_get(v___x_2778_, 0);
                                                v_isSharedCheck_2786_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_2778_))
                                                        as u8;
                                                if v_isSharedCheck_2786_ == 0 {
                                                    v___x_2781_ = v___x_2778_;
                                                    v_isShared_2782_ = v_isSharedCheck_2786_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_2779_);
                                                    crate::leanh::lean_dec(v___x_2778_);
                                                    v___x_2781_ = crate::leanh::lean_box(0);
                                                    v_isShared_2782_ = v_isSharedCheck_2786_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_2717_);
                                        v_a_2787_ = crate::leanh::lean_ctor_get(v___x_2772_, 0);
                                        v_isSharedCheck_2794_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2772_)) as u8;
                                        if v_isSharedCheck_2794_ == 0 {
                                            v___x_2789_ = v___x_2772_;
                                            v_isShared_2790_ = v_isSharedCheck_2794_;
                                            state = 15;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2787_);
                                            crate::leanh::lean_dec(v___x_2772_);
                                            v___x_2789_ = crate::leanh::lean_box(0);
                                            v_isShared_2790_ = v_isSharedCheck_2794_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2717_);
                                crate::leanh::lean_dec_ref(v___x_2710_);
                                crate::leanh::lean_dec(v_val_2707_);
                                crate::leanh::lean_dec(v_a_2696_);
                                crate::leanh::lean_dec_ref(v_type_2684_);
                                return v___x_2718_;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2710_);
                            crate::leanh::lean_dec(v_val_2707_);
                            crate::leanh::lean_dec(v_a_2696_);
                            crate::leanh::lean_dec_ref(v_type_2684_);
                            v_a_2795_ = crate::leanh::lean_ctor_get(v___x_2716_, 0);
                            v_isSharedCheck_2802_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2716_)) as u8;
                            if v_isSharedCheck_2802_ == 0 {
                                v___x_2797_ = v___x_2716_;
                                v_isShared_2798_ = v_isSharedCheck_2802_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2795_);
                                crate::leanh::lean_dec(v___x_2716_);
                                v___x_2797_ = crate::leanh::lean_box(0);
                                v_isShared_2798_ = v_isSharedCheck_2802_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_2710_);
                        crate::leanh::lean_dec(v_val_2707_);
                        crate::leanh::lean_dec(v_a_2696_);
                        crate::leanh::lean_dec_ref(v_type_2684_);
                        v_a_2803_ = crate::leanh::lean_ctor_get(v___x_2714_, 0);
                        v_isSharedCheck_2810_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2714_)) as u8;
                        if v_isSharedCheck_2810_ == 0 {
                            v___x_2805_ = v___x_2714_;
                            v_isShared_2806_ = v_isSharedCheck_2810_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2803_);
                            crate::leanh::lean_dec(v___x_2714_);
                            v___x_2805_ = crate::leanh::lean_box(0);
                            v_isShared_2806_ = v_isSharedCheck_2810_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2703_);
                    crate::leanh::lean_dec_ref_known(v___x_2699_, 2);
                    crate::leanh::lean_dec(v_a_2696_);
                    crate::leanh::lean_dec_ref(v_type_2684_);
                    v___x_2811_ = crate::leanh::lean_box(0);
                    if v_isShared_2706_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2705_, 0, v___x_2811_);
                        v___x_2813_ = v___x_2705_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2814_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
                        v___x_2813_ = v_reuseFailAlloc_2814_;
                        state = 21;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2724_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2686_, v_a_2689_);
                if crate::leanh::lean_obj_tag(v___x_2724_) == 0 {
                    v_a_2725_ = crate::leanh::lean_ctor_get(v___x_2724_, 0);
                    crate::leanh::lean_inc(v_a_2725_);
                    crate::leanh::lean_dec_ref_known(v___x_2724_, 1);
                    v_semirings_2726_ = crate::leanh::lean_ctor_get(v_a_2725_, 2);
                    crate::leanh::lean_inc_ref(v_semirings_2726_);
                    crate::leanh::lean_dec(v_a_2725_);
                    v___x_2727_ = lean_array_get_size(v_semirings_2726_);
                    crate::leanh::lean_dec_ref(v_semirings_2726_);
                    v___x_2728_ = crate::leanh::lean_box(0);
                    v___x_2729_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2729_, 0, v___x_2727_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 1, v_type_2684_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 2, v_a_2696_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 3, v___x_2710_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 4, v___x_2728_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 5, v___x_2728_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 6, v___x_2728_);
                    crate::leanh::lean_ctor_set(v___x_2729_, 7, v___x_2728_);
                    crate::leanh::lean_inc(v_val_2720_);
                    v___x_2730_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                    crate::leanh::lean_ctor_set(v___x_2730_, 1, v_val_2720_);
                    crate::leanh::lean_ctor_set(v___x_2730_, 2, v_val_2707_);
                    crate::leanh::lean_ctor_set(v___x_2730_, 3, v___x_2728_);
                    crate::leanh::lean_ctor_set(v___x_2730_, 4, v___x_2728_);
                    v___f_2731_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2731_, 0, v___x_2730_);
                    v___x_2732_ = l_Lean_Meta_Sym_Arith_arithExt;
                    v___x_2733_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2732_, v___f_2731_, v_a_2686_);
                    if crate::leanh::lean_obj_tag(v___x_2733_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2733_, 1);
                        v___f_2734_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_2734_, 0, v_val_2720_);
                        crate::leanh::lean_closure_set(v___f_2734_, 1, v___x_2727_);
                        v___x_2735_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2732_, v___f_2734_, v_a_2686_);
                        if crate::leanh::lean_obj_tag(v___x_2735_) == 0 {
                            v_isSharedCheck_2745_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2735_)) as u8;
                            if v_isSharedCheck_2745_ == 0 {
                                v_unused_2746_ = crate::leanh::lean_ctor_get(v___x_2735_, 0);
                                crate::leanh::lean_dec(v_unused_2746_);
                                v___x_2737_ = v___x_2735_;
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2735_);
                                v___x_2737_ = crate::leanh::lean_box(0);
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2722_);
                            v_a_2747_ = crate::leanh::lean_ctor_get(v___x_2735_, 0);
                            v_isSharedCheck_2754_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2735_)) as u8;
                            if v_isSharedCheck_2754_ == 0 {
                                v___x_2749_ = v___x_2735_;
                                v_isShared_2750_ = v_isSharedCheck_2754_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2747_);
                                crate::leanh::lean_dec(v___x_2735_);
                                v___x_2749_ = crate::leanh::lean_box(0);
                                v_isShared_2750_ = v_isSharedCheck_2754_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2722_);
                        crate::leanh::lean_dec(v_val_2720_);
                        v_a_2755_ = crate::leanh::lean_ctor_get(v___x_2733_, 0);
                        v_isSharedCheck_2762_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2733_)) as u8;
                        if v_isSharedCheck_2762_ == 0 {
                            v___x_2757_ = v___x_2733_;
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2755_);
                            crate::leanh::lean_dec(v___x_2733_);
                            v___x_2757_ = crate::leanh::lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2722_);
                    crate::leanh::lean_dec(v_val_2720_);
                    crate::leanh::lean_dec_ref(v___x_2710_);
                    crate::leanh::lean_dec(v_val_2707_);
                    crate::leanh::lean_dec(v_a_2696_);
                    crate::leanh::lean_dec_ref(v_type_2684_);
                    v_a_2763_ = crate::leanh::lean_ctor_get(v___x_2724_, 0);
                    v_isSharedCheck_2770_ = (!crate::leanh::lean_is_exclusive(v___x_2724_)) as u8;
                    if v_isSharedCheck_2770_ == 0 {
                        v___x_2765_ = v___x_2724_;
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2763_);
                        crate::leanh::lean_dec(v___x_2724_);
                        v___x_2765_ = crate::leanh::lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2723_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2722_, 0, v___x_2727_);
                    v___x_2740_ = v___x_2722_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2727_);
                    v___x_2740_ = v_reuseFailAlloc_2744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2737_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2737_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
                    v___x_2742_ = v_reuseFailAlloc_2743_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2742_;
            }
            7 => {
                if v_isShared_2750_ == 0 {
                    v___x_2752_ = v___x_2749_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2753_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
                    v___x_2752_ = v_reuseFailAlloc_2753_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2752_;
            }
            9 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2760_;
            }
            11 => {
                if v_isShared_2766_ == 0 {
                    v___x_2768_ = v___x_2765_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
                    v___x_2768_ = v_reuseFailAlloc_2769_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2768_;
            }
            13 => {
                if v_isShared_2782_ == 0 {
                    v___x_2784_ = v___x_2781_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2785_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
                    v___x_2784_ = v_reuseFailAlloc_2785_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2784_;
            }
            15 => {
                if v_isShared_2790_ == 0 {
                    v___x_2792_ = v___x_2789_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2793_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
                    v___x_2792_ = v_reuseFailAlloc_2793_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2792_;
            }
            17 => {
                if v_isShared_2798_ == 0 {
                    v___x_2800_ = v___x_2797_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2801_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
                    v___x_2800_ = v_reuseFailAlloc_2801_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_2800_;
            }
            19 => {
                if v_isShared_2806_ == 0 {
                    v___x_2808_ = v___x_2805_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
                    v___x_2808_ = v_reuseFailAlloc_2809_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_2808_;
            }
            21 => {
                return v___x_2813_;
            }
            22 => {
                if v_isShared_2819_ == 0 {
                    v___x_2821_ = v___x_2818_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
                    v___x_2821_ = v_reuseFailAlloc_2822_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2821_;
            }
            24 => {
                if v_isShared_2827_ == 0 {
                    v___x_2829_ = v___x_2826_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_2829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___boxed(
    mut v_type_2832_: *mut crate::leanh::LeanObject,
    mut v_a_2833_: *mut crate::leanh::LeanObject,
    mut v_a_2834_: *mut crate::leanh::LeanObject,
    mut v_a_2835_: *mut crate::leanh::LeanObject,
    mut v_a_2836_: *mut crate::leanh::LeanObject,
    mut v_a_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(
            v_type_2832_,
            v_a_2833_,
            v_a_2834_,
            v_a_2835_,
            v_a_2836_,
            v_a_2837_,
            v_a_2838_,
        );
    crate::leanh::lean_dec(v_a_2838_);
    crate::leanh::lean_dec_ref(v_a_2837_);
    crate::leanh::lean_dec(v_a_2836_);
    crate::leanh::lean_dec_ref(v_a_2835_);
    crate::leanh::lean_dec(v_a_2834_);
    crate::leanh::lean_dec_ref(v_a_2833_);
    return v_res_2840_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(
    mut v___x_2841_: *mut crate::leanh::LeanObject,
    mut v_s_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_2843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2843_ = crate::leanh::lean_ctor_get(v_s_2842_, 0);
                v_rings_2844_ = crate::leanh::lean_ctor_get(v_s_2842_, 1);
                v_semirings_2845_ = crate::leanh::lean_ctor_get(v_s_2842_, 2);
                v_ncRings_2846_ = crate::leanh::lean_ctor_get(v_s_2842_, 3);
                v_ncSemirings_2847_ = crate::leanh::lean_ctor_get(v_s_2842_, 4);
                v_typeClassify_2848_ = crate::leanh::lean_ctor_get(v_s_2842_, 5);
                v_isSharedCheck_2856_ = (!crate::leanh::lean_is_exclusive(v_s_2842_)) as u8;
                if v_isSharedCheck_2856_ == 0 {
                    v___x_2850_ = v_s_2842_;
                    v_isShared_2851_ = v_isSharedCheck_2856_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_2848_);
                    crate::leanh::lean_inc(v_ncSemirings_2847_);
                    crate::leanh::lean_inc(v_ncRings_2846_);
                    crate::leanh::lean_inc(v_semirings_2845_);
                    crate::leanh::lean_inc(v_rings_2844_);
                    crate::leanh::lean_inc(v_exp_2843_);
                    crate::leanh::lean_dec(v_s_2842_);
                    v___x_2850_ = crate::leanh::lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2852_ = lean_array_push(v_ncSemirings_2847_, v___x_2841_);
                if v_isShared_2851_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2850_, 4, v___x_2852_);
                    v___x_2854_ = v___x_2850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_exp_2843_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_rings_2844_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_semirings_2845_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_ncRings_2846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 4, v___x_2852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 5, v_typeClassify_2848_);
                    v___x_2854_ = v_reuseFailAlloc_2855_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2854_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(
    mut v_type_2862_: *mut crate::leanh::LeanObject,
    mut v_a_2863_: *mut crate::leanh::LeanObject,
    mut v_a_2864_: *mut crate::leanh::LeanObject,
    mut v_a_2865_: *mut crate::leanh::LeanObject,
    mut v_a_2866_: *mut crate::leanh::LeanObject,
    mut v_a_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v_val_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_unused_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v___x_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut v_a_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2862_);
                v___x_2869_ = l_Lean_Meta_getDecLevel(
                    v_type_2862_,
                    v_a_2864_,
                    v_a_2865_,
                    v_a_2866_,
                    v_a_2867_,
                );
                if crate::leanh::lean_obj_tag(v___x_2869_) == 0 {
                    v_a_2870_ = crate::leanh::lean_ctor_get(v___x_2869_, 0);
                    crate::leanh::lean_inc_n(v_a_2870_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_2869_, 1);
                    v___x_2871_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1;
                    v___x_2872_ = crate::leanh::lean_box(0);
                    v___x_2873_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2873_, 0, v_a_2870_);
                    crate::leanh::lean_ctor_set(v___x_2873_, 1, v___x_2872_);
                    v___x_2874_ = l_Lean_mkConst(v___x_2871_, v___x_2873_);
                    crate::leanh::lean_inc_ref(v_type_2862_);
                    v___x_2875_ = l_Lean_Expr_app___override(v___x_2874_, v_type_2862_);
                    v___x_2876_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2875_,
                        v_a_2864_,
                        v_a_2865_,
                        v_a_2866_,
                        v_a_2867_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2876_) == 0 {
                        v_a_2877_ = crate::leanh::lean_ctor_get(v___x_2876_, 0);
                        v_isSharedCheck_2926_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2876_)) as u8;
                        if v_isSharedCheck_2926_ == 0 {
                            v___x_2879_ = v___x_2876_;
                            v_isShared_2880_ = v_isSharedCheck_2926_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2877_);
                            crate::leanh::lean_dec(v___x_2876_);
                            v___x_2879_ = crate::leanh::lean_box(0);
                            v_isShared_2880_ = v_isSharedCheck_2926_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2870_);
                        crate::leanh::lean_dec_ref(v_type_2862_);
                        v_a_2927_ = crate::leanh::lean_ctor_get(v___x_2876_, 0);
                        v_isSharedCheck_2934_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2876_)) as u8;
                        if v_isSharedCheck_2934_ == 0 {
                            v___x_2929_ = v___x_2876_;
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2927_);
                            crate::leanh::lean_dec(v___x_2876_);
                            v___x_2929_ = crate::leanh::lean_box(0);
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2862_);
                    v_a_2935_ = crate::leanh::lean_ctor_get(v___x_2869_, 0);
                    v_isSharedCheck_2942_ = (!crate::leanh::lean_is_exclusive(v___x_2869_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v___x_2869_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2935_);
                        crate::leanh::lean_dec(v___x_2869_);
                        v___x_2937_ = crate::leanh::lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2877_) == 1 {
                    crate::leanh::lean_del_object(v___x_2879_);
                    v_val_2881_ = crate::leanh::lean_ctor_get(v_a_2877_, 0);
                    v_isSharedCheck_2921_ = (!crate::leanh::lean_is_exclusive(v_a_2877_)) as u8;
                    if v_isSharedCheck_2921_ == 0 {
                        v___x_2883_ = v_a_2877_;
                        v_isShared_2884_ = v_isSharedCheck_2921_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2881_);
                        crate::leanh::lean_dec(v_a_2877_);
                        v___x_2883_ = crate::leanh::lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2921_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2877_);
                    crate::leanh::lean_dec(v_a_2870_);
                    crate::leanh::lean_dec_ref(v_type_2862_);
                    v___x_2922_ = crate::leanh::lean_box(0);
                    if v_isShared_2880_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2879_, 0, v___x_2922_);
                        v___x_2924_ = v___x_2879_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
                        v___x_2924_ = v_reuseFailAlloc_2925_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2885_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2863_, v_a_2866_);
                if crate::leanh::lean_obj_tag(v___x_2885_) == 0 {
                    v_a_2886_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    crate::leanh::lean_inc(v_a_2886_);
                    crate::leanh::lean_dec_ref_known(v___x_2885_, 1);
                    v_ncSemirings_2887_ = crate::leanh::lean_ctor_get(v_a_2886_, 4);
                    crate::leanh::lean_inc_ref(v_ncSemirings_2887_);
                    crate::leanh::lean_dec(v_a_2886_);
                    v___x_2888_ = lean_array_get_size(v_ncSemirings_2887_);
                    crate::leanh::lean_dec_ref(v_ncSemirings_2887_);
                    v___x_2889_ = crate::leanh::lean_box(0);
                    v___x_2890_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2890_, 0, v___x_2888_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 1, v_type_2862_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 2, v_a_2870_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 3, v_val_2881_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 4, v___x_2889_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 5, v___x_2889_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 6, v___x_2889_);
                    crate::leanh::lean_ctor_set(v___x_2890_, 7, v___x_2889_);
                    v___f_2891_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2891_, 0, v___x_2890_);
                    v___x_2892_ = l_Lean_Meta_Sym_Arith_arithExt;
                    v___x_2893_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2892_, v___f_2891_, v_a_2863_);
                    if crate::leanh::lean_obj_tag(v___x_2893_) == 0 {
                        v_isSharedCheck_2903_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2903_ == 0 {
                            v_unused_2904_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                            crate::leanh::lean_dec(v_unused_2904_);
                            v___x_2895_ = v___x_2893_;
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2893_);
                            v___x_2895_ = crate::leanh::lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2883_);
                        v_a_2905_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2912_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2912_ == 0 {
                            v___x_2907_ = v___x_2893_;
                            v_isShared_2908_ = v_isSharedCheck_2912_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2905_);
                            crate::leanh::lean_dec(v___x_2893_);
                            v___x_2907_ = crate::leanh::lean_box(0);
                            v_isShared_2908_ = v_isSharedCheck_2912_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2883_);
                    crate::leanh::lean_dec(v_val_2881_);
                    crate::leanh::lean_dec(v_a_2870_);
                    crate::leanh::lean_dec_ref(v_type_2862_);
                    v_a_2913_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    v_isSharedCheck_2920_ = (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                    if v_isSharedCheck_2920_ == 0 {
                        v___x_2915_ = v___x_2885_;
                        v_isShared_2916_ = v_isSharedCheck_2920_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2913_);
                        crate::leanh::lean_dec(v___x_2885_);
                        v___x_2915_ = crate::leanh::lean_box(0);
                        v_isShared_2916_ = v_isSharedCheck_2920_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2884_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2883_, 0, v___x_2888_);
                    v___x_2898_ = v___x_2883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2888_);
                    v___x_2898_ = v_reuseFailAlloc_2902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2895_, 0, v___x_2898_);
                    v___x_2900_ = v___x_2895_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
                    v___x_2900_ = v_reuseFailAlloc_2901_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2900_;
            }
            6 => {
                if v_isShared_2908_ == 0 {
                    v___x_2910_ = v___x_2907_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2911_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
                    v___x_2910_ = v_reuseFailAlloc_2911_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2910_;
            }
            8 => {
                if v_isShared_2916_ == 0 {
                    v___x_2918_ = v___x_2915_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
                    v___x_2918_ = v_reuseFailAlloc_2919_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2918_;
            }
            10 => {
                return v___x_2924_;
            }
            11 => {
                if v_isShared_2930_ == 0 {
                    v___x_2932_ = v___x_2929_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
                    v___x_2932_ = v_reuseFailAlloc_2933_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_2932_;
            }
            13 => {
                if v_isShared_2938_ == 0 {
                    v___x_2940_ = v___x_2937_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
                    v___x_2940_ = v_reuseFailAlloc_2941_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_2940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___boxed(
    mut v_type_2943_: *mut crate::leanh::LeanObject,
    mut v_a_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
    mut v_a_2948_: *mut crate::leanh::LeanObject,
    mut v_a_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2950_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
    crate::leanh::lean_dec(v_a_2948_);
    crate::leanh::lean_dec_ref(v_a_2947_);
    crate::leanh::lean_dec(v_a_2946_);
    crate::leanh::lean_dec_ref(v_a_2945_);
    crate::leanh::lean_dec(v_a_2944_);
    return v_res_2950_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(
    mut v_type_2951_: *mut crate::leanh::LeanObject,
    mut v_a_2952_: *mut crate::leanh::LeanObject,
    mut v_a_2953_: *mut crate::leanh::LeanObject,
    mut v_a_2954_: *mut crate::leanh::LeanObject,
    mut v_a_2955_: *mut crate::leanh::LeanObject,
    mut v_a_2956_: *mut crate::leanh::LeanObject,
    mut v_a_2957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2959_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2951_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
    return v___x_2959_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(
    mut v_type_2960_: *mut crate::leanh::LeanObject,
    mut v_a_2961_: *mut crate::leanh::LeanObject,
    mut v_a_2962_: *mut crate::leanh::LeanObject,
    mut v_a_2963_: *mut crate::leanh::LeanObject,
    mut v_a_2964_: *mut crate::leanh::LeanObject,
    mut v_a_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2968_ =
        l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(
            v_type_2960_,
            v_a_2961_,
            v_a_2962_,
            v_a_2963_,
            v_a_2964_,
            v_a_2965_,
            v_a_2966_,
        );
    crate::leanh::lean_dec(v_a_2966_);
    crate::leanh::lean_dec_ref(v_a_2965_);
    crate::leanh::lean_dec(v_a_2964_);
    crate::leanh::lean_dec_ref(v_a_2963_);
    crate::leanh::lean_dec(v_a_2962_);
    crate::leanh::lean_dec_ref(v_a_2961_);
    return v_res_2968_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(
    mut v_type_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v_val_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v_val_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v_val_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut v___x_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v_val_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v___x_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_a_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut v_a_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v_a_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_a_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_type_2969_);
                v___x_2977_ =
                    l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(
                        v_type_2969_,
                        v_a_2970_,
                        v_a_2971_,
                        v_a_2972_,
                        v_a_2973_,
                        v_a_2974_,
                        v_a_2975_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2977_) == 0 {
                    v_a_2978_ = crate::leanh::lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_3072_ = (!crate::leanh::lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_3072_ == 0 {
                        v___x_2980_ = v___x_2977_;
                        v_isShared_2981_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2978_);
                        crate::leanh::lean_dec(v___x_2977_);
                        v___x_2980_ = crate::leanh::lean_box(0);
                        v_isShared_2981_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_2969_);
                    v_a_3073_ = crate::leanh::lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_3080_ = (!crate::leanh::lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3075_ = v___x_2977_;
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 24;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3073_);
                        crate::leanh::lean_dec(v___x_2977_);
                        v___x_3075_ = crate::leanh::lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2978_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2969_);
                    v_val_2982_ = crate::leanh::lean_ctor_get(v_a_2978_, 0);
                    v_isSharedCheck_2992_ = (!crate::leanh::lean_is_exclusive(v_a_2978_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v___x_2984_ = v_a_2978_;
                        v_isShared_2985_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2982_);
                        crate::leanh::lean_dec(v_a_2978_);
                        v___x_2984_ = crate::leanh::lean_box(0);
                        v_isShared_2985_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2980_);
                    crate::leanh::lean_dec(v_a_2978_);
                    crate::leanh::lean_inc_ref(v_type_2969_);
                    v___x_2993_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if crate::leanh::lean_obj_tag(v___x_2993_) == 0 {
                        v_a_2994_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
                        v_isSharedCheck_3063_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2993_)) as u8;
                        if v_isSharedCheck_3063_ == 0 {
                            v___x_2996_ = v___x_2993_;
                            v_isShared_2997_ = v_isSharedCheck_3063_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2994_);
                            crate::leanh::lean_dec(v___x_2993_);
                            v___x_2996_ = crate::leanh::lean_box(0);
                            v_isShared_2997_ = v_isSharedCheck_3063_;
                            state = 5;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_2969_);
                        v_a_3064_ = crate::leanh::lean_ctor_get(v___x_2993_, 0);
                        v_isSharedCheck_3071_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2993_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3066_ = v___x_2993_;
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3064_);
                            crate::leanh::lean_dec(v___x_2993_);
                            v___x_3066_ = crate::leanh::lean_box(0);
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2985_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2984_, 0);
                    v___x_2987_ = v___x_2984_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_val_2982_);
                    v___x_2987_ = v_reuseFailAlloc_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2981_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2980_, 0, v___x_2987_);
                    v___x_2989_ = v___x_2980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
                    v___x_2989_ = v_reuseFailAlloc_2990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2989_;
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_2994_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2969_);
                    v_val_2998_ = crate::leanh::lean_ctor_get(v_a_2994_, 0);
                    v_isSharedCheck_3008_ = (!crate::leanh::lean_is_exclusive(v_a_2994_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v___x_3000_ = v_a_2994_;
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2998_);
                        crate::leanh::lean_dec(v_a_2994_);
                        v___x_3000_ = crate::leanh::lean_box(0);
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2996_);
                    crate::leanh::lean_dec(v_a_2994_);
                    crate::leanh::lean_inc_ref(v_type_2969_);
                    v___x_3009_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if crate::leanh::lean_obj_tag(v___x_3009_) == 0 {
                        v_a_3010_ = crate::leanh::lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3054_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3054_ == 0 {
                            v___x_3012_ = v___x_3009_;
                            v_isShared_3013_ = v_isSharedCheck_3054_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3010_);
                            crate::leanh::lean_dec(v___x_3009_);
                            v___x_3012_ = crate::leanh::lean_box(0);
                            v_isShared_3013_ = v_isSharedCheck_3054_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_2969_);
                        v_a_3055_ = crate::leanh::lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3062_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3062_ == 0 {
                            v___x_3057_ = v___x_3009_;
                            v_isShared_3058_ = v_isSharedCheck_3062_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3055_);
                            crate::leanh::lean_dec(v___x_3009_);
                            v___x_3057_ = crate::leanh::lean_box(0);
                            v_isShared_3058_ = v_isSharedCheck_3062_;
                            state = 20;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_3001_ == 0 {
                    v___x_3003_ = v___x_3000_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3007_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_val_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3007_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2997_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2996_, 0, v___x_3003_);
                    v___x_3005_ = v___x_2996_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3005_;
            }
            9 => {
                if crate::leanh::lean_obj_tag(v_a_3010_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_2969_);
                    v_val_3014_ = crate::leanh::lean_ctor_get(v_a_3010_, 0);
                    v_isSharedCheck_3024_ = (!crate::leanh::lean_is_exclusive(v_a_3010_)) as u8;
                    if v_isSharedCheck_3024_ == 0 {
                        v___x_3016_ = v_a_3010_;
                        v_isShared_3017_ = v_isSharedCheck_3024_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3014_);
                        crate::leanh::lean_dec(v_a_3010_);
                        v___x_3016_ = crate::leanh::lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3024_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3012_);
                    crate::leanh::lean_dec(v_a_3010_);
                    v___x_3025_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2969_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if crate::leanh::lean_obj_tag(v___x_3025_) == 0 {
                        v_a_3026_ = crate::leanh::lean_ctor_get(v___x_3025_, 0);
                        v_isSharedCheck_3045_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3025_)) as u8;
                        if v_isSharedCheck_3045_ == 0 {
                            v___x_3028_ = v___x_3025_;
                            v_isShared_3029_ = v_isSharedCheck_3045_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3026_);
                            crate::leanh::lean_dec(v___x_3025_);
                            v___x_3028_ = crate::leanh::lean_box(0);
                            v_isShared_3029_ = v_isSharedCheck_3045_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_3046_ = crate::leanh::lean_ctor_get(v___x_3025_, 0);
                        v_isSharedCheck_3053_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3025_)) as u8;
                        if v_isSharedCheck_3053_ == 0 {
                            v___x_3048_ = v___x_3025_;
                            v_isShared_3049_ = v_isSharedCheck_3053_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3046_);
                            crate::leanh::lean_dec(v___x_3025_);
                            v___x_3048_ = crate::leanh::lean_box(0);
                            v_isShared_3049_ = v_isSharedCheck_3053_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_3017_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3016_, 2);
                    v___x_3019_ = v___x_3016_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3023_ = crate::leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_val_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3023_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3012_, 0, v___x_3019_);
                    v___x_3021_ = v___x_3012_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
                    v___x_3021_ = v_reuseFailAlloc_3022_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3021_;
            }
            13 => {
                if crate::leanh::lean_obj_tag(v_a_3026_) == 1 {
                    v_val_3030_ = crate::leanh::lean_ctor_get(v_a_3026_, 0);
                    v_isSharedCheck_3040_ = (!crate::leanh::lean_is_exclusive(v_a_3026_)) as u8;
                    if v_isSharedCheck_3040_ == 0 {
                        v___x_3032_ = v_a_3026_;
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3030_);
                        crate::leanh::lean_dec(v_a_3026_);
                        v___x_3032_ = crate::leanh::lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 14;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3026_);
                    v___x_3041_ = crate::leanh::lean_box(4);
                    if v_isShared_3029_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3028_, 0, v___x_3041_);
                        v___x_3043_ = v___x_3028_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3044_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
                        v___x_3043_ = v_reuseFailAlloc_3044_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3033_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3032_, 3);
                    v___x_3035_ = v___x_3032_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_val_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3039_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3029_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3028_, 0, v___x_3035_);
                    v___x_3037_ = v___x_3028_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3037_;
            }
            17 => {
                return v___x_3043_;
            }
            18 => {
                if v_isShared_3049_ == 0 {
                    v___x_3051_ = v___x_3048_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3052_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
                    v___x_3051_ = v_reuseFailAlloc_3052_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3051_;
            }
            20 => {
                if v_isShared_3058_ == 0 {
                    v___x_3060_ = v___x_3057_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3061_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
                    v___x_3060_ = v_reuseFailAlloc_3061_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3060_;
            }
            22 => {
                if v_isShared_3067_ == 0 {
                    v___x_3069_ = v___x_3066_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3070_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
                    v___x_3069_ = v_reuseFailAlloc_3070_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3069_;
            }
            24 => {
                if v_isShared_3076_ == 0 {
                    v___x_3078_ = v___x_3075_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3079_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
                    v___x_3078_ = v_reuseFailAlloc_3079_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3078_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go___boxed(
    mut v_type_3081_: *mut crate::leanh::LeanObject,
    mut v_a_3082_: *mut crate::leanh::LeanObject,
    mut v_a_3083_: *mut crate::leanh::LeanObject,
    mut v_a_3084_: *mut crate::leanh::LeanObject,
    mut v_a_3085_: *mut crate::leanh::LeanObject,
    mut v_a_3086_: *mut crate::leanh::LeanObject,
    mut v_a_3087_: *mut crate::leanh::LeanObject,
    mut v_a_3088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3089_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(
        v_type_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
        v_a_3087_,
    );
    crate::leanh::lean_dec(v_a_3087_);
    crate::leanh::lean_dec_ref(v_a_3086_);
    crate::leanh::lean_dec(v_a_3085_);
    crate::leanh::lean_dec_ref(v_a_3084_);
    crate::leanh::lean_dec(v_a_3083_);
    crate::leanh::lean_dec_ref(v_a_3082_);
    return v_res_3089_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(
    mut v_type_3090_: *mut crate::leanh::LeanObject,
    mut v_a_3091_: *mut crate::leanh::LeanObject,
    mut v_s_3092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_exp_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rings_3094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_3093_ = crate::leanh::lean_ctor_get(v_s_3092_, 0);
                v_rings_3094_ = crate::leanh::lean_ctor_get(v_s_3092_, 1);
                v_semirings_3095_ = crate::leanh::lean_ctor_get(v_s_3092_, 2);
                v_ncRings_3096_ = crate::leanh::lean_ctor_get(v_s_3092_, 3);
                v_ncSemirings_3097_ = crate::leanh::lean_ctor_get(v_s_3092_, 4);
                v_typeClassify_3098_ = crate::leanh::lean_ctor_get(v_s_3092_, 5);
                v_isSharedCheck_3106_ = (!crate::leanh::lean_is_exclusive(v_s_3092_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3100_ = v_s_3092_;
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_typeClassify_3098_);
                    crate::leanh::lean_inc(v_ncSemirings_3097_);
                    crate::leanh::lean_inc(v_ncRings_3096_);
                    crate::leanh::lean_inc(v_semirings_3095_);
                    crate::leanh::lean_inc(v_rings_3094_);
                    crate::leanh::lean_inc(v_exp_3093_);
                    crate::leanh::lean_dec(v_s_3092_);
                    v___x_3100_ = crate::leanh::lean_box(0);
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3102_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_3098_, v_type_3090_, v_a_3091_);
                if v_isShared_3101_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3100_, 5, v___x_3102_);
                    v___x_3104_ = v___x_3100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = crate::leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_exp_3093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_rings_3094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_semirings_3095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_ncRings_3096_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_ncSemirings_3097_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3105_, 5, v___x_3102_);
                    v___x_3104_ = v_reuseFailAlloc_3105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3104_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_classify_x3f(
    mut v_type_3107_: *mut crate::leanh::LeanObject,
    mut v_a_3108_: *mut crate::leanh::LeanObject,
    mut v_a_3109_: *mut crate::leanh::LeanObject,
    mut v_a_3110_: *mut crate::leanh::LeanObject,
    mut v_a_3111_: *mut crate::leanh::LeanObject,
    mut v_a_3112_: *mut crate::leanh::LeanObject,
    mut v_a_3113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v_typeClassify_3120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_unused_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v_a_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3115_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_3109_, v_a_3112_);
                if crate::leanh::lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = crate::leanh::lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3147_ = (!crate::leanh::lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3147_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3147_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3116_);
                        crate::leanh::lean_dec(v___x_3115_);
                        v___x_3118_ = crate::leanh::lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3147_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3107_);
                    v_a_3148_ = crate::leanh::lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3155_ = (!crate::leanh::lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3155_ == 0 {
                        v___x_3150_ = v___x_3115_;
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3148_);
                        crate::leanh::lean_dec(v___x_3115_);
                        v___x_3150_ = crate::leanh::lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_typeClassify_3120_ = crate::leanh::lean_ctor_get(v_a_3116_, 5);
                crate::leanh::lean_inc_ref(v_typeClassify_3120_);
                crate::leanh::lean_dec(v_a_3116_);
                v___x_3121_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_3120_, v_type_3107_);
                crate::leanh::lean_dec_ref(v_typeClassify_3120_);
                if crate::leanh::lean_obj_tag(v___x_3121_) == 1 {
                    crate::leanh::lean_dec_ref(v_type_3107_);
                    v_val_3122_ = crate::leanh::lean_ctor_get(v___x_3121_, 0);
                    crate::leanh::lean_inc(v_val_3122_);
                    crate::leanh::lean_dec_ref_known(v___x_3121_, 1);
                    if v_isShared_3119_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3118_, 0, v_val_3122_);
                        v___x_3124_ = v___x_3118_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3125_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_val_3122_);
                        v___x_3124_ = v_reuseFailAlloc_3125_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3121_);
                    crate::leanh::lean_del_object(v___x_3118_);
                    crate::leanh::lean_inc_ref(v_type_3107_);
                    v___x_3126_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
                    if crate::leanh::lean_obj_tag(v___x_3126_) == 0 {
                        v_a_3127_ = crate::leanh::lean_ctor_get(v___x_3126_, 0);
                        crate::leanh::lean_inc_n(v_a_3127_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3126_, 1);
                        v___f_3128_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Meta_Sym_Arith_classify_x3f___lam__0 as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        crate::leanh::lean_closure_set(v___f_3128_, 0, v_type_3107_);
                        crate::leanh::lean_closure_set(v___f_3128_, 1, v_a_3127_);
                        v___x_3129_ = l_Lean_Meta_Sym_Arith_arithExt;
                        v___x_3130_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_3129_, v___f_3128_, v_a_3109_);
                        if crate::leanh::lean_obj_tag(v___x_3130_) == 0 {
                            v_isSharedCheck_3137_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3137_ == 0 {
                                v_unused_3138_ = crate::leanh::lean_ctor_get(v___x_3130_, 0);
                                crate::leanh::lean_dec(v_unused_3138_);
                                v___x_3132_ = v___x_3130_;
                                v_isShared_3133_ = v_isSharedCheck_3137_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3130_);
                                v___x_3132_ = crate::leanh::lean_box(0);
                                v_isShared_3133_ = v_isSharedCheck_3137_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3127_);
                            v_a_3139_ = crate::leanh::lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3146_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3146_ == 0 {
                                v___x_3141_ = v___x_3130_;
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3139_);
                                crate::leanh::lean_dec(v___x_3130_);
                                v___x_3141_ = crate::leanh::lean_box(0);
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_type_3107_);
                        return v___x_3126_;
                    }
                }
            }
            2 => {
                return v___x_3124_;
            }
            3 => {
                if v_isShared_3133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3132_, 0, v_a_3127_);
                    v___x_3135_ = v___x_3132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3127_);
                    v___x_3135_ = v_reuseFailAlloc_3136_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3135_;
            }
            5 => {
                if v_isShared_3142_ == 0 {
                    v___x_3144_ = v___x_3141_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
                    v___x_3144_ = v_reuseFailAlloc_3145_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3144_;
            }
            7 => {
                if v_isShared_3151_ == 0 {
                    v___x_3153_ = v___x_3150_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3153_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_Arith_classify_x3f___boxed(
    mut v_type_3156_: *mut crate::leanh::LeanObject,
    mut v_a_3157_: *mut crate::leanh::LeanObject,
    mut v_a_3158_: *mut crate::leanh::LeanObject,
    mut v_a_3159_: *mut crate::leanh::LeanObject,
    mut v_a_3160_: *mut crate::leanh::LeanObject,
    mut v_a_3161_: *mut crate::leanh::LeanObject,
    mut v_a_3162_: *mut crate::leanh::LeanObject,
    mut v_a_3163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_Meta_Sym_Arith_classify_x3f(
        v_type_3156_,
        v_a_3157_,
        v_a_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
        v_a_3162_,
    );
    crate::leanh::lean_dec(v_a_3162_);
    crate::leanh::lean_dec_ref(v_a_3161_);
    crate::leanh::lean_dec(v_a_3160_);
    crate::leanh::lean_dec_ref(v_a_3159_);
    crate::leanh::lean_dec(v_a_3158_);
    crate::leanh::lean_dec_ref(v_a_3157_);
    return v_res_3164_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Classify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Classify(
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
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Classify(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Canon(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Ring(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}

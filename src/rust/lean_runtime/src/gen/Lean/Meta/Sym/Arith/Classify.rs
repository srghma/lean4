// Lean compiler output
// Module: Lean.Meta.Sym.Arith.Classify
// Imports: Lean.Meta.Sym.Arith.EvalNum Lean.Meta.Sym.SynthInstance Lean.Meta.Sym.Canon Lean.Meta.DecLevel Init.Grind.Ring
use crate::r#gen::Init::Grind::Ring::{
    initialize_Init_Grind_Ring, runtime_initialize_Init_Grind_Ring,
};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5,
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
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_7, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [73, 115, 67, 104, 97, 114, 80, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__2_value) as *mut LeanObject,5319903737885873089 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 97, 116, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__0_value) as *mut LeanObject,11442535297760353691 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [78, 97, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__0_value) as *mut LeanObject,12969150934523051142 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value: LeanStringObject<18> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [78, 111, 78, 97, 116, 90, 101, 114, 111, 68, 105, 118, 105, 115, 111, 114, 115, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__2_value) as *mut LeanObject,5648161575337860430 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 109, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [116, 111, 82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__2_value) as *mut LeanObject,12221341192526463479 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [82, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [116, 111, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut LeanObject,14047490016268445595 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value: LeanStringObject<15> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [116, 111, 67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__0_value) as *mut LeanObject,16367934121419604941 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__7_value) as *mut LeanObject,9499613419783151494 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [70, 105, 101, 108, 100, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__9_value) as *mut LeanObject,8615353994042975301 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [67, 111, 109, 109, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut LeanObject,15814158821706329669 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__0_value) as *mut LeanObject,15814158821706329669 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__5_value) as *mut LeanObject,4308150853741380486 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [79, 102, 83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value: LeanStringObject<2> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [81, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__4_value) as *mut LeanObject,10806710915646349764 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__3_value) as *mut LeanObject,8254287559757149654 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__4_value) as *mut LeanObject,12174124158933200568 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value: LeanStringObject<37> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32, 102, 97, 105, 108, 117, 114, 101, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 105, 110, 103, 32, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [83, 101, 109, 105, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value) as *mut LeanObject;
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__0_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__1_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
pub static l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__0_value) as *mut LeanObject,12050285396929189622 as *mut LeanObject] };
static mut l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(
    mut v_e_1583_: *mut LeanObject,
    mut v___y_1584_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1586_: u8 = 0;
    let mut v___x_1587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_postponed_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1600_: u8 = 0;
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1606_: u8 = 0;
    let mut v_unused_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1586_ = l_Lean_Expr_hasMVar(v_e_1583_);
                if v___x_1586_ == 0 {
                    v___x_1587_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1587_, 0, v_e_1583_);
                    return v___x_1587_;
                } else {
                    v___x_1588_ = lean_st_ref_get(v___y_1584_);
                    v_mctx_1589_ = lean_ctor_get(v___x_1588_, 0);
                    lean_inc_ref(v_mctx_1589_);
                    lean_dec(v___x_1588_);
                    v___x_1590_ = l_Lean_instantiateMVarsCore(v_mctx_1589_, v_e_1583_);
                    v_fst_1591_ = lean_ctor_get(v___x_1590_, 0);
                    lean_inc(v_fst_1591_);
                    v_snd_1592_ = lean_ctor_get(v___x_1590_, 1);
                    lean_inc(v_snd_1592_);
                    lean_dec_ref(v___x_1590_);
                    v___x_1593_ = lean_st_ref_take(v___y_1584_);
                    v_cache_1594_ = lean_ctor_get(v___x_1593_, 1);
                    v_zetaDeltaFVarIds_1595_ = lean_ctor_get(v___x_1593_, 2);
                    v_postponed_1596_ = lean_ctor_get(v___x_1593_, 3);
                    v_diag_1597_ = lean_ctor_get(v___x_1593_, 4);
                    v_isSharedCheck_1606_ = (!lean_is_exclusive(v___x_1593_)) as u8;
                    if v_isSharedCheck_1606_ == 0 {
                        v_unused_1607_ = lean_ctor_get(v___x_1593_, 0);
                        lean_dec(v_unused_1607_);
                        v___x_1599_ = v___x_1593_;
                        v_isShared_1600_ = v_isSharedCheck_1606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_diag_1597_);
                        lean_inc(v_postponed_1596_);
                        lean_inc(v_zetaDeltaFVarIds_1595_);
                        lean_inc(v_cache_1594_);
                        lean_dec(v___x_1593_);
                        v___x_1599_ = lean_box(0);
                        v_isShared_1600_ = v_isSharedCheck_1606_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1600_ == 0 {
                    lean_ctor_set(v___x_1599_, 0, v_snd_1592_);
                    v___x_1602_ = v___x_1599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_snd_1592_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 1, v_cache_1594_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_zetaDeltaFVarIds_1595_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 3, v_postponed_1596_);
                    lean_ctor_set(v_reuseFailAlloc_1605_, 4, v_diag_1597_);
                    v___x_1602_ = v_reuseFailAlloc_1605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1603_ = lean_st_ref_set(v___y_1584_, v___x_1602_);
                v___x_1604_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1604_, 0, v_fst_1591_);
                return v___x_1604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg___boxed(
    mut v_e_1608_: *mut LeanObject,
    mut v___y_1609_: *mut LeanObject,
    mut v___y_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1611_: *mut LeanObject = core::ptr::null_mut();
    v_res_1611_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_1608_, v___y_1609_);
    lean_dec(v___y_1609_);
    return v_res_1611_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(
    mut v_e_1612_: *mut LeanObject,
    mut v___y_1613_: *mut LeanObject,
    mut v___y_1614_: *mut LeanObject,
    mut v___y_1615_: *mut LeanObject,
    mut v___y_1616_: *mut LeanObject,
    mut v___y_1617_: *mut LeanObject,
    mut v___y_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    v___x_1620_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_e_1612_, v___y_1616_);
    return v___x_1620_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___boxed(
    mut v_e_1621_: *mut LeanObject,
    mut v___y_1622_: *mut LeanObject,
    mut v___y_1623_: *mut LeanObject,
    mut v___y_1624_: *mut LeanObject,
    mut v___y_1625_: *mut LeanObject,
    mut v___y_1626_: *mut LeanObject,
    mut v___y_1627_: *mut LeanObject,
    mut v___y_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1629_: *mut LeanObject = core::ptr::null_mut();
    v_res_1629_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0(v_e_1621_, v___y_1622_, v___y_1623_, v___y_1624_, v___y_1625_, v___y_1626_, v___y_1627_);
    lean_dec(v___y_1627_);
    lean_dec_ref(v___y_1626_);
    lean_dec(v___y_1625_);
    lean_dec_ref(v___y_1624_);
    lean_dec(v___y_1623_);
    lean_dec_ref(v___y_1622_);
    return v_res_1629_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(
    mut v_k_1630_: *mut LeanObject,
    mut v___y_1631_: *mut LeanObject,
    mut v___y_1632_: *mut LeanObject,
    mut v___y_1633_: *mut LeanObject,
    mut v___y_1634_: *mut LeanObject,
    mut v___y_1635_: *mut LeanObject,
    mut v___y_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___y_1632_);
    lean_inc_ref(v___y_1631_);
    v___x_1638_ = lean_apply_7(
        v_k_1630_,
        v___y_1631_,
        v___y_1632_,
        v___y_1633_,
        v___y_1634_,
        v___y_1635_,
        v___y_1636_,
        lean_box(0),
    );
    return v___x_1638_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed(
    mut v_k_1639_: *mut LeanObject,
    mut v___y_1640_: *mut LeanObject,
    mut v___y_1641_: *mut LeanObject,
    mut v___y_1642_: *mut LeanObject,
    mut v___y_1643_: *mut LeanObject,
    mut v___y_1644_: *mut LeanObject,
    mut v___y_1645_: *mut LeanObject,
    mut v___y_1646_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1647_: *mut LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0(v_k_1639_, v___y_1640_, v___y_1641_, v___y_1642_, v___y_1643_, v___y_1644_, v___y_1645_);
    lean_dec(v___y_1641_);
    lean_dec_ref(v___y_1640_);
    return v_res_1647_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(
    mut v_k_1648_: *mut LeanObject,
    mut v_allowLevelAssignments_1649_: u8,
    mut v___y_1650_: *mut LeanObject,
    mut v___y_1651_: *mut LeanObject,
    mut v___y_1652_: *mut LeanObject,
    mut v___y_1653_: *mut LeanObject,
    mut v___y_1654_: *mut LeanObject,
    mut v___y_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1662_: u8 = 0;
    let mut v___x_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1666_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v___y_1651_);
                lean_inc_ref(v___y_1650_);
                v___f_1657_ = lean_alloc_closure(l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                lean_closure_set(v___f_1657_, 0, v_k_1648_);
                lean_closure_set(v___f_1657_, 1, v___y_1650_);
                lean_closure_set(v___f_1657_, 2, v___y_1651_);
                v___x_1658_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(
                    lean_box(0),
                    v_allowLevelAssignments_1649_,
                    v___f_1657_,
                    v___y_1652_,
                    v___y_1653_,
                    v___y_1654_,
                    v___y_1655_,
                );
                if lean_obj_tag(v___x_1658_) == 0 {
                    return v___x_1658_;
                } else {
                    v_a_1659_ = lean_ctor_get(v___x_1658_, 0);
                    v_isSharedCheck_1666_ = (!lean_is_exclusive(v___x_1658_)) as u8;
                    if v_isSharedCheck_1666_ == 0 {
                        v___x_1661_ = v___x_1658_;
                        v_isShared_1662_ = v_isSharedCheck_1666_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1659_);
                        lean_dec(v___x_1658_);
                        v___x_1661_ = lean_box(0);
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
                    v_reuseFailAlloc_1665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_a_1659_);
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
    mut v_k_1667_: *mut LeanObject,
    mut v_allowLevelAssignments_1668_: *mut LeanObject,
    mut v___y_1669_: *mut LeanObject,
    mut v___y_1670_: *mut LeanObject,
    mut v___y_1671_: *mut LeanObject,
    mut v___y_1672_: *mut LeanObject,
    mut v___y_1673_: *mut LeanObject,
    mut v___y_1674_: *mut LeanObject,
    mut v___y_1675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1676_: u8 = 0;
    let mut v_res_1677_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1676_ = (lean_unbox(v_allowLevelAssignments_1668_) as u8);
    v_res_1677_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_1667_, v_allowLevelAssignments_boxed_1676_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_, v___y_1673_, v___y_1674_);
    lean_dec(v___y_1674_);
    lean_dec_ref(v___y_1673_);
    lean_dec(v___y_1672_);
    lean_dec_ref(v___y_1671_);
    lean_dec(v___y_1670_);
    lean_dec_ref(v___y_1669_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(
    mut v_00_u03b1_1678_: *mut LeanObject,
    mut v_k_1679_: *mut LeanObject,
    mut v_allowLevelAssignments_1680_: u8,
    mut v___y_1681_: *mut LeanObject,
    mut v___y_1682_: *mut LeanObject,
    mut v___y_1683_: *mut LeanObject,
    mut v___y_1684_: *mut LeanObject,
    mut v___y_1685_: *mut LeanObject,
    mut v___y_1686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
    v___x_1688_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v_k_1679_, v_allowLevelAssignments_1680_, v___y_1681_, v___y_1682_, v___y_1683_, v___y_1684_, v___y_1685_, v___y_1686_);
    return v___x_1688_;
}
pub unsafe fn l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___boxed(
    mut v_00_u03b1_1689_: *mut LeanObject,
    mut v_k_1690_: *mut LeanObject,
    mut v_allowLevelAssignments_1691_: *mut LeanObject,
    mut v___y_1692_: *mut LeanObject,
    mut v___y_1693_: *mut LeanObject,
    mut v___y_1694_: *mut LeanObject,
    mut v___y_1695_: *mut LeanObject,
    mut v___y_1696_: *mut LeanObject,
    mut v___y_1697_: *mut LeanObject,
    mut v___y_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_allowLevelAssignments_boxed_1699_: u8 = 0;
    let mut v_res_1700_: *mut LeanObject = core::ptr::null_mut();
    v_allowLevelAssignments_boxed_1699_ = (lean_unbox(v_allowLevelAssignments_1691_) as u8);
    v_res_1700_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1(v_00_u03b1_1689_, v_k_1690_, v_allowLevelAssignments_boxed_1699_, v___y_1692_, v___y_1693_, v___y_1694_, v___y_1695_, v___y_1696_, v___y_1697_);
    lean_dec(v___y_1697_);
    lean_dec_ref(v___y_1696_);
    lean_dec(v___y_1695_);
    lean_dec_ref(v___y_1694_);
    lean_dec(v___y_1693_);
    lean_dec_ref(v___y_1692_);
    return v_res_1700_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0(
    mut v___x_1708_: *mut LeanObject,
    mut v___x_1709_: u8,
    mut v___x_1710_: *mut LeanObject,
    mut v_u_1711_: *mut LeanObject,
    mut v___x_1712_: *mut LeanObject,
    mut v_type_1713_: *mut LeanObject,
    mut v_semiringInst_1714_: *mut LeanObject,
    mut v___y_1715_: *mut LeanObject,
    mut v___y_1716_: *mut LeanObject,
    mut v___y_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_charType_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1732_: u8 = 0;
    let mut v_val_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1740_: u8 = 0;
    let mut v_val_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1752_: u8 = 0;
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1757_: u8 = 0;
    let mut v_a_1758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1761_: u8 = 0;
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1765_: u8 = 0;
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1770_: u8 = 0;
    let mut v_a_1771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1774_: u8 = 0;
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1778_: u8 = 0;
    let mut v_a_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1782_: u8 = 0;
    let mut v___x_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1785_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_1722_) == 0 {
                    v_a_1723_ = lean_ctor_get(v___x_1722_, 0);
                    lean_inc_n(v_a_1723_, 2);
                    lean_dec_ref_known(v___x_1722_, 1);
                    v___x_1724_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___closed__3;
                    v___x_1725_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1725_, 0, v_u_1711_);
                    lean_ctor_set(v___x_1725_, 1, v___x_1712_);
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
                    if lean_obj_tag(v___x_1728_) == 0 {
                        v_a_1729_ = lean_ctor_get(v___x_1728_, 0);
                        v_isSharedCheck_1770_ = (!lean_is_exclusive(v___x_1728_)) as u8;
                        if v_isSharedCheck_1770_ == 0 {
                            v___x_1731_ = v___x_1728_;
                            v_isShared_1732_ = v_isSharedCheck_1770_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1729_);
                            lean_dec(v___x_1728_);
                            v___x_1731_ = lean_box(0);
                            v_isShared_1732_ = v_isSharedCheck_1770_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_1723_);
                        v_a_1771_ = lean_ctor_get(v___x_1728_, 0);
                        v_isSharedCheck_1778_ = (!lean_is_exclusive(v___x_1728_)) as u8;
                        if v_isSharedCheck_1778_ == 0 {
                            v___x_1773_ = v___x_1728_;
                            v_isShared_1774_ = v_isSharedCheck_1778_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_1771_);
                            lean_dec(v___x_1728_);
                            v___x_1773_ = lean_box(0);
                            v_isShared_1774_ = v_isSharedCheck_1778_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_semiringInst_1714_);
                    lean_dec_ref(v_type_1713_);
                    lean_dec(v___x_1712_);
                    lean_dec(v_u_1711_);
                    v_a_1779_ = lean_ctor_get(v___x_1722_, 0);
                    v_isSharedCheck_1786_ = (!lean_is_exclusive(v___x_1722_)) as u8;
                    if v_isSharedCheck_1786_ == 0 {
                        v___x_1781_ = v___x_1722_;
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_1779_);
                        lean_dec(v___x_1722_);
                        v___x_1781_ = lean_box(0);
                        v_isShared_1782_ = v_isSharedCheck_1786_;
                        state = 12;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1729_) == 1 {
                    lean_del_object(v___x_1731_);
                    v_val_1733_ = lean_ctor_get(v_a_1729_, 0);
                    lean_inc(v_val_1733_);
                    lean_dec_ref_known(v_a_1729_, 1);
                    v___x_1734_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__0___redArg(v_a_1723_, v___y_1718_);
                    v_a_1735_ = lean_ctor_get(v___x_1734_, 0);
                    lean_inc(v_a_1735_);
                    lean_dec_ref(v___x_1734_);
                    v___x_1736_ = l_Lean_Meta_Sym_Arith_evalNat_x3f(
                        v_a_1735_,
                        v___y_1715_,
                        v___y_1716_,
                        v___y_1717_,
                        v___y_1718_,
                        v___y_1719_,
                        v___y_1720_,
                    );
                    if lean_obj_tag(v___x_1736_) == 0 {
                        v_a_1737_ = lean_ctor_get(v___x_1736_, 0);
                        v_isSharedCheck_1757_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                        if v_isSharedCheck_1757_ == 0 {
                            v___x_1739_ = v___x_1736_;
                            v_isShared_1740_ = v_isSharedCheck_1757_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1737_);
                            lean_dec(v___x_1736_);
                            v___x_1739_ = lean_box(0);
                            v_isShared_1740_ = v_isSharedCheck_1757_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_1733_);
                        v_a_1758_ = lean_ctor_get(v___x_1736_, 0);
                        v_isSharedCheck_1765_ = (!lean_is_exclusive(v___x_1736_)) as u8;
                        if v_isSharedCheck_1765_ == 0 {
                            v___x_1760_ = v___x_1736_;
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1758_);
                            lean_dec(v___x_1736_);
                            v___x_1760_ = lean_box(0);
                            v_isShared_1761_ = v_isSharedCheck_1765_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1729_);
                    lean_dec(v_a_1723_);
                    v___x_1766_ = lean_box(0);
                    if v_isShared_1732_ == 0 {
                        lean_ctor_set(v___x_1731_, 0, v___x_1766_);
                        v___x_1768_ = v___x_1731_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_1769_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1769_, 0, v___x_1766_);
                        v___x_1768_ = v_reuseFailAlloc_1769_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_1737_) == 1 {
                    v_val_1741_ = lean_ctor_get(v_a_1737_, 0);
                    v_isSharedCheck_1752_ = (!lean_is_exclusive(v_a_1737_)) as u8;
                    if v_isSharedCheck_1752_ == 0 {
                        v___x_1743_ = v_a_1737_;
                        v_isShared_1744_ = v_isSharedCheck_1752_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_1741_);
                        lean_dec(v_a_1737_);
                        v___x_1743_ = lean_box(0);
                        v_isShared_1744_ = v_isSharedCheck_1752_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1737_);
                    lean_dec(v_val_1733_);
                    v___x_1753_ = lean_box(0);
                    if v_isShared_1740_ == 0 {
                        lean_ctor_set(v___x_1739_, 0, v___x_1753_);
                        v___x_1755_ = v___x_1739_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1756_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1756_, 0, v___x_1753_);
                        v___x_1755_ = v_reuseFailAlloc_1756_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_1745_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1745_, 0, v_val_1733_);
                lean_ctor_set(v___x_1745_, 1, v_val_1741_);
                if v_isShared_1744_ == 0 {
                    lean_ctor_set(v___x_1743_, 0, v___x_1745_);
                    v___x_1747_ = v___x_1743_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1751_, 0, v___x_1745_);
                    v___x_1747_ = v_reuseFailAlloc_1751_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1740_ == 0 {
                    lean_ctor_set(v___x_1739_, 0, v___x_1747_);
                    v___x_1749_ = v___x_1739_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1747_);
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
                    v_reuseFailAlloc_1764_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1764_, 0, v_a_1758_);
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
                    v_reuseFailAlloc_1777_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_a_1771_);
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
                    v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
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
    mut v___x_1787_: *mut LeanObject,
    mut v___x_1788_: *mut LeanObject,
    mut v___x_1789_: *mut LeanObject,
    mut v_u_1790_: *mut LeanObject,
    mut v___x_1791_: *mut LeanObject,
    mut v_type_1792_: *mut LeanObject,
    mut v_semiringInst_1793_: *mut LeanObject,
    mut v___y_1794_: *mut LeanObject,
    mut v___y_1795_: *mut LeanObject,
    mut v___y_1796_: *mut LeanObject,
    mut v___y_1797_: *mut LeanObject,
    mut v___y_1798_: *mut LeanObject,
    mut v___y_1799_: *mut LeanObject,
    mut v___y_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3810__boxed_1801_: u8 = 0;
    let mut v_res_1802_: *mut LeanObject = core::ptr::null_mut();
    v___x_3810__boxed_1801_ = (lean_unbox(v___x_1788_) as u8);
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
    lean_dec(v___y_1799_);
    lean_dec_ref(v___y_1798_);
    lean_dec(v___y_1797_);
    lean_dec_ref(v___y_1796_);
    lean_dec(v___y_1795_);
    lean_dec_ref(v___y_1794_);
    return v_res_1802_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2()
-> *mut LeanObject {
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    v___x_1806_ = lean_box(0);
    v___x_1807_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__1;
    v___x_1808_ = l_Lean_mkConst(v___x_1807_, v___x_1806_);
    return v___x_1808_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3()
-> *mut LeanObject {
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    v___x_1809_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__2);
    v___x_1810_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1810_, 0, v___x_1809_);
    return v___x_1810_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(
    mut v_u_1811_: *mut LeanObject,
    mut v_type_1812_: *mut LeanObject,
    mut v_semiringInst_1813_: *mut LeanObject,
    mut v_a_1814_: *mut LeanObject,
    mut v_a_1815_: *mut LeanObject,
    mut v_a_1816_: *mut LeanObject,
    mut v_a_1817_: *mut LeanObject,
    mut v_a_1818_: *mut LeanObject,
    mut v_a_1819_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v___x_1828_: *mut LeanObject = core::ptr::null_mut();
    v___x_1821_ = lean_box(0);
    v___x_1822_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___closed__3);
    v___x_1823_ = 0;
    v___x_1824_ = lean_box(0);
    v___x_1825_ = lean_box((v___x_1823_) as usize);
    v___f_1826_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
    lean_closure_set(v___f_1826_, 0, v___x_1822_);
    lean_closure_set(v___f_1826_, 1, v___x_1825_);
    lean_closure_set(v___f_1826_, 2, v___x_1824_);
    lean_closure_set(v___f_1826_, 3, v_u_1811_);
    lean_closure_set(v___f_1826_, 4, v___x_1821_);
    lean_closure_set(v___f_1826_, 5, v_type_1812_);
    lean_closure_set(v___f_1826_, 6, v_semiringInst_1813_);
    v___x_1827_ = 0;
    v___x_1828_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f_spec__1___redArg(v___f_1826_, v___x_1827_, v_a_1814_, v_a_1815_, v_a_1816_, v_a_1817_, v_a_1818_, v_a_1819_);
    return v___x_1828_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f___boxed(
    mut v_u_1829_: *mut LeanObject,
    mut v_type_1830_: *mut LeanObject,
    mut v_semiringInst_1831_: *mut LeanObject,
    mut v_a_1832_: *mut LeanObject,
    mut v_a_1833_: *mut LeanObject,
    mut v_a_1834_: *mut LeanObject,
    mut v_a_1835_: *mut LeanObject,
    mut v_a_1836_: *mut LeanObject,
    mut v_a_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1839_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1837_);
    lean_dec_ref(v_a_1836_);
    lean_dec(v_a_1835_);
    lean_dec_ref(v_a_1834_);
    lean_dec(v_a_1833_);
    lean_dec_ref(v_a_1832_);
    return v_res_1839_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(
    mut v_u_1850_: *mut LeanObject,
    mut v_type_1851_: *mut LeanObject,
    mut v_a_1852_: *mut LeanObject,
    mut v_a_1853_: *mut LeanObject,
    mut v_a_1854_: *mut LeanObject,
    mut v_a_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleType_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1866_: u8 = 0;
    let mut v_val_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1857_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg___closed__1;
                v___x_1858_ = lean_box(0);
                v___x_1859_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_1859_, 0, v_u_1850_);
                lean_ctor_set(v___x_1859_, 1, v___x_1858_);
                lean_inc_ref(v___x_1859_);
                v___x_1860_ = l_Lean_mkConst(v___x_1857_, v___x_1859_);
                lean_inc_ref(v_type_1851_);
                v_natModuleType_1861_ = l_Lean_Expr_app___override(v___x_1860_, v_type_1851_);
                v___x_1862_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                    v_natModuleType_1861_,
                    v_a_1852_,
                    v_a_1853_,
                    v_a_1854_,
                    v_a_1855_,
                );
                if lean_obj_tag(v___x_1862_) == 0 {
                    v_a_1863_ = lean_ctor_get(v___x_1862_, 0);
                    v_isSharedCheck_1876_ = (!lean_is_exclusive(v___x_1862_)) as u8;
                    if v_isSharedCheck_1876_ == 0 {
                        v___x_1865_ = v___x_1862_;
                        v_isShared_1866_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1863_);
                        lean_dec(v___x_1862_);
                        v___x_1865_ = lean_box(0);
                        v_isShared_1866_ = v_isSharedCheck_1876_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_1859_, 2);
                    lean_dec_ref(v_type_1851_);
                    return v___x_1862_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1863_) == 1 {
                    lean_del_object(v___x_1865_);
                    v_val_1867_ = lean_ctor_get(v_a_1863_, 0);
                    lean_inc(v_val_1867_);
                    lean_dec_ref_known(v_a_1863_, 1);
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
                    lean_dec(v_a_1863_);
                    lean_dec_ref_known(v___x_1859_, 2);
                    lean_dec_ref(v_type_1851_);
                    v___x_1872_ = lean_box(0);
                    if v_isShared_1866_ == 0 {
                        lean_ctor_set(v___x_1865_, 0, v___x_1872_);
                        v___x_1874_ = v___x_1865_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1872_);
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
    mut v_u_1877_: *mut LeanObject,
    mut v_type_1878_: *mut LeanObject,
    mut v_a_1879_: *mut LeanObject,
    mut v_a_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
    mut v_a_1883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1884_: *mut LeanObject = core::ptr::null_mut();
    v_res_1884_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_1877_, v_type_1878_, v_a_1879_, v_a_1880_, v_a_1881_, v_a_1882_);
    lean_dec(v_a_1882_);
    lean_dec_ref(v_a_1881_);
    lean_dec(v_a_1880_);
    lean_dec_ref(v_a_1879_);
    return v_res_1884_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f(
    mut v_u_1885_: *mut LeanObject,
    mut v_type_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
    mut v_a_1889_: *mut LeanObject,
    mut v_a_1890_: *mut LeanObject,
    mut v_a_1891_: *mut LeanObject,
    mut v_a_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1894_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_u_1885_, v_type_1886_, v_a_1889_, v_a_1890_, v_a_1891_, v_a_1892_);
    return v___x_1894_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___boxed(
    mut v_u_1895_: *mut LeanObject,
    mut v_type_1896_: *mut LeanObject,
    mut v_a_1897_: *mut LeanObject,
    mut v_a_1898_: *mut LeanObject,
    mut v_a_1899_: *mut LeanObject,
    mut v_a_1900_: *mut LeanObject,
    mut v_a_1901_: *mut LeanObject,
    mut v_a_1902_: *mut LeanObject,
    mut v_a_1903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1904_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1902_);
    lean_dec_ref(v_a_1901_);
    lean_dec(v_a_1900_);
    lean_dec_ref(v_a_1899_);
    lean_dec(v_a_1898_);
    lean_dec_ref(v_a_1897_);
    return v_res_1904_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0(
    mut v___x_1905_: *mut LeanObject,
    mut v_s_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1915_: u8 = 0;
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_1907_ = lean_ctor_get(v_s_1906_, 0);
                v_rings_1908_ = lean_ctor_get(v_s_1906_, 1);
                v_semirings_1909_ = lean_ctor_get(v_s_1906_, 2);
                v_ncRings_1910_ = lean_ctor_get(v_s_1906_, 3);
                v_ncSemirings_1911_ = lean_ctor_get(v_s_1906_, 4);
                v_typeClassify_1912_ = lean_ctor_get(v_s_1906_, 5);
                v_isSharedCheck_1920_ = (!lean_is_exclusive(v_s_1906_)) as u8;
                if v_isSharedCheck_1920_ == 0 {
                    v___x_1914_ = v_s_1906_;
                    v_isShared_1915_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_1912_);
                    lean_inc(v_ncSemirings_1911_);
                    lean_inc(v_ncRings_1910_);
                    lean_inc(v_semirings_1909_);
                    lean_inc(v_rings_1908_);
                    lean_inc(v_exp_1907_);
                    lean_dec(v_s_1906_);
                    v___x_1914_ = lean_box(0);
                    v_isShared_1915_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1916_ = lean_array_push(v_rings_1908_, v___x_1905_);
                if v_isShared_1915_ == 0 {
                    lean_ctor_set(v___x_1914_, 1, v___x_1916_);
                    v___x_1918_ = v___x_1914_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1919_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 0, v_exp_1907_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 1, v___x_1916_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 2, v_semirings_1909_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 3, v_ncRings_1910_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 4, v_ncSemirings_1911_);
                    lean_ctor_set(v_reuseFailAlloc_1919_, 5, v_typeClassify_1912_);
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
    mut v_type_1950_: *mut LeanObject,
    mut v_a_1951_: *mut LeanObject,
    mut v_a_1952_: *mut LeanObject,
    mut v_a_1953_: *mut LeanObject,
    mut v_a_1954_: *mut LeanObject,
    mut v_a_1955_: *mut LeanObject,
    mut v_a_1956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1969_: u8 = 0;
    let mut v_val_1970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1973_: u8 = 0;
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2004_: u8 = 0;
    let mut v___x_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_unused_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2016_: u8 = 0;
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_a_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2024_: u8 = 0;
    let mut v___x_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2028_: u8 = 0;
    let mut v_a_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2032_: u8 = 0;
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2036_: u8 = 0;
    let mut v_a_2037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2040_: u8 = 0;
    let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2044_: u8 = 0;
    let mut v_a_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2048_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2052_: u8 = 0;
    let mut v_isSharedCheck_2053_: u8 = 0;
    let mut v___x_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2058_: u8 = 0;
    let mut v_a_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2062_: u8 = 0;
    let mut v___x_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2066_: u8 = 0;
    let mut v_a_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2070_: u8 = 0;
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_1950_);
                v___x_1958_ = l_Lean_Meta_getDecLevel(
                    v_type_1950_,
                    v_a_1953_,
                    v_a_1954_,
                    v_a_1955_,
                    v_a_1956_,
                );
                if lean_obj_tag(v___x_1958_) == 0 {
                    v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
                    lean_inc_n(v_a_1959_, 2);
                    lean_dec_ref_known(v___x_1958_, 1);
                    v___x_1960_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__1;
                    v___x_1961_ = lean_box(0);
                    v___x_1962_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1962_, 0, v_a_1959_);
                    lean_ctor_set(v___x_1962_, 1, v___x_1961_);
                    lean_inc_ref(v___x_1962_);
                    v___x_1963_ = l_Lean_mkConst(v___x_1960_, v___x_1962_);
                    lean_inc_ref(v_type_1950_);
                    v___x_1964_ = l_Lean_Expr_app___override(v___x_1963_, v_type_1950_);
                    v___x_1965_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_1964_,
                        v_a_1953_,
                        v_a_1954_,
                        v_a_1955_,
                        v_a_1956_,
                    );
                    if lean_obj_tag(v___x_1965_) == 0 {
                        v_a_1966_ = lean_ctor_get(v___x_1965_, 0);
                        v_isSharedCheck_2058_ = (!lean_is_exclusive(v___x_1965_)) as u8;
                        if v_isSharedCheck_2058_ == 0 {
                            v___x_1968_ = v___x_1965_;
                            v_isShared_1969_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1966_);
                            lean_dec(v___x_1965_);
                            v___x_1968_ = lean_box(0);
                            v_isShared_1969_ = v_isSharedCheck_2058_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_1962_, 2);
                        lean_dec(v_a_1959_);
                        lean_dec_ref(v_type_1950_);
                        v_a_2059_ = lean_ctor_get(v___x_1965_, 0);
                        v_isSharedCheck_2066_ = (!lean_is_exclusive(v___x_1965_)) as u8;
                        if v_isSharedCheck_2066_ == 0 {
                            v___x_2061_ = v___x_1965_;
                            v_isShared_2062_ = v_isSharedCheck_2066_;
                            state = 17;
                            continue;
                        } else {
                            lean_inc(v_a_2059_);
                            lean_dec(v___x_1965_);
                            v___x_2061_ = lean_box(0);
                            v_isShared_2062_ = v_isSharedCheck_2066_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_1950_);
                    v_a_2067_ = lean_ctor_get(v___x_1958_, 0);
                    v_isSharedCheck_2074_ = (!lean_is_exclusive(v___x_1958_)) as u8;
                    if v_isSharedCheck_2074_ == 0 {
                        v___x_2069_ = v___x_1958_;
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 19;
                        continue;
                    } else {
                        lean_inc(v_a_2067_);
                        lean_dec(v___x_1958_);
                        v___x_2069_ = lean_box(0);
                        v_isShared_2070_ = v_isSharedCheck_2074_;
                        state = 19;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1966_) == 1 {
                    lean_del_object(v___x_1968_);
                    v_val_1970_ = lean_ctor_get(v_a_1966_, 0);
                    v_isSharedCheck_2053_ = (!lean_is_exclusive(v_a_1966_)) as u8;
                    if v_isSharedCheck_2053_ == 0 {
                        v___x_1972_ = v_a_1966_;
                        v_isShared_1973_ = v_isSharedCheck_2053_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_1970_);
                        lean_dec(v_a_1966_);
                        v___x_1972_ = lean_box(0);
                        v_isShared_1973_ = v_isSharedCheck_2053_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_1966_);
                    lean_dec_ref_known(v___x_1962_, 2);
                    lean_dec(v_a_1959_);
                    lean_dec_ref(v_type_1950_);
                    v___x_2054_ = lean_box(0);
                    if v_isShared_1969_ == 0 {
                        lean_ctor_set(v___x_1968_, 0, v___x_2054_);
                        v___x_2056_ = v___x_1968_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2057_, 0, v___x_2054_);
                        v___x_2056_ = v_reuseFailAlloc_2057_;
                        state = 16;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1974_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__3;
                lean_inc_ref_n(v___x_1962_, 3);
                v___x_1975_ = l_Lean_mkConst(v___x_1974_, v___x_1962_);
                lean_inc(v_val_1970_);
                lean_inc_ref_n(v_type_1950_, 4);
                v___x_1976_ = l_Lean_mkAppB(v___x_1975_, v_type_1950_, v_val_1970_);
                v___x_1977_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6;
                v___x_1978_ = l_Lean_mkConst(v___x_1977_, v___x_1962_);
                lean_inc_ref(v___x_1976_);
                v___x_1979_ = l_Lean_mkAppB(v___x_1978_, v_type_1950_, v___x_1976_);
                v___x_1980_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__8;
                v___x_1981_ = l_Lean_mkConst(v___x_1980_, v___x_1962_);
                lean_inc_ref_n(v___x_1979_, 2);
                v___x_1982_ = l_Lean_mkAppB(v___x_1981_, v_type_1950_, v___x_1979_);
                lean_inc(v_a_1959_);
                v___x_1983_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_1959_, v_type_1950_, v___x_1979_, v_a_1951_, v_a_1952_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
                if lean_obj_tag(v___x_1983_) == 0 {
                    v_a_1984_ = lean_ctor_get(v___x_1983_, 0);
                    lean_inc(v_a_1984_);
                    lean_dec_ref_known(v___x_1983_, 1);
                    lean_inc_ref(v_type_1950_);
                    lean_inc(v_a_1959_);
                    v___x_1985_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getNoZeroDivInst_x3f___redArg(v_a_1959_, v_type_1950_, v_a_1953_, v_a_1954_, v_a_1955_, v_a_1956_);
                    if lean_obj_tag(v___x_1985_) == 0 {
                        v_a_1986_ = lean_ctor_get(v___x_1985_, 0);
                        lean_inc(v_a_1986_);
                        lean_dec_ref_known(v___x_1985_, 1);
                        v___x_1987_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__10;
                        v___x_1988_ = l_Lean_mkConst(v___x_1987_, v___x_1962_);
                        lean_inc_ref(v_type_1950_);
                        v___x_1989_ = l_Lean_Expr_app___override(v___x_1988_, v_type_1950_);
                        v___x_1990_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                            v___x_1989_,
                            v_a_1953_,
                            v_a_1954_,
                            v_a_1955_,
                            v_a_1956_,
                        );
                        if lean_obj_tag(v___x_1990_) == 0 {
                            v_a_1991_ = lean_ctor_get(v___x_1990_, 0);
                            lean_inc(v_a_1991_);
                            lean_dec_ref_known(v___x_1990_, 1);
                            v___x_1992_ =
                                l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_1952_, v_a_1955_);
                            if lean_obj_tag(v___x_1992_) == 0 {
                                v_a_1993_ = lean_ctor_get(v___x_1992_, 0);
                                lean_inc(v_a_1993_);
                                lean_dec_ref_known(v___x_1992_, 1);
                                v_rings_1994_ = lean_ctor_get(v_a_1993_, 1);
                                lean_inc_ref(v_rings_1994_);
                                lean_dec(v_a_1993_);
                                v___x_1995_ = lean_box(0);
                                v___x_1996_ = lean_array_get_size(v_rings_1994_);
                                lean_dec_ref(v_rings_1994_);
                                v___x_1997_ = lean_alloc_ctor(0, 14, (0) as u32);
                                lean_ctor_set(v___x_1997_, 0, v___x_1996_);
                                lean_ctor_set(v___x_1997_, 1, v_type_1950_);
                                lean_ctor_set(v___x_1997_, 2, v_a_1959_);
                                lean_ctor_set(v___x_1997_, 3, v___x_1976_);
                                lean_ctor_set(v___x_1997_, 4, v___x_1979_);
                                lean_ctor_set(v___x_1997_, 5, v_a_1984_);
                                lean_ctor_set(v___x_1997_, 6, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 7, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 8, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 9, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 10, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 11, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 12, v___x_1995_);
                                lean_ctor_set(v___x_1997_, 13, v___x_1995_);
                                v___x_1998_ = lean_alloc_ctor(0, 7, (0) as u32);
                                lean_ctor_set(v___x_1998_, 0, v___x_1997_);
                                lean_ctor_set(v___x_1998_, 1, v___x_1995_);
                                lean_ctor_set(v___x_1998_, 2, v___x_1995_);
                                lean_ctor_set(v___x_1998_, 3, v___x_1982_);
                                lean_ctor_set(v___x_1998_, 4, v_val_1970_);
                                lean_ctor_set(v___x_1998_, 5, v_a_1986_);
                                lean_ctor_set(v___x_1998_, 6, v_a_1991_);
                                v___f_1999_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                                lean_closure_set(v___f_1999_, 0, v___x_1998_);
                                v___x_2000_ = l_Lean_Meta_Sym_Arith_arithExt;
                                v___x_2001_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2000_, v___f_1999_, v_a_1952_);
                                if lean_obj_tag(v___x_2001_) == 0 {
                                    v_isSharedCheck_2011_ = (!lean_is_exclusive(v___x_2001_)) as u8;
                                    if v_isSharedCheck_2011_ == 0 {
                                        v_unused_2012_ = lean_ctor_get(v___x_2001_, 0);
                                        lean_dec(v_unused_2012_);
                                        v___x_2003_ = v___x_2001_;
                                        v_isShared_2004_ = v_isSharedCheck_2011_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_dec(v___x_2001_);
                                        v___x_2003_ = lean_box(0);
                                        v_isShared_2004_ = v_isSharedCheck_2011_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_del_object(v___x_1972_);
                                    v_a_2013_ = lean_ctor_get(v___x_2001_, 0);
                                    v_isSharedCheck_2020_ = (!lean_is_exclusive(v___x_2001_)) as u8;
                                    if v_isSharedCheck_2020_ == 0 {
                                        v___x_2015_ = v___x_2001_;
                                        v_isShared_2016_ = v_isSharedCheck_2020_;
                                        state = 6;
                                        continue;
                                    } else {
                                        lean_inc(v_a_2013_);
                                        lean_dec(v___x_2001_);
                                        v___x_2015_ = lean_box(0);
                                        v_isShared_2016_ = v_isSharedCheck_2020_;
                                        state = 6;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_1991_);
                                lean_dec(v_a_1986_);
                                lean_dec(v_a_1984_);
                                lean_dec_ref(v___x_1982_);
                                lean_dec_ref(v___x_1979_);
                                lean_dec_ref(v___x_1976_);
                                lean_del_object(v___x_1972_);
                                lean_dec(v_val_1970_);
                                lean_dec(v_a_1959_);
                                lean_dec_ref(v_type_1950_);
                                v_a_2021_ = lean_ctor_get(v___x_1992_, 0);
                                v_isSharedCheck_2028_ = (!lean_is_exclusive(v___x_1992_)) as u8;
                                if v_isSharedCheck_2028_ == 0 {
                                    v___x_2023_ = v___x_1992_;
                                    v_isShared_2024_ = v_isSharedCheck_2028_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_2021_);
                                    lean_dec(v___x_1992_);
                                    v___x_2023_ = lean_box(0);
                                    v_isShared_2024_ = v_isSharedCheck_2028_;
                                    state = 8;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_1986_);
                            lean_dec(v_a_1984_);
                            lean_dec_ref(v___x_1982_);
                            lean_dec_ref(v___x_1979_);
                            lean_dec_ref(v___x_1976_);
                            lean_del_object(v___x_1972_);
                            lean_dec(v_val_1970_);
                            lean_dec(v_a_1959_);
                            lean_dec_ref(v_type_1950_);
                            v_a_2029_ = lean_ctor_get(v___x_1990_, 0);
                            v_isSharedCheck_2036_ = (!lean_is_exclusive(v___x_1990_)) as u8;
                            if v_isSharedCheck_2036_ == 0 {
                                v___x_2031_ = v___x_1990_;
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_2029_);
                                lean_dec(v___x_1990_);
                                v___x_2031_ = lean_box(0);
                                v_isShared_2032_ = v_isSharedCheck_2036_;
                                state = 10;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1984_);
                        lean_dec_ref(v___x_1982_);
                        lean_dec_ref(v___x_1979_);
                        lean_dec_ref(v___x_1976_);
                        lean_del_object(v___x_1972_);
                        lean_dec(v_val_1970_);
                        lean_dec_ref_known(v___x_1962_, 2);
                        lean_dec(v_a_1959_);
                        lean_dec_ref(v_type_1950_);
                        v_a_2037_ = lean_ctor_get(v___x_1985_, 0);
                        v_isSharedCheck_2044_ = (!lean_is_exclusive(v___x_1985_)) as u8;
                        if v_isSharedCheck_2044_ == 0 {
                            v___x_2039_ = v___x_1985_;
                            v_isShared_2040_ = v_isSharedCheck_2044_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2037_);
                            lean_dec(v___x_1985_);
                            v___x_2039_ = lean_box(0);
                            v_isShared_2040_ = v_isSharedCheck_2044_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_1982_);
                    lean_dec_ref(v___x_1979_);
                    lean_dec_ref(v___x_1976_);
                    lean_del_object(v___x_1972_);
                    lean_dec(v_val_1970_);
                    lean_dec_ref_known(v___x_1962_, 2);
                    lean_dec(v_a_1959_);
                    lean_dec_ref(v_type_1950_);
                    v_a_2045_ = lean_ctor_get(v___x_1983_, 0);
                    v_isSharedCheck_2052_ = (!lean_is_exclusive(v___x_1983_)) as u8;
                    if v_isSharedCheck_2052_ == 0 {
                        v___x_2047_ = v___x_1983_;
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_2045_);
                        lean_dec(v___x_1983_);
                        v___x_2047_ = lean_box(0);
                        v_isShared_2048_ = v_isSharedCheck_2052_;
                        state = 14;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1973_ == 0 {
                    lean_ctor_set(v___x_1972_, 0, v___x_1996_);
                    v___x_2006_ = v___x_1972_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2010_, 0, v___x_1996_);
                    v___x_2006_ = v_reuseFailAlloc_2010_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2004_ == 0 {
                    lean_ctor_set(v___x_2003_, 0, v___x_2006_);
                    v___x_2008_ = v___x_2003_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2009_, 0, v___x_2006_);
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
                    v_reuseFailAlloc_2019_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 0, v_a_2013_);
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
                    v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2027_, 0, v_a_2021_);
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
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v_a_2029_);
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
                    v_reuseFailAlloc_2043_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_a_2037_);
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
                    v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_a_2045_);
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
                    v_reuseFailAlloc_2065_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2065_, 0, v_a_2059_);
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
                    v_reuseFailAlloc_2073_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2073_, 0, v_a_2067_);
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
    mut v_type_2075_: *mut LeanObject,
    mut v_a_2076_: *mut LeanObject,
    mut v_a_2077_: *mut LeanObject,
    mut v_a_2078_: *mut LeanObject,
    mut v_a_2079_: *mut LeanObject,
    mut v_a_2080_: *mut LeanObject,
    mut v_a_2081_: *mut LeanObject,
    mut v_a_2082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2083_: *mut LeanObject = core::ptr::null_mut();
    v_res_2083_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(
        v_type_2075_,
        v_a_2076_,
        v_a_2077_,
        v_a_2078_,
        v_a_2079_,
        v_a_2080_,
        v_a_2081_,
    );
    lean_dec(v_a_2081_);
    lean_dec_ref(v_a_2080_);
    lean_dec(v_a_2079_);
    lean_dec_ref(v_a_2078_);
    lean_dec(v_a_2077_);
    lean_dec_ref(v_a_2076_);
    return v_res_2083_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0(
    mut v___x_2084_: *mut LeanObject,
    mut v_s_2085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2099_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2086_ = lean_ctor_get(v_s_2085_, 0);
                v_rings_2087_ = lean_ctor_get(v_s_2085_, 1);
                v_semirings_2088_ = lean_ctor_get(v_s_2085_, 2);
                v_ncRings_2089_ = lean_ctor_get(v_s_2085_, 3);
                v_ncSemirings_2090_ = lean_ctor_get(v_s_2085_, 4);
                v_typeClassify_2091_ = lean_ctor_get(v_s_2085_, 5);
                v_isSharedCheck_2099_ = (!lean_is_exclusive(v_s_2085_)) as u8;
                if v_isSharedCheck_2099_ == 0 {
                    v___x_2093_ = v_s_2085_;
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_2091_);
                    lean_inc(v_ncSemirings_2090_);
                    lean_inc(v_ncRings_2089_);
                    lean_inc(v_semirings_2088_);
                    lean_inc(v_rings_2087_);
                    lean_inc(v_exp_2086_);
                    lean_dec(v_s_2085_);
                    v___x_2093_ = lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2099_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2095_ = lean_array_push(v_ncRings_2089_, v___x_2084_);
                if v_isShared_2094_ == 0 {
                    lean_ctor_set(v___x_2093_, 3, v___x_2095_);
                    v___x_2097_ = v___x_2093_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2098_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 0, v_exp_2086_);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 1, v_rings_2087_);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 2, v_semirings_2088_);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 3, v___x_2095_);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 4, v_ncSemirings_2090_);
                    lean_ctor_set(v_reuseFailAlloc_2098_, 5, v_typeClassify_2091_);
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
    mut v_type_2104_: *mut LeanObject,
    mut v_a_2105_: *mut LeanObject,
    mut v_a_2106_: *mut LeanObject,
    mut v_a_2107_: *mut LeanObject,
    mut v_a_2108_: *mut LeanObject,
    mut v_a_2109_: *mut LeanObject,
    mut v_a_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2123_: u8 = 0;
    let mut v_val_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2127_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2151_: u8 = 0;
    let mut v_unused_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2156_: u8 = 0;
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_a_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2164_: u8 = 0;
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_a_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2172_: u8 = 0;
    let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2176_: u8 = 0;
    let mut v_isSharedCheck_2177_: u8 = 0;
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2182_: u8 = 0;
    let mut v_a_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2186_: u8 = 0;
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2190_: u8 = 0;
    let mut v_a_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2194_: u8 = 0;
    let mut v___x_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2198_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2104_);
                v___x_2112_ = l_Lean_Meta_getDecLevel(
                    v_type_2104_,
                    v_a_2107_,
                    v_a_2108_,
                    v_a_2109_,
                    v_a_2110_,
                );
                if lean_obj_tag(v___x_2112_) == 0 {
                    v_a_2113_ = lean_ctor_get(v___x_2112_, 0);
                    lean_inc_n(v_a_2113_, 2);
                    lean_dec_ref_known(v___x_2112_, 1);
                    v___x_2114_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___closed__0;
                    v___x_2115_ = lean_box(0);
                    v___x_2116_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2116_, 0, v_a_2113_);
                    lean_ctor_set(v___x_2116_, 1, v___x_2115_);
                    lean_inc_ref(v___x_2116_);
                    v___x_2117_ = l_Lean_mkConst(v___x_2114_, v___x_2116_);
                    lean_inc_ref(v_type_2104_);
                    v___x_2118_ = l_Lean_Expr_app___override(v___x_2117_, v_type_2104_);
                    v___x_2119_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2118_,
                        v_a_2107_,
                        v_a_2108_,
                        v_a_2109_,
                        v_a_2110_,
                    );
                    if lean_obj_tag(v___x_2119_) == 0 {
                        v_a_2120_ = lean_ctor_get(v___x_2119_, 0);
                        v_isSharedCheck_2182_ = (!lean_is_exclusive(v___x_2119_)) as u8;
                        if v_isSharedCheck_2182_ == 0 {
                            v___x_2122_ = v___x_2119_;
                            v_isShared_2123_ = v_isSharedCheck_2182_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2120_);
                            lean_dec(v___x_2119_);
                            v___x_2122_ = lean_box(0);
                            v_isShared_2123_ = v_isSharedCheck_2182_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2116_, 2);
                        lean_dec(v_a_2113_);
                        lean_dec_ref(v_type_2104_);
                        v_a_2183_ = lean_ctor_get(v___x_2119_, 0);
                        v_isSharedCheck_2190_ = (!lean_is_exclusive(v___x_2119_)) as u8;
                        if v_isSharedCheck_2190_ == 0 {
                            v___x_2185_ = v___x_2119_;
                            v_isShared_2186_ = v_isSharedCheck_2190_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_2183_);
                            lean_dec(v___x_2119_);
                            v___x_2185_ = lean_box(0);
                            v_isShared_2186_ = v_isSharedCheck_2190_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2104_);
                    v_a_2191_ = lean_ctor_get(v___x_2112_, 0);
                    v_isSharedCheck_2198_ = (!lean_is_exclusive(v___x_2112_)) as u8;
                    if v_isSharedCheck_2198_ == 0 {
                        v___x_2193_ = v___x_2112_;
                        v_isShared_2194_ = v_isSharedCheck_2198_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2191_);
                        lean_dec(v___x_2112_);
                        v___x_2193_ = lean_box(0);
                        v_isShared_2194_ = v_isSharedCheck_2198_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2120_) == 1 {
                    lean_del_object(v___x_2122_);
                    v_val_2124_ = lean_ctor_get(v_a_2120_, 0);
                    v_isSharedCheck_2177_ = (!lean_is_exclusive(v_a_2120_)) as u8;
                    if v_isSharedCheck_2177_ == 0 {
                        v___x_2126_ = v_a_2120_;
                        v_isShared_2127_ = v_isSharedCheck_2177_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2124_);
                        lean_dec(v_a_2120_);
                        v___x_2126_ = lean_box(0);
                        v_isShared_2127_ = v_isSharedCheck_2177_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2120_);
                    lean_dec_ref_known(v___x_2116_, 2);
                    lean_dec(v_a_2113_);
                    lean_dec_ref(v_type_2104_);
                    v___x_2178_ = lean_box(0);
                    if v_isShared_2123_ == 0 {
                        lean_ctor_set(v___x_2122_, 0, v___x_2178_);
                        v___x_2180_ = v___x_2122_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2181_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2181_, 0, v___x_2178_);
                        v___x_2180_ = v_reuseFailAlloc_2181_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2128_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f___closed__6;
                v___x_2129_ = l_Lean_mkConst(v___x_2128_, v___x_2116_);
                lean_inc(v_val_2124_);
                lean_inc_ref_n(v_type_2104_, 2);
                v___x_2130_ = l_Lean_mkAppB(v___x_2129_, v_type_2104_, v_val_2124_);
                lean_inc_ref(v___x_2130_);
                lean_inc(v_a_2113_);
                v___x_2131_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_getIsCharInst_x3f(v_a_2113_, v_type_2104_, v___x_2130_, v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
                if lean_obj_tag(v___x_2131_) == 0 {
                    v_a_2132_ = lean_ctor_get(v___x_2131_, 0);
                    lean_inc(v_a_2132_);
                    lean_dec_ref_known(v___x_2131_, 1);
                    v___x_2133_ =
                        l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2106_, v_a_2109_);
                    if lean_obj_tag(v___x_2133_) == 0 {
                        v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
                        lean_inc(v_a_2134_);
                        lean_dec_ref_known(v___x_2133_, 1);
                        v_ncRings_2135_ = lean_ctor_get(v_a_2134_, 3);
                        lean_inc_ref(v_ncRings_2135_);
                        lean_dec(v_a_2134_);
                        v___x_2136_ = lean_array_get_size(v_ncRings_2135_);
                        lean_dec_ref(v_ncRings_2135_);
                        v___x_2137_ = lean_box(0);
                        v___x_2138_ = lean_alloc_ctor(0, 14, (0) as u32);
                        lean_ctor_set(v___x_2138_, 0, v___x_2136_);
                        lean_ctor_set(v___x_2138_, 1, v_type_2104_);
                        lean_ctor_set(v___x_2138_, 2, v_a_2113_);
                        lean_ctor_set(v___x_2138_, 3, v_val_2124_);
                        lean_ctor_set(v___x_2138_, 4, v___x_2130_);
                        lean_ctor_set(v___x_2138_, 5, v_a_2132_);
                        lean_ctor_set(v___x_2138_, 6, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 7, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 8, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 9, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 10, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 11, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 12, v___x_2137_);
                        lean_ctor_set(v___x_2138_, 13, v___x_2137_);
                        v___f_2139_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                        lean_closure_set(v___f_2139_, 0, v___x_2138_);
                        v___x_2140_ = l_Lean_Meta_Sym_Arith_arithExt;
                        v___x_2141_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2140_, v___f_2139_, v_a_2106_);
                        if lean_obj_tag(v___x_2141_) == 0 {
                            v_isSharedCheck_2151_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                            if v_isSharedCheck_2151_ == 0 {
                                v_unused_2152_ = lean_ctor_get(v___x_2141_, 0);
                                lean_dec(v_unused_2152_);
                                v___x_2143_ = v___x_2141_;
                                v_isShared_2144_ = v_isSharedCheck_2151_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_2141_);
                                v___x_2143_ = lean_box(0);
                                v_isShared_2144_ = v_isSharedCheck_2151_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2126_);
                            v_a_2153_ = lean_ctor_get(v___x_2141_, 0);
                            v_isSharedCheck_2160_ = (!lean_is_exclusive(v___x_2141_)) as u8;
                            if v_isSharedCheck_2160_ == 0 {
                                v___x_2155_ = v___x_2141_;
                                v_isShared_2156_ = v_isSharedCheck_2160_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2153_);
                                lean_dec(v___x_2141_);
                                v___x_2155_ = lean_box(0);
                                v_isShared_2156_ = v_isSharedCheck_2160_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2132_);
                        lean_dec_ref(v___x_2130_);
                        lean_del_object(v___x_2126_);
                        lean_dec(v_val_2124_);
                        lean_dec(v_a_2113_);
                        lean_dec_ref(v_type_2104_);
                        v_a_2161_ = lean_ctor_get(v___x_2133_, 0);
                        v_isSharedCheck_2168_ = (!lean_is_exclusive(v___x_2133_)) as u8;
                        if v_isSharedCheck_2168_ == 0 {
                            v___x_2163_ = v___x_2133_;
                            v_isShared_2164_ = v_isSharedCheck_2168_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2161_);
                            lean_dec(v___x_2133_);
                            v___x_2163_ = lean_box(0);
                            v_isShared_2164_ = v_isSharedCheck_2168_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_2130_);
                    lean_del_object(v___x_2126_);
                    lean_dec(v_val_2124_);
                    lean_dec(v_a_2113_);
                    lean_dec_ref(v_type_2104_);
                    v_a_2169_ = lean_ctor_get(v___x_2131_, 0);
                    v_isSharedCheck_2176_ = (!lean_is_exclusive(v___x_2131_)) as u8;
                    if v_isSharedCheck_2176_ == 0 {
                        v___x_2171_ = v___x_2131_;
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2169_);
                        lean_dec(v___x_2131_);
                        v___x_2171_ = lean_box(0);
                        v_isShared_2172_ = v_isSharedCheck_2176_;
                        state = 10;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2127_ == 0 {
                    lean_ctor_set(v___x_2126_, 0, v___x_2136_);
                    v___x_2146_ = v___x_2126_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2150_, 0, v___x_2136_);
                    v___x_2146_ = v_reuseFailAlloc_2150_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2144_ == 0 {
                    lean_ctor_set(v___x_2143_, 0, v___x_2146_);
                    v___x_2148_ = v___x_2143_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v___x_2146_);
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
                    v_reuseFailAlloc_2159_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2159_, 0, v_a_2153_);
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
                    v_reuseFailAlloc_2167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2167_, 0, v_a_2161_);
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
                    v_reuseFailAlloc_2175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2175_, 0, v_a_2169_);
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
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v_a_2183_);
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
                    v_reuseFailAlloc_2197_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2197_, 0, v_a_2191_);
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
    mut v_type_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2207_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2205_);
    lean_dec_ref(v_a_2204_);
    lean_dec(v_a_2203_);
    lean_dec_ref(v_a_2202_);
    lean_dec(v_a_2201_);
    lean_dec_ref(v_a_2200_);
    return v_res_2207_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_2208_: *mut LeanObject,
    mut v_x_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
    mut v_x_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2216_: u8 = 0;
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: u8 = 0;
    let mut v___x_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: u8 = 0;
    let mut v___x_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2212_ = lean_ctor_get(v_x_2208_, 0);
                v_vs_2213_ = lean_ctor_get(v_x_2208_, 1);
                v_isSharedCheck_2237_ = (!lean_is_exclusive(v_x_2208_)) as u8;
                if v_isSharedCheck_2237_ == 0 {
                    v___x_2215_ = v_x_2208_;
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2213_);
                    lean_inc(v_ks_2212_);
                    lean_dec(v_x_2208_);
                    v___x_2215_ = lean_box(0);
                    v_isShared_2216_ = v_isSharedCheck_2237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2217_ = lean_array_get_size(v_ks_2212_);
                v___x_2218_ = lean_nat_dec_lt(v_x_2209_, v___x_2217_);
                if v___x_2218_ == 0 {
                    lean_dec(v_x_2209_);
                    v___x_2219_ = lean_array_push(v_ks_2212_, v_x_2210_);
                    v___x_2220_ = lean_array_push(v_vs_2213_, v_x_2211_);
                    if v_isShared_2216_ == 0 {
                        lean_ctor_set(v___x_2215_, 1, v___x_2220_);
                        lean_ctor_set(v___x_2215_, 0, v___x_2219_);
                        v___x_2222_ = v___x_2215_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2223_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2223_, 0, v___x_2219_);
                        lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2220_);
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
                            v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_ks_2212_);
                            lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_vs_2213_);
                            v___x_2227_ = v_reuseFailAlloc_2231_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2232_ = lean_array_fset(v_ks_2212_, v_x_2209_, v_x_2210_);
                        v___x_2233_ = lean_array_fset(v_vs_2213_, v_x_2209_, v_x_2211_);
                        lean_dec(v_x_2209_);
                        if v_isShared_2216_ == 0 {
                            lean_ctor_set(v___x_2215_, 1, v___x_2233_);
                            lean_ctor_set(v___x_2215_, 0, v___x_2232_);
                            v___x_2235_ = v___x_2215_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2232_);
                            lean_ctor_set(v_reuseFailAlloc_2236_, 1, v___x_2233_);
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
                v___x_2228_ = lean_unsigned_to_nat(1);
                v___x_2229_ = lean_nat_add(v_x_2209_, v___x_2228_);
                lean_dec(v_x_2209_);
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
    mut v_n_2238_: *mut LeanObject,
    mut v_k_2239_: *mut LeanObject,
    mut v_v_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    v___x_2241_ = lean_unsigned_to_nat(0);
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
    v___x_2247_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_2248_ = lean_usize_sub(v___x_2247_, v___x_2246_);
    return v___x_2248_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_2249_: *mut LeanObject = core::ptr::null_mut();
    v___x_2249_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(
    mut v_x_2250_: *mut LeanObject,
    mut v_x_2251_: usize,
    mut v_x_2252_: usize,
    mut v_x_2253_: *mut LeanObject,
    mut v_x_2254_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: usize = 0;
    let mut v___x_2257_: usize = 0;
    let mut v___x_2258_: usize = 0;
    let mut v___x_2259_: usize = 0;
    let mut v_j_2260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v___x_2264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v_v_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2279_: u8 = 0;
    let mut v___x_2280_: u8 = 0;
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2286_: u8 = 0;
    let mut v_node_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2290_: u8 = 0;
    let mut v___x_2291_: usize = 0;
    let mut v___x_2292_: usize = 0;
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2297_: u8 = 0;
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2299_: u8 = 0;
    let mut v_unused_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2305_: u8 = 0;
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: u8 = 0;
    let mut v_ks_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: usize = 0;
    let mut v___x_2317_: u8 = 0;
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2320_: u8 = 0;
    let mut v_reuseFailAlloc_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2250_) == 0 {
                    v_es_2255_ = lean_ctor_get(v_x_2250_, 0);
                    v___x_2256_ = 5usize;
                    v___x_2257_ = 1usize;
                    v___x_2258_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2259_ = lean_usize_land(v_x_2251_, v___x_2258_);
                    v_j_2260_ = lean_usize_to_nat(v___x_2259_);
                    v___x_2261_ = lean_array_get_size(v_es_2255_);
                    v___x_2262_ = lean_nat_dec_lt(v_j_2260_, v___x_2261_);
                    if v___x_2262_ == 0 {
                        lean_dec(v_j_2260_);
                        lean_dec(v_x_2254_);
                        lean_dec_ref(v_x_2253_);
                        return v_x_2250_;
                    } else {
                        lean_inc_ref(v_es_2255_);
                        v_isSharedCheck_2299_ = (!lean_is_exclusive(v_x_2250_)) as u8;
                        if v_isSharedCheck_2299_ == 0 {
                            v_unused_2300_ = lean_ctor_get(v_x_2250_, 0);
                            lean_dec(v_unused_2300_);
                            v___x_2264_ = v_x_2250_;
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2250_);
                            v___x_2264_ = lean_box(0);
                            v_isShared_2265_ = v_isSharedCheck_2299_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2301_ = lean_ctor_get(v_x_2250_, 0);
                    v_vs_2302_ = lean_ctor_get(v_x_2250_, 1);
                    v_isSharedCheck_2322_ = (!lean_is_exclusive(v_x_2250_)) as u8;
                    if v_isSharedCheck_2322_ == 0 {
                        v___x_2304_ = v_x_2250_;
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2302_);
                        lean_inc(v_ks_2301_);
                        lean_dec(v_x_2250_);
                        v___x_2304_ = lean_box(0);
                        v_isShared_2305_ = v_isSharedCheck_2322_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2266_ = lean_array_fget(v_es_2255_, v_j_2260_);
                v___x_2267_ = lean_box(0);
                v_xs_x27_2268_ = lean_array_fset(v_es_2255_, v_j_2260_, v___x_2267_);
                match lean_obj_tag(v_v_2266_) {
                    0 => {
                        v_key_2275_ = lean_ctor_get(v_v_2266_, 0);
                        v_val_2276_ = lean_ctor_get(v_v_2266_, 1);
                        v_isSharedCheck_2286_ = (!lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2286_ == 0 {
                            v___x_2278_ = v_v_2266_;
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2276_);
                            lean_inc(v_key_2275_);
                            lean_dec(v_v_2266_);
                            v___x_2278_ = lean_box(0);
                            v_isShared_2279_ = v_isSharedCheck_2286_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2287_ = lean_ctor_get(v_v_2266_, 0);
                        v_isSharedCheck_2297_ = (!lean_is_exclusive(v_v_2266_)) as u8;
                        if v_isSharedCheck_2297_ == 0 {
                            v___x_2289_ = v_v_2266_;
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2287_);
                            lean_dec(v_v_2266_);
                            v___x_2289_ = lean_box(0);
                            v_isShared_2290_ = v_isSharedCheck_2297_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2298_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2298_, 0, v_x_2253_);
                        lean_ctor_set(v___x_2298_, 1, v_x_2254_);
                        v___y_2270_ = v___x_2298_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2271_ = lean_array_fset(v_xs_x27_2268_, v_j_2260_, v___y_2270_);
                lean_dec(v_j_2260_);
                if v_isShared_2265_ == 0 {
                    lean_ctor_set(v___x_2264_, 0, v___x_2271_);
                    v___x_2273_ = v___x_2264_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
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
                    lean_del_object(v___x_2278_);
                    v___x_2281_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2275_,
                        v_val_2276_,
                        v_x_2253_,
                        v_x_2254_,
                    );
                    v___x_2282_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2282_, 0, v___x_2281_);
                    v___y_2270_ = v___x_2282_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2276_);
                    lean_dec(v_key_2275_);
                    if v_isShared_2279_ == 0 {
                        lean_ctor_set(v___x_2278_, 1, v_x_2254_);
                        lean_ctor_set(v___x_2278_, 0, v_x_2253_);
                        v___x_2284_ = v___x_2278_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_x_2253_);
                        lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_x_2254_);
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
                    lean_ctor_set(v___x_2289_, 0, v___x_2293_);
                    v___x_2295_ = v___x_2289_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2296_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2296_, 0, v___x_2293_);
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
                    v_reuseFailAlloc_2321_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 0, v_ks_2301_);
                    lean_ctor_set(v_reuseFailAlloc_2321_, 1, v_vs_2302_);
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
                    v___x_2319_ = lean_unsigned_to_nat(4);
                    v___x_2320_ = lean_nat_dec_lt(v___x_2318_, v___x_2319_);
                    lean_dec(v___x_2318_);
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
                    v_ks_2311_ = lean_ctor_get(v_newNode_2308_, 0);
                    lean_inc_ref(v_ks_2311_);
                    v_vs_2312_ = lean_ctor_get(v_newNode_2308_, 1);
                    lean_inc_ref(v_vs_2312_);
                    lean_dec_ref(v_newNode_2308_);
                    v___x_2313_ = lean_unsigned_to_nat(0);
                    v___x_2314_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_2315_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_x_2252_, v_ks_2311_, v_vs_2312_, v___x_2313_, v___x_2314_);
                    lean_dec_ref(v_vs_2312_);
                    lean_dec_ref(v_ks_2311_);
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
    mut v_keys_2324_: *mut LeanObject,
    mut v_vals_2325_: *mut LeanObject,
    mut v_i_2326_: *mut LeanObject,
    mut v_entries_2327_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: u8 = 0;
    let mut v_k_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: u64 = 0;
    let mut v_h_2333_: usize = 0;
    let mut v___x_2334_: usize = 0;
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: usize = 0;
    let mut v___x_2337_: usize = 0;
    let mut v___x_2338_: usize = 0;
    let mut v_h_2339_: usize = 0;
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2328_ = lean_array_get_size(v_keys_2324_);
                v___x_2329_ = lean_nat_dec_lt(v_i_2326_, v___x_2328_);
                if v___x_2329_ == 0 {
                    lean_dec(v_i_2326_);
                    return v_entries_2327_;
                } else {
                    v_k_2330_ = lean_array_fget_borrowed(v_keys_2324_, v_i_2326_);
                    v_v_2331_ = lean_array_fget_borrowed(v_vals_2325_, v_i_2326_);
                    v___x_2332_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2330_);
                    v_h_2333_ = lean_uint64_to_usize(v___x_2332_);
                    v___x_2334_ = 5usize;
                    v___x_2335_ = lean_unsigned_to_nat(1);
                    v___x_2336_ = 1usize;
                    v___x_2337_ = lean_usize_sub(v_depth_2323_, v___x_2336_);
                    v___x_2338_ = lean_usize_mul(v___x_2334_, v___x_2337_);
                    v_h_2339_ = lean_usize_shift_right(v_h_2333_, v___x_2338_);
                    v___x_2340_ = lean_nat_add(v_i_2326_, v___x_2335_);
                    lean_dec(v_i_2326_);
                    lean_inc(v_v_2331_);
                    lean_inc(v_k_2330_);
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
    mut v_depth_2343_: *mut LeanObject,
    mut v_keys_2344_: *mut LeanObject,
    mut v_vals_2345_: *mut LeanObject,
    mut v_i_2346_: *mut LeanObject,
    mut v_entries_2347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2348_: usize = 0;
    let mut v_res_2349_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2348_ = lean_unbox_usize(v_depth_2343_);
    lean_dec(v_depth_2343_);
    v_res_2349_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_2348_, v_keys_2344_, v_vals_2345_, v_i_2346_, v_entries_2347_);
    lean_dec_ref(v_vals_2345_);
    lean_dec_ref(v_keys_2344_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_2350_: *mut LeanObject,
    mut v_x_2351_: *mut LeanObject,
    mut v_x_2352_: *mut LeanObject,
    mut v_x_2353_: *mut LeanObject,
    mut v_x_2354_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2086__boxed_2355_: usize = 0;
    let mut v_x_2087__boxed_2356_: usize = 0;
    let mut v_res_2357_: *mut LeanObject = core::ptr::null_mut();
    v_x_2086__boxed_2355_ = lean_unbox_usize(v_x_2351_);
    lean_dec(v_x_2351_);
    v_x_2087__boxed_2356_ = lean_unbox_usize(v_x_2352_);
    lean_dec(v_x_2352_);
    v_res_2357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2350_, v_x_2086__boxed_2355_, v_x_2087__boxed_2356_, v_x_2353_, v_x_2354_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(
    mut v_x_2358_: *mut LeanObject,
    mut v_x_2359_: *mut LeanObject,
    mut v_x_2360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2361_: u64 = 0;
    let mut v___x_2362_: usize = 0;
    let mut v___x_2363_: usize = 0;
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    v___x_2361_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2359_);
    v___x_2362_ = lean_uint64_to_usize(v___x_2361_);
    v___x_2363_ = 1usize;
    v___x_2364_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2358_, v___x_2362_, v___x_2363_, v_x_2359_, v_x_2360_);
    return v___x_2364_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0(
    mut v_type_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v_s_2367_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2376_: u8 = 0;
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2368_ = lean_ctor_get(v_s_2367_, 0);
                v_rings_2369_ = lean_ctor_get(v_s_2367_, 1);
                v_semirings_2370_ = lean_ctor_get(v_s_2367_, 2);
                v_ncRings_2371_ = lean_ctor_get(v_s_2367_, 3);
                v_ncSemirings_2372_ = lean_ctor_get(v_s_2367_, 4);
                v_typeClassify_2373_ = lean_ctor_get(v_s_2367_, 5);
                v_isSharedCheck_2381_ = (!lean_is_exclusive(v_s_2367_)) as u8;
                if v_isSharedCheck_2381_ == 0 {
                    v___x_2375_ = v_s_2367_;
                    v_isShared_2376_ = v_isSharedCheck_2381_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_2373_);
                    lean_inc(v_ncSemirings_2372_);
                    lean_inc(v_ncRings_2371_);
                    lean_inc(v_semirings_2370_);
                    lean_inc(v_rings_2369_);
                    lean_inc(v_exp_2368_);
                    lean_dec(v_s_2367_);
                    v___x_2375_ = lean_box(0);
                    v_isShared_2376_ = v_isSharedCheck_2381_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2377_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_2373_, v_type_2365_, v___y_2366_);
                if v_isShared_2376_ == 0 {
                    lean_ctor_set(v___x_2375_, 5, v___x_2377_);
                    v___x_2379_ = v___x_2375_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_exp_2368_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_rings_2369_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 2, v_semirings_2370_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 3, v_ncRings_2371_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 4, v_ncSemirings_2372_);
                    lean_ctor_set(v_reuseFailAlloc_2380_, 5, v___x_2377_);
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
    mut v_keys_2382_: *mut LeanObject,
    mut v_vals_2383_: *mut LeanObject,
    mut v_i_2384_: *mut LeanObject,
    mut v_k_2385_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: u8 = 0;
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: u8 = 0;
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2386_ = lean_array_get_size(v_keys_2382_);
                v___x_2387_ = lean_nat_dec_lt(v_i_2384_, v___x_2386_);
                if v___x_2387_ == 0 {
                    lean_dec(v_i_2384_);
                    v___x_2388_ = lean_box(0);
                    return v___x_2388_;
                } else {
                    v_k_x27_2389_ = lean_array_fget_borrowed(v_keys_2382_, v_i_2384_);
                    v___x_2390_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2385_,
                            v_k_x27_2389_,
                        );
                    if v___x_2390_ == 0 {
                        v___x_2391_ = lean_unsigned_to_nat(1);
                        v___x_2392_ = lean_nat_add(v_i_2384_, v___x_2391_);
                        lean_dec(v_i_2384_);
                        v_i_2384_ = v___x_2392_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2394_ = lean_array_fget_borrowed(v_vals_2383_, v_i_2384_);
                        lean_dec(v_i_2384_);
                        lean_inc(v___x_2394_);
                        v___x_2395_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2395_, 0, v___x_2394_);
                        return v___x_2395_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2396_: *mut LeanObject,
    mut v_vals_2397_: *mut LeanObject,
    mut v_i_2398_: *mut LeanObject,
    mut v_k_2399_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2400_: *mut LeanObject = core::ptr::null_mut();
    v_res_2400_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2396_, v_vals_2397_, v_i_2398_, v_k_2399_);
    lean_dec_ref(v_k_2399_);
    lean_dec_ref(v_vals_2397_);
    lean_dec_ref(v_keys_2396_);
    return v_res_2400_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(
    mut v_x_2401_: *mut LeanObject,
    mut v_x_2402_: usize,
    mut v_x_2403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: usize = 0;
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v_j_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: u8 = 0;
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: usize = 0;
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2401_) == 0 {
                    v_es_2404_ = lean_ctor_get(v_x_2401_, 0);
                    v___x_2405_ = lean_box(2);
                    v___x_2406_ = 5usize;
                    v___x_2407_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_2408_ = lean_usize_land(v_x_2402_, v___x_2407_);
                    v_j_2409_ = lean_usize_to_nat(v___x_2408_);
                    v___x_2410_ = lean_array_get_borrowed(v___x_2405_, v_es_2404_, v_j_2409_);
                    lean_dec(v_j_2409_);
                    match lean_obj_tag(v___x_2410_) {
                        0 => {
                            v_key_2411_ = lean_ctor_get(v___x_2410_, 0);
                            v_val_2412_ = lean_ctor_get(v___x_2410_, 1);
                            v___x_2413_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2403_, v_key_2411_);
                            if v___x_2413_ == 0 {
                                v___x_2414_ = lean_box(0);
                                return v___x_2414_;
                            } else {
                                lean_inc(v_val_2412_);
                                v___x_2415_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2415_, 0, v_val_2412_);
                                return v___x_2415_;
                            }
                        }
                        1 => {
                            v_node_2416_ = lean_ctor_get(v___x_2410_, 0);
                            v___x_2417_ = lean_usize_shift_right(v_x_2402_, v___x_2406_);
                            v_x_2401_ = v_node_2416_;
                            v_x_2402_ = v___x_2417_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2419_ = lean_box(0);
                            return v___x_2419_;
                        }
                    }
                } else {
                    v_ks_2420_ = lean_ctor_get(v_x_2401_, 0);
                    v_vs_2421_ = lean_ctor_get(v_x_2401_, 1);
                    v___x_2422_ = lean_unsigned_to_nat(0);
                    v___x_2423_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2420_, v_vs_2421_, v___x_2422_, v_x_2403_);
                    return v___x_2423_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2424_: *mut LeanObject,
    mut v_x_2425_: *mut LeanObject,
    mut v_x_2426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2304__boxed_2427_: usize = 0;
    let mut v_res_2428_: *mut LeanObject = core::ptr::null_mut();
    v_x_2304__boxed_2427_ = lean_unbox_usize(v_x_2425_);
    lean_dec(v_x_2425_);
    v_res_2428_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2424_, v_x_2304__boxed_2427_, v_x_2426_);
    lean_dec_ref(v_x_2426_);
    lean_dec_ref(v_x_2424_);
    return v_res_2428_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(
    mut v_x_2429_: *mut LeanObject,
    mut v_x_2430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2431_: u64 = 0;
    let mut v___x_2432_: usize = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    v___x_2431_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2430_);
    v___x_2432_ = lean_uint64_to_usize(v___x_2431_);
    v___x_2433_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2429_, v___x_2432_, v_x_2430_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg___boxed(
    mut v_x_2434_: *mut LeanObject,
    mut v_x_2435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2436_: *mut LeanObject = core::ptr::null_mut();
    v_res_2436_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_2434_, v_x_2435_);
    lean_dec_ref(v_x_2435_);
    lean_dec_ref(v_x_2434_);
    return v_res_2436_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(
    mut v_type_2437_: *mut LeanObject,
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2449_: u8 = 0;
    let mut v_typeClassify_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2455_: u8 = 0;
    let mut v_id_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2472_: u8 = 0;
    let mut v___y_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2480_: u8 = 0;
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2484_: u8 = 0;
    let mut v_unused_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2489_: u8 = 0;
    let mut v___x_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2493_: u8 = 0;
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2499_: u8 = 0;
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut v_a_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2504_: u8 = 0;
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2508_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2445_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2439_, v_a_2442_);
                if lean_obj_tag(v___x_2445_) == 0 {
                    v_a_2446_ = lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2500_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2500_ == 0 {
                        v___x_2448_ = v___x_2445_;
                        v_isShared_2449_ = v_isSharedCheck_2500_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2446_);
                        lean_dec(v___x_2445_);
                        v___x_2448_ = lean_box(0);
                        v_isShared_2449_ = v_isSharedCheck_2500_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2437_);
                    v_a_2501_ = lean_ctor_get(v___x_2445_, 0);
                    v_isSharedCheck_2508_ = (!lean_is_exclusive(v___x_2445_)) as u8;
                    if v_isSharedCheck_2508_ == 0 {
                        v___x_2503_ = v___x_2445_;
                        v_isShared_2504_ = v_isSharedCheck_2508_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2501_);
                        lean_dec(v___x_2445_);
                        v___x_2503_ = lean_box(0);
                        v_isShared_2504_ = v_isSharedCheck_2508_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                v_typeClassify_2450_ = lean_ctor_get(v_a_2446_, 5);
                lean_inc_ref(v_typeClassify_2450_);
                lean_dec(v_a_2446_);
                v___x_2451_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_2450_, v_type_2437_);
                lean_dec_ref(v_typeClassify_2450_);
                if lean_obj_tag(v___x_2451_) == 1 {
                    lean_dec_ref(v_type_2437_);
                    v_val_2452_ = lean_ctor_get(v___x_2451_, 0);
                    v_isSharedCheck_2467_ = (!lean_is_exclusive(v___x_2451_)) as u8;
                    if v_isSharedCheck_2467_ == 0 {
                        v___x_2454_ = v___x_2451_;
                        v_isShared_2455_ = v_isSharedCheck_2467_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2452_);
                        lean_dec(v___x_2451_);
                        v___x_2454_ = lean_box(0);
                        v_isShared_2455_ = v_isSharedCheck_2467_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2451_);
                    lean_del_object(v___x_2448_);
                    lean_inc_ref(v_type_2437_);
                    v___x_2468_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommRing_x3f(v_type_2437_, v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
                    if lean_obj_tag(v___x_2468_) == 0 {
                        v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
                        v_isSharedCheck_2499_ = (!lean_is_exclusive(v___x_2468_)) as u8;
                        if v_isSharedCheck_2499_ == 0 {
                            v___x_2471_ = v___x_2468_;
                            v_isShared_2472_ = v_isSharedCheck_2499_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2469_);
                            lean_dec(v___x_2468_);
                            v___x_2471_ = lean_box(0);
                            v_isShared_2472_ = v_isSharedCheck_2499_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_2437_);
                        return v___x_2468_;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_val_2452_) == 0 {
                    v_id_2456_ = lean_ctor_get(v_val_2452_, 0);
                    lean_inc(v_id_2456_);
                    lean_dec_ref_known(v_val_2452_, 1);
                    if v_isShared_2455_ == 0 {
                        lean_ctor_set(v___x_2454_, 0, v_id_2456_);
                        v___x_2458_ = v___x_2454_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2462_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2462_, 0, v_id_2456_);
                        v___x_2458_ = v_reuseFailAlloc_2462_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2454_);
                    lean_dec(v_val_2452_);
                    v___x_2463_ = lean_box(0);
                    if v_isShared_2449_ == 0 {
                        lean_ctor_set(v___x_2448_, 0, v___x_2463_);
                        v___x_2465_ = v___x_2448_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2463_);
                        v___x_2465_ = v_reuseFailAlloc_2466_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2449_ == 0 {
                    lean_ctor_set(v___x_2448_, 0, v___x_2458_);
                    v___x_2460_ = v___x_2448_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2461_, 0, v___x_2458_);
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
                if lean_obj_tag(v_a_2469_) == 0 {
                    lean_del_object(v___x_2471_);
                    v___x_2494_ = lean_box(4);
                    v___y_2474_ = v___x_2494_;
                    state = 7;
                    continue;
                } else {
                    v_val_2495_ = lean_ctor_get(v_a_2469_, 0);
                    lean_inc(v_val_2495_);
                    if v_isShared_2472_ == 0 {
                        lean_ctor_set(v___x_2471_, 0, v_val_2495_);
                        v___x_2497_ = v___x_2471_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2498_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2498_, 0, v_val_2495_);
                        v___x_2497_ = v_reuseFailAlloc_2498_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                v___f_2475_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f___lam__0 as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_2475_, 0, v_type_2437_);
                lean_closure_set(v___f_2475_, 1, v___y_2474_);
                v___x_2476_ = l_Lean_Meta_Sym_Arith_arithExt;
                v___x_2477_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2476_, v___f_2475_, v_a_2439_);
                if lean_obj_tag(v___x_2477_) == 0 {
                    v_isSharedCheck_2484_ = (!lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2484_ == 0 {
                        v_unused_2485_ = lean_ctor_get(v___x_2477_, 0);
                        lean_dec(v_unused_2485_);
                        v___x_2479_ = v___x_2477_;
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___x_2477_);
                        v___x_2479_ = lean_box(0);
                        v_isShared_2480_ = v_isSharedCheck_2484_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2469_);
                    v_a_2486_ = lean_ctor_get(v___x_2477_, 0);
                    v_isSharedCheck_2493_ = (!lean_is_exclusive(v___x_2477_)) as u8;
                    if v_isSharedCheck_2493_ == 0 {
                        v___x_2488_ = v___x_2477_;
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2486_);
                        lean_dec(v___x_2477_);
                        v___x_2488_ = lean_box(0);
                        v_isShared_2489_ = v_isSharedCheck_2493_;
                        state = 10;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_2480_ == 0 {
                    lean_ctor_set(v___x_2479_, 0, v_a_2469_);
                    v___x_2482_ = v___x_2479_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2483_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2469_);
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
                    v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
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
                    v_reuseFailAlloc_2507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2507_, 0, v_a_2501_);
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
    mut v_type_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
    mut v_a_2513_: *mut LeanObject,
    mut v_a_2514_: *mut LeanObject,
    mut v_a_2515_: *mut LeanObject,
    mut v_a_2516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2517_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2515_);
    lean_dec_ref(v_a_2514_);
    lean_dec(v_a_2513_);
    lean_dec_ref(v_a_2512_);
    lean_dec(v_a_2511_);
    lean_dec_ref(v_a_2510_);
    return v_res_2517_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(
    mut v_00_u03b2_2518_: *mut LeanObject,
    mut v_x_2519_: *mut LeanObject,
    mut v_x_2520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2521_: *mut LeanObject = core::ptr::null_mut();
    v___x_2521_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_x_2519_, v_x_2520_);
    return v___x_2521_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___boxed(
    mut v_00_u03b2_2522_: *mut LeanObject,
    mut v_x_2523_: *mut LeanObject,
    mut v_x_2524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2525_: *mut LeanObject = core::ptr::null_mut();
    v_res_2525_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0(v_00_u03b2_2522_, v_x_2523_, v_x_2524_);
    lean_dec_ref(v_x_2524_);
    lean_dec_ref(v_x_2523_);
    return v_res_2525_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1(
    mut v_00_u03b2_2526_: *mut LeanObject,
    mut v_x_2527_: *mut LeanObject,
    mut v_x_2528_: *mut LeanObject,
    mut v_x_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    v___x_2530_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_x_2527_, v_x_2528_, v_x_2529_);
    return v___x_2530_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(
    mut v_00_u03b2_2531_: *mut LeanObject,
    mut v_x_2532_: *mut LeanObject,
    mut v_x_2533_: usize,
    mut v_x_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    v___x_2535_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___redArg(v_x_2532_, v_x_2533_, v_x_2534_);
    return v___x_2535_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2536_: *mut LeanObject,
    mut v_x_2537_: *mut LeanObject,
    mut v_x_2538_: *mut LeanObject,
    mut v_x_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2512__boxed_2540_: usize = 0;
    let mut v_res_2541_: *mut LeanObject = core::ptr::null_mut();
    v_x_2512__boxed_2540_ = lean_unbox_usize(v_x_2538_);
    lean_dec(v_x_2538_);
    v_res_2541_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0(v_00_u03b2_2536_, v_x_2537_, v_x_2512__boxed_2540_, v_x_2539_);
    lean_dec_ref(v_x_2539_);
    lean_dec_ref(v_x_2537_);
    return v_res_2541_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(
    mut v_00_u03b2_2542_: *mut LeanObject,
    mut v_x_2543_: *mut LeanObject,
    mut v_x_2544_: usize,
    mut v_x_2545_: usize,
    mut v_x_2546_: *mut LeanObject,
    mut v_x_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
    v___x_2548_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___redArg(v_x_2543_, v_x_2544_, v_x_2545_, v_x_2546_, v_x_2547_);
    return v___x_2548_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_2549_: *mut LeanObject,
    mut v_x_2550_: *mut LeanObject,
    mut v_x_2551_: *mut LeanObject,
    mut v_x_2552_: *mut LeanObject,
    mut v_x_2553_: *mut LeanObject,
    mut v_x_2554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_2523__boxed_2555_: usize = 0;
    let mut v_x_2524__boxed_2556_: usize = 0;
    let mut v_res_2557_: *mut LeanObject = core::ptr::null_mut();
    v_x_2523__boxed_2555_ = lean_unbox_usize(v_x_2551_);
    lean_dec(v_x_2551_);
    v_x_2524__boxed_2556_ = lean_unbox_usize(v_x_2552_);
    lean_dec(v_x_2552_);
    v_res_2557_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2(v_00_u03b2_2549_, v_x_2550_, v_x_2523__boxed_2555_, v_x_2524__boxed_2556_, v_x_2553_, v_x_2554_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2558_: *mut LeanObject,
    mut v_keys_2559_: *mut LeanObject,
    mut v_vals_2560_: *mut LeanObject,
    mut v_heq_2561_: *mut LeanObject,
    mut v_i_2562_: *mut LeanObject,
    mut v_k_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    v___x_2564_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2559_, v_vals_2560_, v_i_2562_, v_k_2563_);
    return v___x_2564_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2565_: *mut LeanObject,
    mut v_keys_2566_: *mut LeanObject,
    mut v_vals_2567_: *mut LeanObject,
    mut v_heq_2568_: *mut LeanObject,
    mut v_i_2569_: *mut LeanObject,
    mut v_k_2570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2571_: *mut LeanObject = core::ptr::null_mut();
    v_res_2571_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2565_, v_keys_2566_, v_vals_2567_, v_heq_2568_, v_i_2569_, v_k_2570_);
    lean_dec_ref(v_k_2570_);
    lean_dec_ref(v_vals_2567_);
    lean_dec_ref(v_keys_2566_);
    return v_res_2571_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_2572_: *mut LeanObject,
    mut v_n_2573_: *mut LeanObject,
    mut v_k_2574_: *mut LeanObject,
    mut v_v_2575_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    v___x_2576_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4___redArg(v_n_2573_, v_k_2574_, v_v_2575_);
    return v___x_2576_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_2577_: *mut LeanObject,
    mut v_depth_2578_: usize,
    mut v_keys_2579_: *mut LeanObject,
    mut v_vals_2580_: *mut LeanObject,
    mut v_heq_2581_: *mut LeanObject,
    mut v_i_2582_: *mut LeanObject,
    mut v_entries_2583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    v___x_2584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___redArg(v_depth_2578_, v_keys_2579_, v_vals_2580_, v_i_2582_, v_entries_2583_);
    return v___x_2584_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_2585_: *mut LeanObject,
    mut v_depth_2586_: *mut LeanObject,
    mut v_keys_2587_: *mut LeanObject,
    mut v_vals_2588_: *mut LeanObject,
    mut v_heq_2589_: *mut LeanObject,
    mut v_i_2590_: *mut LeanObject,
    mut v_entries_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2592_: usize = 0;
    let mut v_res_2593_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2592_ = lean_unbox_usize(v_depth_2586_);
    lean_dec(v_depth_2586_);
    v_res_2593_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__5(v_00_u03b2_2585_, v_depth_boxed_2592_, v_keys_2587_, v_vals_2588_, v_heq_2589_, v_i_2590_, v_entries_2591_);
    lean_dec_ref(v_vals_2588_);
    lean_dec_ref(v_keys_2587_);
    return v_res_2593_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_2594_: *mut LeanObject,
    mut v_x_2595_: *mut LeanObject,
    mut v_x_2596_: *mut LeanObject,
    mut v_x_2597_: *mut LeanObject,
    mut v_x_2598_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2599_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2595_, v_x_2596_, v_x_2597_, v_x_2598_);
    return v___x_2599_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0(
    mut v___x_2600_: *mut LeanObject,
    mut v_s_2601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2615_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2602_ = lean_ctor_get(v_s_2601_, 0);
                v_rings_2603_ = lean_ctor_get(v_s_2601_, 1);
                v_semirings_2604_ = lean_ctor_get(v_s_2601_, 2);
                v_ncRings_2605_ = lean_ctor_get(v_s_2601_, 3);
                v_ncSemirings_2606_ = lean_ctor_get(v_s_2601_, 4);
                v_typeClassify_2607_ = lean_ctor_get(v_s_2601_, 5);
                v_isSharedCheck_2615_ = (!lean_is_exclusive(v_s_2601_)) as u8;
                if v_isSharedCheck_2615_ == 0 {
                    v___x_2609_ = v_s_2601_;
                    v_isShared_2610_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_2607_);
                    lean_inc(v_ncSemirings_2606_);
                    lean_inc(v_ncRings_2605_);
                    lean_inc(v_semirings_2604_);
                    lean_inc(v_rings_2603_);
                    lean_inc(v_exp_2602_);
                    lean_dec(v_s_2601_);
                    v___x_2609_ = lean_box(0);
                    v_isShared_2610_ = v_isSharedCheck_2615_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2611_ = lean_array_push(v_semirings_2604_, v___x_2600_);
                if v_isShared_2610_ == 0 {
                    lean_ctor_set(v___x_2609_, 2, v___x_2611_);
                    v___x_2613_ = v___x_2609_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_exp_2602_);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 1, v_rings_2603_);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 2, v___x_2611_);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 3, v_ncRings_2605_);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 4, v_ncSemirings_2606_);
                    lean_ctor_set(v_reuseFailAlloc_2614_, 5, v_typeClassify_2607_);
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
    mut v_val_2616_: *mut LeanObject,
    mut v___x_2617_: *mut LeanObject,
    mut v_s_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: u8 = 0;
    let mut v___x_2628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2629_: u8 = 0;
    let mut v_v_2630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRing_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_invFn_x3f_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commSemiringInst_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_commRingInst_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_noZeroDivInst_x3f_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fieldInst_x3f_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2639_: u8 = 0;
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_unused_2651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2652_: u8 = 0;
    let mut v_unused_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2619_ = lean_ctor_get(v_s_2618_, 0);
                v_rings_2620_ = lean_ctor_get(v_s_2618_, 1);
                v_semirings_2621_ = lean_ctor_get(v_s_2618_, 2);
                v_ncRings_2622_ = lean_ctor_get(v_s_2618_, 3);
                v_ncSemirings_2623_ = lean_ctor_get(v_s_2618_, 4);
                v_typeClassify_2624_ = lean_ctor_get(v_s_2618_, 5);
                v___x_2625_ = lean_array_get_size(v_rings_2620_);
                v___x_2626_ = lean_nat_dec_lt(v_val_2616_, v___x_2625_);
                if v___x_2626_ == 0 {
                    lean_dec(v___x_2617_);
                    return v_s_2618_;
                } else {
                    lean_inc_ref(v_typeClassify_2624_);
                    lean_inc_ref(v_ncSemirings_2623_);
                    lean_inc_ref(v_ncRings_2622_);
                    lean_inc_ref(v_semirings_2621_);
                    lean_inc_ref(v_rings_2620_);
                    lean_inc(v_exp_2619_);
                    v_isSharedCheck_2652_ = (!lean_is_exclusive(v_s_2618_)) as u8;
                    if v_isSharedCheck_2652_ == 0 {
                        v_unused_2653_ = lean_ctor_get(v_s_2618_, 5);
                        lean_dec(v_unused_2653_);
                        v_unused_2654_ = lean_ctor_get(v_s_2618_, 4);
                        lean_dec(v_unused_2654_);
                        v_unused_2655_ = lean_ctor_get(v_s_2618_, 3);
                        lean_dec(v_unused_2655_);
                        v_unused_2656_ = lean_ctor_get(v_s_2618_, 2);
                        lean_dec(v_unused_2656_);
                        v_unused_2657_ = lean_ctor_get(v_s_2618_, 1);
                        lean_dec(v_unused_2657_);
                        v_unused_2658_ = lean_ctor_get(v_s_2618_, 0);
                        lean_dec(v_unused_2658_);
                        v___x_2628_ = v_s_2618_;
                        v_isShared_2629_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2618_);
                        v___x_2628_ = lean_box(0);
                        v_isShared_2629_ = v_isSharedCheck_2652_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2630_ = lean_array_fget(v_rings_2620_, v_val_2616_);
                v_toRing_2631_ = lean_ctor_get(v_v_2630_, 0);
                v_invFn_x3f_2632_ = lean_ctor_get(v_v_2630_, 1);
                v_commSemiringInst_2633_ = lean_ctor_get(v_v_2630_, 3);
                v_commRingInst_2634_ = lean_ctor_get(v_v_2630_, 4);
                v_noZeroDivInst_x3f_2635_ = lean_ctor_get(v_v_2630_, 5);
                v_fieldInst_x3f_2636_ = lean_ctor_get(v_v_2630_, 6);
                v_isSharedCheck_2650_ = (!lean_is_exclusive(v_v_2630_)) as u8;
                if v_isSharedCheck_2650_ == 0 {
                    v_unused_2651_ = lean_ctor_get(v_v_2630_, 2);
                    lean_dec(v_unused_2651_);
                    v___x_2638_ = v_v_2630_;
                    v_isShared_2639_ = v_isSharedCheck_2650_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_fieldInst_x3f_2636_);
                    lean_inc(v_noZeroDivInst_x3f_2635_);
                    lean_inc(v_commRingInst_2634_);
                    lean_inc(v_commSemiringInst_2633_);
                    lean_inc(v_invFn_x3f_2632_);
                    lean_inc(v_toRing_2631_);
                    lean_dec(v_v_2630_);
                    v___x_2638_ = lean_box(0);
                    v_isShared_2639_ = v_isSharedCheck_2650_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2640_ = lean_box(0);
                v_xs_x27_2641_ = lean_array_fset(v_rings_2620_, v_val_2616_, v___x_2640_);
                v___x_2642_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2642_, 0, v___x_2617_);
                if v_isShared_2639_ == 0 {
                    lean_ctor_set(v___x_2638_, 2, v___x_2642_);
                    v___x_2644_ = v___x_2638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 7, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_toRing_2631_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_invFn_x3f_2632_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 2, v___x_2642_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 3, v_commSemiringInst_2633_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 4, v_commRingInst_2634_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 5, v_noZeroDivInst_x3f_2635_);
                    lean_ctor_set(v_reuseFailAlloc_2649_, 6, v_fieldInst_x3f_2636_);
                    v___x_2644_ = v_reuseFailAlloc_2649_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2645_ = lean_array_fset(v_xs_x27_2641_, v_val_2616_, v___x_2644_);
                if v_isShared_2629_ == 0 {
                    lean_ctor_set(v___x_2628_, 1, v___x_2645_);
                    v___x_2647_ = v___x_2628_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_exp_2619_);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 1, v___x_2645_);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 2, v_semirings_2621_);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 3, v_ncRings_2622_);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 4, v_ncSemirings_2623_);
                    lean_ctor_set(v_reuseFailAlloc_2648_, 5, v_typeClassify_2624_);
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
    mut v_val_2659_: *mut LeanObject,
    mut v___x_2660_: *mut LeanObject,
    mut v_s_2661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2662_: *mut LeanObject = core::ptr::null_mut();
    v_res_2662_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1(v_val_2659_, v___x_2660_, v_s_2661_);
    lean_dec(v_val_2659_);
    return v_res_2662_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7()
-> *mut LeanObject {
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut LeanObject = core::ptr::null_mut();
    v___x_2682_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__6;
    v___x_2683_ = l_Lean_stringToMessageData(v___x_2682_);
    return v___x_2683_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(
    mut v_type_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
    mut v_a_2686_: *mut LeanObject,
    mut v_a_2687_: *mut LeanObject,
    mut v_a_2688_: *mut LeanObject,
    mut v_a_2689_: *mut LeanObject,
    mut v_a_2690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2706_: u8 = 0;
    let mut v_val_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2723_: u8 = 0;
    let mut v___x_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2738_: u8 = 0;
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2745_: u8 = 0;
    let mut v_unused_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2750_: u8 = 0;
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2754_: u8 = 0;
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2766_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2770_: u8 = 0;
    let mut v_isSharedCheck_2771_: u8 = 0;
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: u8 = 0;
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2782_: u8 = 0;
    let mut v___x_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2786_: u8 = 0;
    let mut v_a_2787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2794_: u8 = 0;
    let mut v_a_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2798_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2802_: u8 = 0;
    let mut v_a_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2806_: u8 = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2815_: u8 = 0;
    let mut v_a_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2819_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2823_: u8 = 0;
    let mut v_a_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2827_: u8 = 0;
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2684_);
                v___x_2695_ = l_Lean_Meta_getDecLevel(
                    v_type_2684_,
                    v_a_2687_,
                    v_a_2688_,
                    v_a_2689_,
                    v_a_2690_,
                );
                if lean_obj_tag(v___x_2695_) == 0 {
                    v_a_2696_ = lean_ctor_get(v___x_2695_, 0);
                    lean_inc_n(v_a_2696_, 2);
                    lean_dec_ref_known(v___x_2695_, 1);
                    v___x_2697_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__1;
                    v___x_2698_ = lean_box(0);
                    v___x_2699_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2699_, 0, v_a_2696_);
                    lean_ctor_set(v___x_2699_, 1, v___x_2698_);
                    lean_inc_ref(v___x_2699_);
                    v___x_2700_ = l_Lean_mkConst(v___x_2697_, v___x_2699_);
                    lean_inc_ref(v_type_2684_);
                    v___x_2701_ = l_Lean_Expr_app___override(v___x_2700_, v_type_2684_);
                    v___x_2702_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2701_,
                        v_a_2687_,
                        v_a_2688_,
                        v_a_2689_,
                        v_a_2690_,
                    );
                    if lean_obj_tag(v___x_2702_) == 0 {
                        v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
                        v_isSharedCheck_2815_ = (!lean_is_exclusive(v___x_2702_)) as u8;
                        if v_isSharedCheck_2815_ == 0 {
                            v___x_2705_ = v___x_2702_;
                            v_isShared_2706_ = v_isSharedCheck_2815_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2703_);
                            lean_dec(v___x_2702_);
                            v___x_2705_ = lean_box(0);
                            v_isShared_2706_ = v_isSharedCheck_2815_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_2699_, 2);
                        lean_dec(v_a_2696_);
                        lean_dec_ref(v_type_2684_);
                        v_a_2816_ = lean_ctor_get(v___x_2702_, 0);
                        v_isSharedCheck_2823_ = (!lean_is_exclusive(v___x_2702_)) as u8;
                        if v_isSharedCheck_2823_ == 0 {
                            v___x_2818_ = v___x_2702_;
                            v_isShared_2819_ = v_isSharedCheck_2823_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_2816_);
                            lean_dec(v___x_2702_);
                            v___x_2818_ = lean_box(0);
                            v_isShared_2819_ = v_isSharedCheck_2823_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2684_);
                    v_a_2824_ = lean_ctor_get(v___x_2695_, 0);
                    v_isSharedCheck_2831_ = (!lean_is_exclusive(v___x_2695_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v___x_2826_ = v___x_2695_;
                        v_isShared_2827_ = v_isSharedCheck_2831_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_2824_);
                        lean_dec(v___x_2695_);
                        v___x_2826_ = lean_box(0);
                        v_isShared_2827_ = v_isSharedCheck_2831_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2693_ = lean_box(0);
                v___x_2694_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2694_, 0, v___x_2693_);
                return v___x_2694_;
            }
            2 => {
                if lean_obj_tag(v_a_2703_) == 1 {
                    lean_del_object(v___x_2705_);
                    v_val_2707_ = lean_ctor_get(v_a_2703_, 0);
                    lean_inc_n(v_val_2707_, 2);
                    lean_dec_ref_known(v_a_2703_, 1);
                    v___x_2708_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__2;
                    lean_inc_ref(v___x_2699_);
                    v___x_2709_ = l_Lean_mkConst(v___x_2708_, v___x_2699_);
                    lean_inc_ref_n(v_type_2684_, 2);
                    v___x_2710_ = l_Lean_mkAppB(v___x_2709_, v_type_2684_, v_val_2707_);
                    v___x_2711_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__5;
                    v___x_2712_ = l_Lean_mkConst(v___x_2711_, v___x_2699_);
                    lean_inc_ref(v___x_2710_);
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
                    if lean_obj_tag(v___x_2714_) == 0 {
                        v_a_2715_ = lean_ctor_get(v___x_2714_, 0);
                        lean_inc(v_a_2715_);
                        lean_dec_ref_known(v___x_2714_, 1);
                        v___x_2716_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_2715_, v_a_2686_);
                        if lean_obj_tag(v___x_2716_) == 0 {
                            v_a_2717_ = lean_ctor_get(v___x_2716_, 0);
                            lean_inc_n(v_a_2717_, 2);
                            lean_dec_ref_known(v___x_2716_, 1);
                            v___x_2718_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f(v_a_2717_, v_a_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_, v_a_2690_);
                            if lean_obj_tag(v___x_2718_) == 0 {
                                v_a_2719_ = lean_ctor_get(v___x_2718_, 0);
                                lean_inc(v_a_2719_);
                                lean_dec_ref_known(v___x_2718_, 1);
                                if lean_obj_tag(v_a_2719_) == 1 {
                                    lean_dec(v_a_2717_);
                                    v_val_2720_ = lean_ctor_get(v_a_2719_, 0);
                                    v_isSharedCheck_2771_ = (!lean_is_exclusive(v_a_2719_)) as u8;
                                    if v_isSharedCheck_2771_ == 0 {
                                        v___x_2722_ = v_a_2719_;
                                        v_isShared_2723_ = v_isSharedCheck_2771_;
                                        state = 3;
                                        continue;
                                    } else {
                                        lean_inc(v_val_2720_);
                                        lean_dec(v_a_2719_);
                                        v___x_2722_ = lean_box(0);
                                        v_isShared_2723_ = v_isSharedCheck_2771_;
                                        state = 3;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_2719_);
                                    lean_dec_ref(v___x_2710_);
                                    lean_dec(v_val_2707_);
                                    lean_dec(v_a_2696_);
                                    lean_dec_ref(v_type_2684_);
                                    v___x_2772_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2685_);
                                    if lean_obj_tag(v___x_2772_) == 0 {
                                        v_a_2773_ = lean_ctor_get(v___x_2772_, 0);
                                        lean_inc(v_a_2773_);
                                        lean_dec_ref_known(v___x_2772_, 1);
                                        v___x_2774_ = (lean_unbox(v_a_2773_) as u8);
                                        lean_dec(v_a_2773_);
                                        if v___x_2774_ == 0 {
                                            lean_dec(v_a_2717_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_2775_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7_once), _init_l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___closed__7);
                                            v___x_2776_ = l_Lean_indentExpr(v_a_2717_);
                                            v___x_2777_ = lean_alloc_ctor(7, 2, (0) as u32);
                                            lean_ctor_set(v___x_2777_, 0, v___x_2775_);
                                            lean_ctor_set(v___x_2777_, 1, v___x_2776_);
                                            v___x_2778_ = l_Lean_Meta_Sym_reportIssue(
                                                v___x_2777_,
                                                v_a_2685_,
                                                v_a_2686_,
                                                v_a_2687_,
                                                v_a_2688_,
                                                v_a_2689_,
                                                v_a_2690_,
                                            );
                                            if lean_obj_tag(v___x_2778_) == 0 {
                                                lean_dec_ref_known(v___x_2778_, 1);
                                                state = 1;
                                                continue;
                                            } else {
                                                v_a_2779_ = lean_ctor_get(v___x_2778_, 0);
                                                v_isSharedCheck_2786_ =
                                                    (!lean_is_exclusive(v___x_2778_)) as u8;
                                                if v_isSharedCheck_2786_ == 0 {
                                                    v___x_2781_ = v___x_2778_;
                                                    v_isShared_2782_ = v_isSharedCheck_2786_;
                                                    state = 13;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_2779_);
                                                    lean_dec(v___x_2778_);
                                                    v___x_2781_ = lean_box(0);
                                                    v_isShared_2782_ = v_isSharedCheck_2786_;
                                                    state = 13;
                                                    continue;
                                                }
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_2717_);
                                        v_a_2787_ = lean_ctor_get(v___x_2772_, 0);
                                        v_isSharedCheck_2794_ =
                                            (!lean_is_exclusive(v___x_2772_)) as u8;
                                        if v_isSharedCheck_2794_ == 0 {
                                            v___x_2789_ = v___x_2772_;
                                            v_isShared_2790_ = v_isSharedCheck_2794_;
                                            state = 15;
                                            continue;
                                        } else {
                                            lean_inc(v_a_2787_);
                                            lean_dec(v___x_2772_);
                                            v___x_2789_ = lean_box(0);
                                            v_isShared_2790_ = v_isSharedCheck_2794_;
                                            state = 15;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_2717_);
                                lean_dec_ref(v___x_2710_);
                                lean_dec(v_val_2707_);
                                lean_dec(v_a_2696_);
                                lean_dec_ref(v_type_2684_);
                                return v___x_2718_;
                            }
                        } else {
                            lean_dec_ref(v___x_2710_);
                            lean_dec(v_val_2707_);
                            lean_dec(v_a_2696_);
                            lean_dec_ref(v_type_2684_);
                            v_a_2795_ = lean_ctor_get(v___x_2716_, 0);
                            v_isSharedCheck_2802_ = (!lean_is_exclusive(v___x_2716_)) as u8;
                            if v_isSharedCheck_2802_ == 0 {
                                v___x_2797_ = v___x_2716_;
                                v_isShared_2798_ = v_isSharedCheck_2802_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_2795_);
                                lean_dec(v___x_2716_);
                                v___x_2797_ = lean_box(0);
                                v_isShared_2798_ = v_isSharedCheck_2802_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_2710_);
                        lean_dec(v_val_2707_);
                        lean_dec(v_a_2696_);
                        lean_dec_ref(v_type_2684_);
                        v_a_2803_ = lean_ctor_get(v___x_2714_, 0);
                        v_isSharedCheck_2810_ = (!lean_is_exclusive(v___x_2714_)) as u8;
                        if v_isSharedCheck_2810_ == 0 {
                            v___x_2805_ = v___x_2714_;
                            v_isShared_2806_ = v_isSharedCheck_2810_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_2803_);
                            lean_dec(v___x_2714_);
                            v___x_2805_ = lean_box(0);
                            v_isShared_2806_ = v_isSharedCheck_2810_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2703_);
                    lean_dec_ref_known(v___x_2699_, 2);
                    lean_dec(v_a_2696_);
                    lean_dec_ref(v_type_2684_);
                    v___x_2811_ = lean_box(0);
                    if v_isShared_2706_ == 0 {
                        lean_ctor_set(v___x_2705_, 0, v___x_2811_);
                        v___x_2813_ = v___x_2705_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
                        v___x_2813_ = v_reuseFailAlloc_2814_;
                        state = 21;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2724_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2686_, v_a_2689_);
                if lean_obj_tag(v___x_2724_) == 0 {
                    v_a_2725_ = lean_ctor_get(v___x_2724_, 0);
                    lean_inc(v_a_2725_);
                    lean_dec_ref_known(v___x_2724_, 1);
                    v_semirings_2726_ = lean_ctor_get(v_a_2725_, 2);
                    lean_inc_ref(v_semirings_2726_);
                    lean_dec(v_a_2725_);
                    v___x_2727_ = lean_array_get_size(v_semirings_2726_);
                    lean_dec_ref(v_semirings_2726_);
                    v___x_2728_ = lean_box(0);
                    v___x_2729_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_2729_, 0, v___x_2727_);
                    lean_ctor_set(v___x_2729_, 1, v_type_2684_);
                    lean_ctor_set(v___x_2729_, 2, v_a_2696_);
                    lean_ctor_set(v___x_2729_, 3, v___x_2710_);
                    lean_ctor_set(v___x_2729_, 4, v___x_2728_);
                    lean_ctor_set(v___x_2729_, 5, v___x_2728_);
                    lean_ctor_set(v___x_2729_, 6, v___x_2728_);
                    lean_ctor_set(v___x_2729_, 7, v___x_2728_);
                    lean_inc(v_val_2720_);
                    v___x_2730_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_2730_, 0, v___x_2729_);
                    lean_ctor_set(v___x_2730_, 1, v_val_2720_);
                    lean_ctor_set(v___x_2730_, 2, v_val_2707_);
                    lean_ctor_set(v___x_2730_, 3, v___x_2728_);
                    lean_ctor_set(v___x_2730_, 4, v___x_2728_);
                    v___f_2731_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__0 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_2731_, 0, v___x_2730_);
                    v___x_2732_ = l_Lean_Meta_Sym_Arith_arithExt;
                    v___x_2733_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2732_, v___f_2731_, v_a_2686_);
                    if lean_obj_tag(v___x_2733_) == 0 {
                        lean_dec_ref_known(v___x_2733_, 1);
                        v___f_2734_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f___lam__1___boxed as *mut core::ffi::c_void, 3, 2);
                        lean_closure_set(v___f_2734_, 0, v_val_2720_);
                        lean_closure_set(v___f_2734_, 1, v___x_2727_);
                        v___x_2735_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2732_, v___f_2734_, v_a_2686_);
                        if lean_obj_tag(v___x_2735_) == 0 {
                            v_isSharedCheck_2745_ = (!lean_is_exclusive(v___x_2735_)) as u8;
                            if v_isSharedCheck_2745_ == 0 {
                                v_unused_2746_ = lean_ctor_get(v___x_2735_, 0);
                                lean_dec(v_unused_2746_);
                                v___x_2737_ = v___x_2735_;
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 4;
                                continue;
                            } else {
                                lean_dec(v___x_2735_);
                                v___x_2737_ = lean_box(0);
                                v_isShared_2738_ = v_isSharedCheck_2745_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2722_);
                            v_a_2747_ = lean_ctor_get(v___x_2735_, 0);
                            v_isSharedCheck_2754_ = (!lean_is_exclusive(v___x_2735_)) as u8;
                            if v_isSharedCheck_2754_ == 0 {
                                v___x_2749_ = v___x_2735_;
                                v_isShared_2750_ = v_isSharedCheck_2754_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2747_);
                                lean_dec(v___x_2735_);
                                v___x_2749_ = lean_box(0);
                                v_isShared_2750_ = v_isSharedCheck_2754_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_2722_);
                        lean_dec(v_val_2720_);
                        v_a_2755_ = lean_ctor_get(v___x_2733_, 0);
                        v_isSharedCheck_2762_ = (!lean_is_exclusive(v___x_2733_)) as u8;
                        if v_isSharedCheck_2762_ == 0 {
                            v___x_2757_ = v___x_2733_;
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2755_);
                            lean_dec(v___x_2733_);
                            v___x_2757_ = lean_box(0);
                            v_isShared_2758_ = v_isSharedCheck_2762_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2722_);
                    lean_dec(v_val_2720_);
                    lean_dec_ref(v___x_2710_);
                    lean_dec(v_val_2707_);
                    lean_dec(v_a_2696_);
                    lean_dec_ref(v_type_2684_);
                    v_a_2763_ = lean_ctor_get(v___x_2724_, 0);
                    v_isSharedCheck_2770_ = (!lean_is_exclusive(v___x_2724_)) as u8;
                    if v_isSharedCheck_2770_ == 0 {
                        v___x_2765_ = v___x_2724_;
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_2763_);
                        lean_dec(v___x_2724_);
                        v___x_2765_ = lean_box(0);
                        v_isShared_2766_ = v_isSharedCheck_2770_;
                        state = 11;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_2723_ == 0 {
                    lean_ctor_set(v___x_2722_, 0, v___x_2727_);
                    v___x_2740_ = v___x_2722_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2727_);
                    v___x_2740_ = v_reuseFailAlloc_2744_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2738_ == 0 {
                    lean_ctor_set(v___x_2737_, 0, v___x_2740_);
                    v___x_2742_ = v___x_2737_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2743_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2740_);
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
                    v_reuseFailAlloc_2753_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2753_, 0, v_a_2747_);
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
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2755_);
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
                    v_reuseFailAlloc_2769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_a_2763_);
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
                    v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2779_);
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
                    v_reuseFailAlloc_2793_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2793_, 0, v_a_2787_);
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
                    v_reuseFailAlloc_2801_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2801_, 0, v_a_2795_);
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
                    v_reuseFailAlloc_2809_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_a_2803_);
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
                    v_reuseFailAlloc_2822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_a_2816_);
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
                    v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_a_2824_);
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
    mut v_type_2832_: *mut LeanObject,
    mut v_a_2833_: *mut LeanObject,
    mut v_a_2834_: *mut LeanObject,
    mut v_a_2835_: *mut LeanObject,
    mut v_a_2836_: *mut LeanObject,
    mut v_a_2837_: *mut LeanObject,
    mut v_a_2838_: *mut LeanObject,
    mut v_a_2839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2840_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2838_);
    lean_dec_ref(v_a_2837_);
    lean_dec(v_a_2836_);
    lean_dec_ref(v_a_2835_);
    lean_dec(v_a_2834_);
    lean_dec_ref(v_a_2833_);
    return v_res_2840_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0(
    mut v___x_2841_: *mut LeanObject,
    mut v_s_2842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_2843_ = lean_ctor_get(v_s_2842_, 0);
                v_rings_2844_ = lean_ctor_get(v_s_2842_, 1);
                v_semirings_2845_ = lean_ctor_get(v_s_2842_, 2);
                v_ncRings_2846_ = lean_ctor_get(v_s_2842_, 3);
                v_ncSemirings_2847_ = lean_ctor_get(v_s_2842_, 4);
                v_typeClassify_2848_ = lean_ctor_get(v_s_2842_, 5);
                v_isSharedCheck_2856_ = (!lean_is_exclusive(v_s_2842_)) as u8;
                if v_isSharedCheck_2856_ == 0 {
                    v___x_2850_ = v_s_2842_;
                    v_isShared_2851_ = v_isSharedCheck_2856_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_2848_);
                    lean_inc(v_ncSemirings_2847_);
                    lean_inc(v_ncRings_2846_);
                    lean_inc(v_semirings_2845_);
                    lean_inc(v_rings_2844_);
                    lean_inc(v_exp_2843_);
                    lean_dec(v_s_2842_);
                    v___x_2850_ = lean_box(0);
                    v_isShared_2851_ = v_isSharedCheck_2856_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2852_ = lean_array_push(v_ncSemirings_2847_, v___x_2841_);
                if v_isShared_2851_ == 0 {
                    lean_ctor_set(v___x_2850_, 4, v___x_2852_);
                    v___x_2854_ = v___x_2850_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_exp_2843_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_rings_2844_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 2, v_semirings_2845_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 3, v_ncRings_2846_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 4, v___x_2852_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 5, v_typeClassify_2848_);
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
    mut v_type_2862_: *mut LeanObject,
    mut v_a_2863_: *mut LeanObject,
    mut v_a_2864_: *mut LeanObject,
    mut v_a_2865_: *mut LeanObject,
    mut v_a_2866_: *mut LeanObject,
    mut v_a_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2880_: u8 = 0;
    let mut v_val_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2884_: u8 = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2903_: u8 = 0;
    let mut v_unused_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2908_: u8 = 0;
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2912_: u8 = 0;
    let mut v_a_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2916_: u8 = 0;
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2920_: u8 = 0;
    let mut v_isSharedCheck_2921_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v_a_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2930_: u8 = 0;
    let mut v___x_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2934_: u8 = 0;
    let mut v_a_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2938_: u8 = 0;
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2862_);
                v___x_2869_ = l_Lean_Meta_getDecLevel(
                    v_type_2862_,
                    v_a_2864_,
                    v_a_2865_,
                    v_a_2866_,
                    v_a_2867_,
                );
                if lean_obj_tag(v___x_2869_) == 0 {
                    v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
                    lean_inc_n(v_a_2870_, 2);
                    lean_dec_ref_known(v___x_2869_, 1);
                    v___x_2871_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___closed__1;
                    v___x_2872_ = lean_box(0);
                    v___x_2873_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_2873_, 0, v_a_2870_);
                    lean_ctor_set(v___x_2873_, 1, v___x_2872_);
                    v___x_2874_ = l_Lean_mkConst(v___x_2871_, v___x_2873_);
                    lean_inc_ref(v_type_2862_);
                    v___x_2875_ = l_Lean_Expr_app___override(v___x_2874_, v_type_2862_);
                    v___x_2876_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_2875_,
                        v_a_2864_,
                        v_a_2865_,
                        v_a_2866_,
                        v_a_2867_,
                    );
                    if lean_obj_tag(v___x_2876_) == 0 {
                        v_a_2877_ = lean_ctor_get(v___x_2876_, 0);
                        v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2876_)) as u8;
                        if v_isSharedCheck_2926_ == 0 {
                            v___x_2879_ = v___x_2876_;
                            v_isShared_2880_ = v_isSharedCheck_2926_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2877_);
                            lean_dec(v___x_2876_);
                            v___x_2879_ = lean_box(0);
                            v_isShared_2880_ = v_isSharedCheck_2926_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2870_);
                        lean_dec_ref(v_type_2862_);
                        v_a_2927_ = lean_ctor_get(v___x_2876_, 0);
                        v_isSharedCheck_2934_ = (!lean_is_exclusive(v___x_2876_)) as u8;
                        if v_isSharedCheck_2934_ == 0 {
                            v___x_2929_ = v___x_2876_;
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_2927_);
                            lean_dec(v___x_2876_);
                            v___x_2929_ = lean_box(0);
                            v_isShared_2930_ = v_isSharedCheck_2934_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_2862_);
                    v_a_2935_ = lean_ctor_get(v___x_2869_, 0);
                    v_isSharedCheck_2942_ = (!lean_is_exclusive(v___x_2869_)) as u8;
                    if v_isSharedCheck_2942_ == 0 {
                        v___x_2937_ = v___x_2869_;
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2935_);
                        lean_dec(v___x_2869_);
                        v___x_2937_ = lean_box(0);
                        v_isShared_2938_ = v_isSharedCheck_2942_;
                        state = 13;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2877_) == 1 {
                    lean_del_object(v___x_2879_);
                    v_val_2881_ = lean_ctor_get(v_a_2877_, 0);
                    v_isSharedCheck_2921_ = (!lean_is_exclusive(v_a_2877_)) as u8;
                    if v_isSharedCheck_2921_ == 0 {
                        v___x_2883_ = v_a_2877_;
                        v_isShared_2884_ = v_isSharedCheck_2921_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2881_);
                        lean_dec(v_a_2877_);
                        v___x_2883_ = lean_box(0);
                        v_isShared_2884_ = v_isSharedCheck_2921_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2877_);
                    lean_dec(v_a_2870_);
                    lean_dec_ref(v_type_2862_);
                    v___x_2922_ = lean_box(0);
                    if v_isShared_2880_ == 0 {
                        lean_ctor_set(v___x_2879_, 0, v___x_2922_);
                        v___x_2924_ = v___x_2879_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2925_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2925_, 0, v___x_2922_);
                        v___x_2924_ = v_reuseFailAlloc_2925_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2885_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_2863_, v_a_2866_);
                if lean_obj_tag(v___x_2885_) == 0 {
                    v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
                    lean_inc(v_a_2886_);
                    lean_dec_ref_known(v___x_2885_, 1);
                    v_ncSemirings_2887_ = lean_ctor_get(v_a_2886_, 4);
                    lean_inc_ref(v_ncSemirings_2887_);
                    lean_dec(v_a_2886_);
                    v___x_2888_ = lean_array_get_size(v_ncSemirings_2887_);
                    lean_dec_ref(v_ncSemirings_2887_);
                    v___x_2889_ = lean_box(0);
                    v___x_2890_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v___x_2890_, 0, v___x_2888_);
                    lean_ctor_set(v___x_2890_, 1, v_type_2862_);
                    lean_ctor_set(v___x_2890_, 2, v_a_2870_);
                    lean_ctor_set(v___x_2890_, 3, v_val_2881_);
                    lean_ctor_set(v___x_2890_, 4, v___x_2889_);
                    lean_ctor_set(v___x_2890_, 5, v___x_2889_);
                    lean_ctor_set(v___x_2890_, 6, v___x_2889_);
                    lean_ctor_set(v___x_2890_, 7, v___x_2889_);
                    v___f_2891_ = lean_alloc_closure(l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_2891_, 0, v___x_2890_);
                    v___x_2892_ = l_Lean_Meta_Sym_Arith_arithExt;
                    v___x_2893_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_2892_, v___f_2891_, v_a_2863_);
                    if lean_obj_tag(v___x_2893_) == 0 {
                        v_isSharedCheck_2903_ = (!lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2903_ == 0 {
                            v_unused_2904_ = lean_ctor_get(v___x_2893_, 0);
                            lean_dec(v_unused_2904_);
                            v___x_2895_ = v___x_2893_;
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_2893_);
                            v___x_2895_ = lean_box(0);
                            v_isShared_2896_ = v_isSharedCheck_2903_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2883_);
                        v_a_2905_ = lean_ctor_get(v___x_2893_, 0);
                        v_isSharedCheck_2912_ = (!lean_is_exclusive(v___x_2893_)) as u8;
                        if v_isSharedCheck_2912_ == 0 {
                            v___x_2907_ = v___x_2893_;
                            v_isShared_2908_ = v_isSharedCheck_2912_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2905_);
                            lean_dec(v___x_2893_);
                            v___x_2907_ = lean_box(0);
                            v_isShared_2908_ = v_isSharedCheck_2912_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2883_);
                    lean_dec(v_val_2881_);
                    lean_dec(v_a_2870_);
                    lean_dec_ref(v_type_2862_);
                    v_a_2913_ = lean_ctor_get(v___x_2885_, 0);
                    v_isSharedCheck_2920_ = (!lean_is_exclusive(v___x_2885_)) as u8;
                    if v_isSharedCheck_2920_ == 0 {
                        v___x_2915_ = v___x_2885_;
                        v_isShared_2916_ = v_isSharedCheck_2920_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2913_);
                        lean_dec(v___x_2885_);
                        v___x_2915_ = lean_box(0);
                        v_isShared_2916_ = v_isSharedCheck_2920_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2884_ == 0 {
                    lean_ctor_set(v___x_2883_, 0, v___x_2888_);
                    v___x_2898_ = v___x_2883_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2888_);
                    v___x_2898_ = v_reuseFailAlloc_2902_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2896_ == 0 {
                    lean_ctor_set(v___x_2895_, 0, v___x_2898_);
                    v___x_2900_ = v___x_2895_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2901_, 0, v___x_2898_);
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
                    v_reuseFailAlloc_2911_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2911_, 0, v_a_2905_);
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
                    v_reuseFailAlloc_2919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_a_2913_);
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
                    v_reuseFailAlloc_2933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2933_, 0, v_a_2927_);
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
                    v_reuseFailAlloc_2941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2941_, 0, v_a_2935_);
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
    mut v_type_2943_: *mut LeanObject,
    mut v_a_2944_: *mut LeanObject,
    mut v_a_2945_: *mut LeanObject,
    mut v_a_2946_: *mut LeanObject,
    mut v_a_2947_: *mut LeanObject,
    mut v_a_2948_: *mut LeanObject,
    mut v_a_2949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2950_: *mut LeanObject = core::ptr::null_mut();
    v_res_2950_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2943_, v_a_2944_, v_a_2945_, v_a_2946_, v_a_2947_, v_a_2948_);
    lean_dec(v_a_2948_);
    lean_dec_ref(v_a_2947_);
    lean_dec(v_a_2946_);
    lean_dec_ref(v_a_2945_);
    lean_dec(v_a_2944_);
    return v_res_2950_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f(
    mut v_type_2951_: *mut LeanObject,
    mut v_a_2952_: *mut LeanObject,
    mut v_a_2953_: *mut LeanObject,
    mut v_a_2954_: *mut LeanObject,
    mut v_a_2955_: *mut LeanObject,
    mut v_a_2956_: *mut LeanObject,
    mut v_a_2957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    v___x_2959_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2951_, v_a_2953_, v_a_2954_, v_a_2955_, v_a_2956_, v_a_2957_);
    return v___x_2959_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___boxed(
    mut v_type_2960_: *mut LeanObject,
    mut v_a_2961_: *mut LeanObject,
    mut v_a_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2968_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2966_);
    lean_dec_ref(v_a_2965_);
    lean_dec(v_a_2964_);
    lean_dec_ref(v_a_2963_);
    lean_dec(v_a_2962_);
    lean_dec_ref(v_a_2961_);
    return v_res_2968_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(
    mut v_type_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
    mut v_a_2975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2981_: u8 = 0;
    let mut v_val_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2985_: u8 = 0;
    let mut v___x_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2992_: u8 = 0;
    let mut v___x_2993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2997_: u8 = 0;
    let mut v_val_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3013_: u8 = 0;
    let mut v_val_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3024_: u8 = 0;
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3029_: u8 = 0;
    let mut v_val_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3033_: u8 = 0;
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_a_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3049_: u8 = 0;
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3053_: u8 = 0;
    let mut v_isSharedCheck_3054_: u8 = 0;
    let mut v_a_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3058_: u8 = 0;
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3062_: u8 = 0;
    let mut v_isSharedCheck_3063_: u8 = 0;
    let mut v_a_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3067_: u8 = 0;
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3071_: u8 = 0;
    let mut v_isSharedCheck_3072_: u8 = 0;
    let mut v_a_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3076_: u8 = 0;
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3080_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_type_2969_);
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
                if lean_obj_tag(v___x_2977_) == 0 {
                    v_a_2978_ = lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_3072_ = (!lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_3072_ == 0 {
                        v___x_2980_ = v___x_2977_;
                        v_isShared_2981_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2978_);
                        lean_dec(v___x_2977_);
                        v___x_2980_ = lean_box(0);
                        v_isShared_2981_ = v_isSharedCheck_3072_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_2969_);
                    v_a_3073_ = lean_ctor_get(v___x_2977_, 0);
                    v_isSharedCheck_3080_ = (!lean_is_exclusive(v___x_2977_)) as u8;
                    if v_isSharedCheck_3080_ == 0 {
                        v___x_3075_ = v___x_2977_;
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 24;
                        continue;
                    } else {
                        lean_inc(v_a_3073_);
                        lean_dec(v___x_2977_);
                        v___x_3075_ = lean_box(0);
                        v_isShared_3076_ = v_isSharedCheck_3080_;
                        state = 24;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2978_) == 1 {
                    lean_dec_ref(v_type_2969_);
                    v_val_2982_ = lean_ctor_get(v_a_2978_, 0);
                    v_isSharedCheck_2992_ = (!lean_is_exclusive(v_a_2978_)) as u8;
                    if v_isSharedCheck_2992_ == 0 {
                        v___x_2984_ = v_a_2978_;
                        v_isShared_2985_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2982_);
                        lean_dec(v_a_2978_);
                        v___x_2984_ = lean_box(0);
                        v_isShared_2985_ = v_isSharedCheck_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2980_);
                    lean_dec(v_a_2978_);
                    lean_inc_ref(v_type_2969_);
                    v___x_2993_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommRing_x3f(v_type_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if lean_obj_tag(v___x_2993_) == 0 {
                        v_a_2994_ = lean_ctor_get(v___x_2993_, 0);
                        v_isSharedCheck_3063_ = (!lean_is_exclusive(v___x_2993_)) as u8;
                        if v_isSharedCheck_3063_ == 0 {
                            v___x_2996_ = v___x_2993_;
                            v_isShared_2997_ = v_isSharedCheck_3063_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_2994_);
                            lean_dec(v___x_2993_);
                            v___x_2996_ = lean_box(0);
                            v_isShared_2997_ = v_isSharedCheck_3063_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_2969_);
                        v_a_3064_ = lean_ctor_get(v___x_2993_, 0);
                        v_isSharedCheck_3071_ = (!lean_is_exclusive(v___x_2993_)) as u8;
                        if v_isSharedCheck_3071_ == 0 {
                            v___x_3066_ = v___x_2993_;
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 22;
                            continue;
                        } else {
                            lean_inc(v_a_3064_);
                            lean_dec(v___x_2993_);
                            v___x_3066_ = lean_box(0);
                            v_isShared_3067_ = v_isSharedCheck_3071_;
                            state = 22;
                            continue;
                        }
                    }
                }
            }
            2 => {
                if v_isShared_2985_ == 0 {
                    lean_ctor_set_tag(v___x_2984_, 0);
                    v___x_2987_ = v___x_2984_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_val_2982_);
                    v___x_2987_ = v_reuseFailAlloc_2991_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2981_ == 0 {
                    lean_ctor_set(v___x_2980_, 0, v___x_2987_);
                    v___x_2989_ = v___x_2980_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2990_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2990_, 0, v___x_2987_);
                    v___x_2989_ = v_reuseFailAlloc_2990_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2989_;
            }
            5 => {
                if lean_obj_tag(v_a_2994_) == 1 {
                    lean_dec_ref(v_type_2969_);
                    v_val_2998_ = lean_ctor_get(v_a_2994_, 0);
                    v_isSharedCheck_3008_ = (!lean_is_exclusive(v_a_2994_)) as u8;
                    if v_isSharedCheck_3008_ == 0 {
                        v___x_3000_ = v_a_2994_;
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_2998_);
                        lean_dec(v_a_2994_);
                        v___x_3000_ = lean_box(0);
                        v_isShared_3001_ = v_isSharedCheck_3008_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2996_);
                    lean_dec(v_a_2994_);
                    lean_inc_ref(v_type_2969_);
                    v___x_3009_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCommSemiring_x3f(v_type_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if lean_obj_tag(v___x_3009_) == 0 {
                        v_a_3010_ = lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3054_ = (!lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3054_ == 0 {
                            v___x_3012_ = v___x_3009_;
                            v_isShared_3013_ = v_isSharedCheck_3054_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_3010_);
                            lean_dec(v___x_3009_);
                            v___x_3012_ = lean_box(0);
                            v_isShared_3013_ = v_isSharedCheck_3054_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_type_2969_);
                        v_a_3055_ = lean_ctor_get(v___x_3009_, 0);
                        v_isSharedCheck_3062_ = (!lean_is_exclusive(v___x_3009_)) as u8;
                        if v_isSharedCheck_3062_ == 0 {
                            v___x_3057_ = v___x_3009_;
                            v_isShared_3058_ = v_isSharedCheck_3062_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_3055_);
                            lean_dec(v___x_3009_);
                            v___x_3057_ = lean_box(0);
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
                    v_reuseFailAlloc_3007_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3007_, 0, v_val_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3007_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2997_ == 0 {
                    lean_ctor_set(v___x_2996_, 0, v___x_3003_);
                    v___x_3005_ = v___x_2996_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3006_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3006_, 0, v___x_3003_);
                    v___x_3005_ = v_reuseFailAlloc_3006_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3005_;
            }
            9 => {
                if lean_obj_tag(v_a_3010_) == 1 {
                    lean_dec_ref(v_type_2969_);
                    v_val_3014_ = lean_ctor_get(v_a_3010_, 0);
                    v_isSharedCheck_3024_ = (!lean_is_exclusive(v_a_3010_)) as u8;
                    if v_isSharedCheck_3024_ == 0 {
                        v___x_3016_ = v_a_3010_;
                        v_isShared_3017_ = v_isSharedCheck_3024_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_val_3014_);
                        lean_dec(v_a_3010_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3024_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3012_);
                    lean_dec(v_a_3010_);
                    v___x_3025_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryNonCommSemiring_x3f___redArg(v_type_2969_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_);
                    if lean_obj_tag(v___x_3025_) == 0 {
                        v_a_3026_ = lean_ctor_get(v___x_3025_, 0);
                        v_isSharedCheck_3045_ = (!lean_is_exclusive(v___x_3025_)) as u8;
                        if v_isSharedCheck_3045_ == 0 {
                            v___x_3028_ = v___x_3025_;
                            v_isShared_3029_ = v_isSharedCheck_3045_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3026_);
                            lean_dec(v___x_3025_);
                            v___x_3028_ = lean_box(0);
                            v_isShared_3029_ = v_isSharedCheck_3045_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v_a_3046_ = lean_ctor_get(v___x_3025_, 0);
                        v_isSharedCheck_3053_ = (!lean_is_exclusive(v___x_3025_)) as u8;
                        if v_isSharedCheck_3053_ == 0 {
                            v___x_3048_ = v___x_3025_;
                            v_isShared_3049_ = v_isSharedCheck_3053_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3046_);
                            lean_dec(v___x_3025_);
                            v___x_3048_ = lean_box(0);
                            v_isShared_3049_ = v_isSharedCheck_3053_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            10 => {
                if v_isShared_3017_ == 0 {
                    lean_ctor_set_tag(v___x_3016_, 2);
                    v___x_3019_ = v___x_3016_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3023_ = lean_alloc_ctor(2, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3023_, 0, v_val_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3023_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3013_ == 0 {
                    lean_ctor_set(v___x_3012_, 0, v___x_3019_);
                    v___x_3021_ = v___x_3012_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3022_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3022_, 0, v___x_3019_);
                    v___x_3021_ = v_reuseFailAlloc_3022_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3021_;
            }
            13 => {
                if lean_obj_tag(v_a_3026_) == 1 {
                    v_val_3030_ = lean_ctor_get(v_a_3026_, 0);
                    v_isSharedCheck_3040_ = (!lean_is_exclusive(v_a_3026_)) as u8;
                    if v_isSharedCheck_3040_ == 0 {
                        v___x_3032_ = v_a_3026_;
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_val_3030_);
                        lean_dec(v_a_3026_);
                        v___x_3032_ = lean_box(0);
                        v_isShared_3033_ = v_isSharedCheck_3040_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3026_);
                    v___x_3041_ = lean_box(4);
                    if v_isShared_3029_ == 0 {
                        lean_ctor_set(v___x_3028_, 0, v___x_3041_);
                        v___x_3043_ = v___x_3028_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3044_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3044_, 0, v___x_3041_);
                        v___x_3043_ = v_reuseFailAlloc_3044_;
                        state = 17;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_3033_ == 0 {
                    lean_ctor_set_tag(v___x_3032_, 3);
                    v___x_3035_ = v___x_3032_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_val_3030_);
                    v___x_3035_ = v_reuseFailAlloc_3039_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_3029_ == 0 {
                    lean_ctor_set(v___x_3028_, 0, v___x_3035_);
                    v___x_3037_ = v___x_3028_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
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
                    v_reuseFailAlloc_3052_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3052_, 0, v_a_3046_);
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
                    v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
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
                    v_reuseFailAlloc_3070_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3070_, 0, v_a_3064_);
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
                    v_reuseFailAlloc_3079_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3079_, 0, v_a_3073_);
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
    mut v_type_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
    mut v_a_3083_: *mut LeanObject,
    mut v_a_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3089_: *mut LeanObject = core::ptr::null_mut();
    v_res_3089_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(
        v_type_3081_,
        v_a_3082_,
        v_a_3083_,
        v_a_3084_,
        v_a_3085_,
        v_a_3086_,
        v_a_3087_,
    );
    lean_dec(v_a_3087_);
    lean_dec_ref(v_a_3086_);
    lean_dec(v_a_3085_);
    lean_dec_ref(v_a_3084_);
    lean_dec(v_a_3083_);
    lean_dec_ref(v_a_3082_);
    return v_res_3089_;
}
pub unsafe fn l_Lean_Meta_Sym_Arith_classify_x3f___lam__0(
    mut v_type_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
    mut v_s_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_exp_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v_semirings_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncRings_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeClassify_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3101_: u8 = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_exp_3093_ = lean_ctor_get(v_s_3092_, 0);
                v_rings_3094_ = lean_ctor_get(v_s_3092_, 1);
                v_semirings_3095_ = lean_ctor_get(v_s_3092_, 2);
                v_ncRings_3096_ = lean_ctor_get(v_s_3092_, 3);
                v_ncSemirings_3097_ = lean_ctor_get(v_s_3092_, 4);
                v_typeClassify_3098_ = lean_ctor_get(v_s_3092_, 5);
                v_isSharedCheck_3106_ = (!lean_is_exclusive(v_s_3092_)) as u8;
                if v_isSharedCheck_3106_ == 0 {
                    v___x_3100_ = v_s_3092_;
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_typeClassify_3098_);
                    lean_inc(v_ncSemirings_3097_);
                    lean_inc(v_ncRings_3096_);
                    lean_inc(v_semirings_3095_);
                    lean_inc(v_rings_3094_);
                    lean_inc(v_exp_3093_);
                    lean_dec(v_s_3092_);
                    v___x_3100_ = lean_box(0);
                    v_isShared_3101_ = v_isSharedCheck_3106_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3102_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__1___redArg(v_typeClassify_3098_, v_type_3090_, v_a_3091_);
                if v_isShared_3101_ == 0 {
                    lean_ctor_set(v___x_3100_, 5, v___x_3102_);
                    v___x_3104_ = v___x_3100_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3105_ = lean_alloc_ctor(0, 6, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 0, v_exp_3093_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 1, v_rings_3094_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 2, v_semirings_3095_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 3, v_ncRings_3096_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 4, v_ncSemirings_3097_);
                    lean_ctor_set(v_reuseFailAlloc_3105_, 5, v___x_3102_);
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
    mut v_type_3107_: *mut LeanObject,
    mut v_a_3108_: *mut LeanObject,
    mut v_a_3109_: *mut LeanObject,
    mut v_a_3110_: *mut LeanObject,
    mut v_a_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3119_: u8 = 0;
    let mut v_typeClassify_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3133_: u8 = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_unused_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3142_: u8 = 0;
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3146_: u8 = 0;
    let mut v_isSharedCheck_3147_: u8 = 0;
    let mut v_a_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3151_: u8 = 0;
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3115_ = l_Lean_Meta_Sym_Arith_getArithState___redArg(v_a_3109_, v_a_3112_);
                if lean_obj_tag(v___x_3115_) == 0 {
                    v_a_3116_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3147_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3147_ == 0 {
                        v___x_3118_ = v___x_3115_;
                        v_isShared_3119_ = v_isSharedCheck_3147_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3116_);
                        lean_dec(v___x_3115_);
                        v___x_3118_ = lean_box(0);
                        v_isShared_3119_ = v_isSharedCheck_3147_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_type_3107_);
                    v_a_3148_ = lean_ctor_get(v___x_3115_, 0);
                    v_isSharedCheck_3155_ = (!lean_is_exclusive(v___x_3115_)) as u8;
                    if v_isSharedCheck_3155_ == 0 {
                        v___x_3150_ = v___x_3115_;
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3148_);
                        lean_dec(v___x_3115_);
                        v___x_3150_ = lean_box(0);
                        v_isShared_3151_ = v_isSharedCheck_3155_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v_typeClassify_3120_ = lean_ctor_get(v_a_3116_, 5);
                lean_inc_ref(v_typeClassify_3120_);
                lean_dec(v_a_3116_);
                v___x_3121_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_tryCacheAndCommRing_x3f_spec__0___redArg(v_typeClassify_3120_, v_type_3107_);
                lean_dec_ref(v_typeClassify_3120_);
                if lean_obj_tag(v___x_3121_) == 1 {
                    lean_dec_ref(v_type_3107_);
                    v_val_3122_ = lean_ctor_get(v___x_3121_, 0);
                    lean_inc(v_val_3122_);
                    lean_dec_ref_known(v___x_3121_, 1);
                    if v_isShared_3119_ == 0 {
                        lean_ctor_set(v___x_3118_, 0, v_val_3122_);
                        v___x_3124_ = v___x_3118_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3125_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_val_3122_);
                        v___x_3124_ = v_reuseFailAlloc_3125_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3121_);
                    lean_del_object(v___x_3118_);
                    lean_inc_ref(v_type_3107_);
                    v___x_3126_ = l___private_Lean_Meta_Sym_Arith_Classify_0__Lean_Meta_Sym_Arith_classify_x3f_go(v_type_3107_, v_a_3108_, v_a_3109_, v_a_3110_, v_a_3111_, v_a_3112_, v_a_3113_);
                    if lean_obj_tag(v___x_3126_) == 0 {
                        v_a_3127_ = lean_ctor_get(v___x_3126_, 0);
                        lean_inc_n(v_a_3127_, 2);
                        lean_dec_ref_known(v___x_3126_, 1);
                        v___f_3128_ = lean_alloc_closure(
                            l_Lean_Meta_Sym_Arith_classify_x3f___lam__0 as *mut core::ffi::c_void,
                            3,
                            2,
                        );
                        lean_closure_set(v___f_3128_, 0, v_type_3107_);
                        lean_closure_set(v___f_3128_, 1, v_a_3127_);
                        v___x_3129_ = l_Lean_Meta_Sym_Arith_arithExt;
                        v___x_3130_ = l___private_Lean_Meta_Sym_SymM_0__Lean_Meta_Sym_SymExtension_modifyStateImpl___redArg(v___x_3129_, v___f_3128_, v_a_3109_);
                        if lean_obj_tag(v___x_3130_) == 0 {
                            v_isSharedCheck_3137_ = (!lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3137_ == 0 {
                                v_unused_3138_ = lean_ctor_get(v___x_3130_, 0);
                                lean_dec(v_unused_3138_);
                                v___x_3132_ = v___x_3130_;
                                v_isShared_3133_ = v_isSharedCheck_3137_;
                                state = 3;
                                continue;
                            } else {
                                lean_dec(v___x_3130_);
                                v___x_3132_ = lean_box(0);
                                v_isShared_3133_ = v_isSharedCheck_3137_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3127_);
                            v_a_3139_ = lean_ctor_get(v___x_3130_, 0);
                            v_isSharedCheck_3146_ = (!lean_is_exclusive(v___x_3130_)) as u8;
                            if v_isSharedCheck_3146_ == 0 {
                                v___x_3141_ = v___x_3130_;
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_3139_);
                                lean_dec(v___x_3130_);
                                v___x_3141_ = lean_box(0);
                                v_isShared_3142_ = v_isSharedCheck_3146_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_type_3107_);
                        return v___x_3126_;
                    }
                }
            }
            2 => {
                return v___x_3124_;
            }
            3 => {
                if v_isShared_3133_ == 0 {
                    lean_ctor_set(v___x_3132_, 0, v_a_3127_);
                    v___x_3135_ = v___x_3132_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3136_, 0, v_a_3127_);
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
                    v_reuseFailAlloc_3145_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3145_, 0, v_a_3139_);
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
                    v_reuseFailAlloc_3154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3154_, 0, v_a_3148_);
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
    mut v_type_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_a_3160_: *mut LeanObject,
    mut v_a_3161_: *mut LeanObject,
    mut v_a_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3164_: *mut LeanObject = core::ptr::null_mut();
    v_res_3164_ = l_Lean_Meta_Sym_Arith_classify_x3f(
        v_type_3156_,
        v_a_3157_,
        v_a_3158_,
        v_a_3159_,
        v_a_3160_,
        v_a_3161_,
        v_a_3162_,
    );
    lean_dec(v_a_3162_);
    lean_dec_ref(v_a_3161_);
    lean_dec(v_a_3160_);
    lean_dec_ref(v_a_3159_);
    lean_dec(v_a_3158_);
    lean_dec_ref(v_a_3157_);
    return v_res_3164_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Canon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Arith_Classify(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Arith_EvalNum(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Canon(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_DecLevel(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Ring(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Arith_Classify(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Arith_Classify(builtin);
}

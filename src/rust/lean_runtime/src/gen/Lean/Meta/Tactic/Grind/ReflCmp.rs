// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.ReflCmp
// Imports: Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.SynthInstance Lean.Meta.Tactic.Grind.Util
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Environment::l_Lean_Environment_contains;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isConstOf, l_Lean_mkApp3, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEq;
use crate::r#gen::Lean::Meta::DecLevel::l_Lean_Meta_decLevel_x3f;
use crate::r#gen::Lean::Meta::InferType::l_Lean_Meta_getLevel;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_getOrderingEqExpr___redArg;
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::SynthInstance::{
    initialize_Lean_Meta_Tactic_Grind_SynthInstance,
    runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_isEqv___redArg,
    l_Lean_Meta_Grind_pushEqCore___redArg, runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Util::{
    initialize_Lean_Meta_Tactic_Grind_Util, l_Lean_Meta_Grind_getBinOp,
    runtime_initialize_Lean_Meta_Tactic_Grind_Util,
};
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
use crate::lean_imports_rs::Lean::Meta::Basic::{lean_infer_type, lean_whnf};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_mk_eq_proof;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__0_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [83, 116, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__1_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [82, 101, 102, 108, 67, 109, 112, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__1_value) as *mut LeanObject,16485472678880165459 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__3_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [79, 114, 100, 101, 114, 105, 110, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__4_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__3_value) as *mut LeanObject,5208578977668345058 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__5_value: LeanStringObject<13> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [99, 109, 112, 95, 101, 113, 95, 111, 102, 95, 101, 113, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__5_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__0_value) as *mut LeanObject,15734321041234825264 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__1_value) as *mut LeanObject,16485472678880165459 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__5_value) as *mut LeanObject,12517604746812501498 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f(
    mut v_op_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
    mut v_a_652_: *mut LeanObject,
    mut v_a_653_: *mut LeanObject,
    mut v_a_654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: u8 = 0;
    let mut v___x_660_: u8 = 0;
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v_binderType_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: u8 = 0;
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v_binderType_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_681_: u8 = 0;
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_690_: u8 = 0;
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_702_: u8 = 0;
    let mut v_val_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v_val_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_716_: u8 = 0;
    let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_a_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_740_: u8 = 0;
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_744_: u8 = 0;
    let mut v_a_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_748_: u8 = 0;
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_752_: u8 = 0;
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_a_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_766_: u8 = 0;
    let mut v_a_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_770_: u8 = 0;
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_774_: u8 = 0;
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_783_: u8 = 0;
    let mut v_a_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_787_: u8 = 0;
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_791_: u8 = 0;
    let mut v_a_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_795_: u8 = 0;
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_656_ = lean_st_ref_get(v_a_654_);
                v_env_657_ = lean_ctor_get(v___x_656_, 0);
                lean_inc_ref(v_env_657_);
                lean_dec(v___x_656_);
                v___x_658_ = l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__2;
                v___x_659_ = 1;
                v___x_660_ = l_Lean_Environment_contains(v_env_657_, v___x_658_, v___x_659_);
                if v___x_660_ == 0 {
                    lean_dec_ref(v_op_650_);
                    v___x_661_ = lean_box(0);
                    v___x_662_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_662_, 0, v___x_661_);
                    return v___x_662_;
                } else {
                    lean_inc(v_a_654_);
                    lean_inc_ref(v_a_653_);
                    lean_inc(v_a_652_);
                    lean_inc_ref(v_a_651_);
                    lean_inc_ref(v_op_650_);
                    v___x_663_ = lean_infer_type(v_op_650_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                    if lean_obj_tag(v___x_663_) == 0 {
                        v_a_664_ = lean_ctor_get(v___x_663_, 0);
                        lean_inc(v_a_664_);
                        lean_dec_ref_known(v___x_663_, 1);
                        lean_inc(v_a_654_);
                        lean_inc_ref(v_a_653_);
                        lean_inc(v_a_652_);
                        lean_inc_ref(v_a_651_);
                        v___x_665_ = lean_whnf(v_a_664_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                        if lean_obj_tag(v___x_665_) == 0 {
                            v_a_666_ = lean_ctor_get(v___x_665_, 0);
                            v_isSharedCheck_783_ = (!lean_is_exclusive(v___x_665_)) as u8;
                            if v_isSharedCheck_783_ == 0 {
                                v___x_668_ = v___x_665_;
                                v_isShared_669_ = v_isSharedCheck_783_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_666_);
                                lean_dec(v___x_665_);
                                v___x_668_ = lean_box(0);
                                v_isShared_669_ = v_isSharedCheck_783_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_op_650_);
                            v_a_784_ = lean_ctor_get(v___x_665_, 0);
                            v_isSharedCheck_791_ = (!lean_is_exclusive(v___x_665_)) as u8;
                            if v_isSharedCheck_791_ == 0 {
                                v___x_786_ = v___x_665_;
                                v_isShared_787_ = v_isSharedCheck_791_;
                                state = 24;
                                continue;
                            } else {
                                lean_inc(v_a_784_);
                                lean_dec(v___x_665_);
                                v___x_786_ = lean_box(0);
                                v_isShared_787_ = v_isSharedCheck_791_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_op_650_);
                        v_a_792_ = lean_ctor_get(v___x_663_, 0);
                        v_isSharedCheck_799_ = (!lean_is_exclusive(v___x_663_)) as u8;
                        if v_isSharedCheck_799_ == 0 {
                            v___x_794_ = v___x_663_;
                            v_isShared_795_ = v_isSharedCheck_799_;
                            state = 26;
                            continue;
                        } else {
                            lean_inc(v_a_792_);
                            lean_dec(v___x_663_);
                            v___x_794_ = lean_box(0);
                            v_isShared_795_ = v_isSharedCheck_799_;
                            state = 26;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_666_) == 7 {
                    v_binderType_670_ = lean_ctor_get(v_a_666_, 1);
                    lean_inc_ref(v_binderType_670_);
                    v_body_671_ = lean_ctor_get(v_a_666_, 2);
                    lean_inc_ref(v_body_671_);
                    lean_dec_ref_known(v_a_666_, 3);
                    v___x_672_ = l_Lean_Expr_hasLooseBVars(v_body_671_);
                    if v___x_672_ == 0 {
                        lean_del_object(v___x_668_);
                        lean_inc(v_a_654_);
                        lean_inc_ref(v_a_653_);
                        lean_inc(v_a_652_);
                        lean_inc_ref(v_a_651_);
                        v___x_673_ = lean_whnf(v_body_671_, v_a_651_, v_a_652_, v_a_653_, v_a_654_);
                        if lean_obj_tag(v___x_673_) == 0 {
                            v_a_674_ = lean_ctor_get(v___x_673_, 0);
                            v_isSharedCheck_766_ = (!lean_is_exclusive(v___x_673_)) as u8;
                            if v_isSharedCheck_766_ == 0 {
                                v___x_676_ = v___x_673_;
                                v_isShared_677_ = v_isSharedCheck_766_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_674_);
                                lean_dec(v___x_673_);
                                v___x_676_ = lean_box(0);
                                v_isShared_677_ = v_isSharedCheck_766_;
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_binderType_670_);
                            lean_dec_ref(v_op_650_);
                            v_a_767_ = lean_ctor_get(v___x_673_, 0);
                            v_isSharedCheck_774_ = (!lean_is_exclusive(v___x_673_)) as u8;
                            if v_isSharedCheck_774_ == 0 {
                                v___x_769_ = v___x_673_;
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 20;
                                continue;
                            } else {
                                lean_inc(v_a_767_);
                                lean_dec(v___x_673_);
                                v___x_769_ = lean_box(0);
                                v_isShared_770_ = v_isSharedCheck_774_;
                                state = 20;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_body_671_);
                        lean_dec_ref(v_binderType_670_);
                        lean_dec_ref(v_op_650_);
                        v___x_775_ = lean_box(0);
                        if v_isShared_669_ == 0 {
                            lean_ctor_set(v___x_668_, 0, v___x_775_);
                            v___x_777_ = v___x_668_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_778_, 0, v___x_775_);
                            v___x_777_ = v_reuseFailAlloc_778_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_666_);
                    lean_dec_ref(v_op_650_);
                    v___x_779_ = lean_box(0);
                    if v_isShared_669_ == 0 {
                        lean_ctor_set(v___x_668_, 0, v___x_779_);
                        v___x_781_ = v___x_668_;
                        state = 23;
                        continue;
                    } else {
                        v_reuseFailAlloc_782_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_782_, 0, v___x_779_);
                        v___x_781_ = v_reuseFailAlloc_782_;
                        state = 23;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_674_) == 7 {
                    v_binderType_678_ = lean_ctor_get(v_a_674_, 1);
                    lean_inc_ref(v_binderType_678_);
                    v_body_679_ = lean_ctor_get(v_a_674_, 2);
                    lean_inc_ref(v_body_679_);
                    lean_dec_ref_known(v_a_674_, 3);
                    v___x_680_ = l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__4;
                    v___x_681_ = l_Lean_Expr_isConstOf(v_body_679_, v___x_680_);
                    lean_dec_ref(v_body_679_);
                    if v___x_681_ == 0 {
                        lean_dec_ref(v_binderType_678_);
                        lean_dec_ref(v_binderType_670_);
                        lean_dec_ref(v_op_650_);
                        v___x_682_ = lean_box(0);
                        if v_isShared_677_ == 0 {
                            lean_ctor_set(v___x_676_, 0, v___x_682_);
                            v___x_684_ = v___x_676_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_685_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_685_, 0, v___x_682_);
                            v___x_684_ = v_reuseFailAlloc_685_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_676_);
                        lean_inc_ref(v_binderType_670_);
                        v___x_686_ = l_Lean_Meta_isExprDefEq(
                            v_binderType_670_,
                            v_binderType_678_,
                            v_a_651_,
                            v_a_652_,
                            v_a_653_,
                            v_a_654_,
                        );
                        if lean_obj_tag(v___x_686_) == 0 {
                            v_a_687_ = lean_ctor_get(v___x_686_, 0);
                            v_isSharedCheck_753_ = (!lean_is_exclusive(v___x_686_)) as u8;
                            if v_isSharedCheck_753_ == 0 {
                                v___x_689_ = v___x_686_;
                                v_isShared_690_ = v_isSharedCheck_753_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_687_);
                                lean_dec(v___x_686_);
                                v___x_689_ = lean_box(0);
                                v_isShared_690_ = v_isSharedCheck_753_;
                                state = 4;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_binderType_670_);
                            lean_dec_ref(v_op_650_);
                            v_a_754_ = lean_ctor_get(v___x_686_, 0);
                            v_isSharedCheck_761_ = (!lean_is_exclusive(v___x_686_)) as u8;
                            if v_isSharedCheck_761_ == 0 {
                                v___x_756_ = v___x_686_;
                                v_isShared_757_ = v_isSharedCheck_761_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_754_);
                                lean_dec(v___x_686_);
                                v___x_756_ = lean_box(0);
                                v_isShared_757_ = v_isSharedCheck_761_;
                                state = 17;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_a_674_);
                    lean_dec_ref(v_binderType_670_);
                    lean_dec_ref(v_op_650_);
                    v___x_762_ = lean_box(0);
                    if v_isShared_677_ == 0 {
                        lean_ctor_set(v___x_676_, 0, v___x_762_);
                        v___x_764_ = v___x_676_;
                        state = 19;
                        continue;
                    } else {
                        v_reuseFailAlloc_765_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_765_, 0, v___x_762_);
                        v___x_764_ = v_reuseFailAlloc_765_;
                        state = 19;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_684_;
            }
            4 => {
                v___x_691_ = (lean_unbox(v_a_687_) as u8);
                lean_dec(v_a_687_);
                if v___x_691_ == 0 {
                    lean_dec_ref(v_binderType_670_);
                    lean_dec_ref(v_op_650_);
                    v___x_692_ = lean_box(0);
                    if v_isShared_690_ == 0 {
                        lean_ctor_set(v___x_689_, 0, v___x_692_);
                        v___x_694_ = v___x_689_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_695_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
                        v___x_694_ = v_reuseFailAlloc_695_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_689_);
                    lean_inc_ref(v_binderType_670_);
                    v___x_696_ = l_Lean_Meta_getLevel(
                        v_binderType_670_,
                        v_a_651_,
                        v_a_652_,
                        v_a_653_,
                        v_a_654_,
                    );
                    if lean_obj_tag(v___x_696_) == 0 {
                        v_a_697_ = lean_ctor_get(v___x_696_, 0);
                        lean_inc(v_a_697_);
                        lean_dec_ref_known(v___x_696_, 1);
                        v___x_698_ = l_Lean_Meta_decLevel_x3f(
                            v_a_697_, v_a_651_, v_a_652_, v_a_653_, v_a_654_,
                        );
                        if lean_obj_tag(v___x_698_) == 0 {
                            v_a_699_ = lean_ctor_get(v___x_698_, 0);
                            v_isSharedCheck_736_ = (!lean_is_exclusive(v___x_698_)) as u8;
                            if v_isSharedCheck_736_ == 0 {
                                v___x_701_ = v___x_698_;
                                v_isShared_702_ = v_isSharedCheck_736_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_699_);
                                lean_dec(v___x_698_);
                                v___x_701_ = lean_box(0);
                                v_isShared_702_ = v_isSharedCheck_736_;
                                state = 6;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_binderType_670_);
                            lean_dec_ref(v_op_650_);
                            v_a_737_ = lean_ctor_get(v___x_698_, 0);
                            v_isSharedCheck_744_ = (!lean_is_exclusive(v___x_698_)) as u8;
                            if v_isSharedCheck_744_ == 0 {
                                v___x_739_ = v___x_698_;
                                v_isShared_740_ = v_isSharedCheck_744_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_737_);
                                lean_dec(v___x_698_);
                                v___x_739_ = lean_box(0);
                                v_isShared_740_ = v_isSharedCheck_744_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_binderType_670_);
                        lean_dec_ref(v_op_650_);
                        v_a_745_ = lean_ctor_get(v___x_696_, 0);
                        v_isSharedCheck_752_ = (!lean_is_exclusive(v___x_696_)) as u8;
                        if v_isSharedCheck_752_ == 0 {
                            v___x_747_ = v___x_696_;
                            v_isShared_748_ = v_isSharedCheck_752_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_745_);
                            lean_dec(v___x_696_);
                            v___x_747_ = lean_box(0);
                            v_isShared_748_ = v_isSharedCheck_752_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            5 => {
                return v___x_694_;
            }
            6 => {
                if lean_obj_tag(v_a_699_) == 1 {
                    lean_del_object(v___x_701_);
                    v_val_703_ = lean_ctor_get(v_a_699_, 0);
                    lean_inc(v_val_703_);
                    lean_dec_ref_known(v_a_699_, 1);
                    v___x_704_ = lean_box(0);
                    v___x_705_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_705_, 0, v_val_703_);
                    lean_ctor_set(v___x_705_, 1, v___x_704_);
                    lean_inc_ref(v___x_705_);
                    v___x_706_ = l_Lean_mkConst(v___x_658_, v___x_705_);
                    lean_inc_ref(v_op_650_);
                    lean_inc_ref(v_binderType_670_);
                    v___x_707_ = l_Lean_mkAppB(v___x_706_, v_binderType_670_, v_op_650_);
                    v___x_708_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
                        v___x_707_, v_a_651_, v_a_652_, v_a_653_, v_a_654_,
                    );
                    if lean_obj_tag(v___x_708_) == 0 {
                        v_a_709_ = lean_ctor_get(v___x_708_, 0);
                        v_isSharedCheck_731_ = (!lean_is_exclusive(v___x_708_)) as u8;
                        if v_isSharedCheck_731_ == 0 {
                            v___x_711_ = v___x_708_;
                            v_isShared_712_ = v_isSharedCheck_731_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_709_);
                            lean_dec(v___x_708_);
                            v___x_711_ = lean_box(0);
                            v_isShared_712_ = v_isSharedCheck_731_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v___x_705_, 2);
                        lean_dec_ref(v_binderType_670_);
                        lean_dec_ref(v_op_650_);
                        return v___x_708_;
                    }
                } else {
                    lean_dec(v_a_699_);
                    lean_dec_ref(v_binderType_670_);
                    lean_dec_ref(v_op_650_);
                    v___x_732_ = lean_box(0);
                    if v_isShared_702_ == 0 {
                        lean_ctor_set(v___x_701_, 0, v___x_732_);
                        v___x_734_ = v___x_701_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_732_);
                        v___x_734_ = v_reuseFailAlloc_735_;
                        state = 12;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v_a_709_) == 1 {
                    v_val_713_ = lean_ctor_get(v_a_709_, 0);
                    v_isSharedCheck_726_ = (!lean_is_exclusive(v_a_709_)) as u8;
                    if v_isSharedCheck_726_ == 0 {
                        v___x_715_ = v_a_709_;
                        v_isShared_716_ = v_isSharedCheck_726_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_713_);
                        lean_dec(v_a_709_);
                        v___x_715_ = lean_box(0);
                        v_isShared_716_ = v_isSharedCheck_726_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_709_);
                    lean_dec_ref_known(v___x_705_, 2);
                    lean_dec_ref(v_binderType_670_);
                    lean_dec_ref(v_op_650_);
                    v___x_727_ = lean_box(0);
                    if v_isShared_712_ == 0 {
                        lean_ctor_set(v___x_711_, 0, v___x_727_);
                        v___x_729_ = v___x_711_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
                        v___x_729_ = v_reuseFailAlloc_730_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v___x_717_ = l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___closed__6;
                v___x_718_ = l_Lean_mkConst(v___x_717_, v___x_705_);
                v___x_719_ = l_Lean_mkApp3(v___x_718_, v_binderType_670_, v_op_650_, v_val_713_);
                if v_isShared_716_ == 0 {
                    lean_ctor_set(v___x_715_, 0, v___x_719_);
                    v___x_721_ = v___x_715_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_725_, 0, v___x_719_);
                    v___x_721_ = v_reuseFailAlloc_725_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_712_ == 0 {
                    lean_ctor_set(v___x_711_, 0, v___x_721_);
                    v___x_723_ = v___x_711_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_724_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_724_, 0, v___x_721_);
                    v___x_723_ = v_reuseFailAlloc_724_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_723_;
            }
            11 => {
                return v___x_729_;
            }
            12 => {
                return v___x_734_;
            }
            13 => {
                if v_isShared_740_ == 0 {
                    v___x_742_ = v___x_739_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_743_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_743_, 0, v_a_737_);
                    v___x_742_ = v_reuseFailAlloc_743_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_742_;
            }
            15 => {
                if v_isShared_748_ == 0 {
                    v___x_750_ = v___x_747_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_751_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_751_, 0, v_a_745_);
                    v___x_750_ = v_reuseFailAlloc_751_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_750_;
            }
            17 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_759_;
            }
            19 => {
                return v___x_764_;
            }
            20 => {
                if v_isShared_770_ == 0 {
                    v___x_772_ = v___x_769_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_773_, 0, v_a_767_);
                    v___x_772_ = v_reuseFailAlloc_773_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_772_;
            }
            22 => {
                return v___x_777_;
            }
            23 => {
                return v___x_781_;
            }
            24 => {
                if v_isShared_787_ == 0 {
                    v___x_789_ = v___x_786_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_790_, 0, v_a_784_);
                    v___x_789_ = v_reuseFailAlloc_790_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_789_;
            }
            26 => {
                if v_isShared_795_ == 0 {
                    v___x_797_ = v___x_794_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_798_, 0, v_a_792_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f___boxed(
    mut v_op_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
    mut v_a_803_: *mut LeanObject,
    mut v_a_804_: *mut LeanObject,
    mut v_a_805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_806_: *mut LeanObject = core::ptr::null_mut();
    v_res_806_ =
        l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f(
            v_op_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_,
        );
    lean_dec(v_a_804_);
    lean_dec_ref(v_a_803_);
    lean_dec(v_a_802_);
    lean_dec_ref(v_a_801_);
    return v_res_806_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(
    mut v_x_807_: *mut LeanObject,
    mut v_x_808_: *mut LeanObject,
    mut v_x_809_: *mut LeanObject,
    mut v_x_810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: u8 = 0;
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_836_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_811_ = lean_ctor_get(v_x_807_, 0);
                v_vs_812_ = lean_ctor_get(v_x_807_, 1);
                v_isSharedCheck_836_ = (!lean_is_exclusive(v_x_807_)) as u8;
                if v_isSharedCheck_836_ == 0 {
                    v___x_814_ = v_x_807_;
                    v_isShared_815_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_812_);
                    lean_inc(v_ks_811_);
                    lean_dec(v_x_807_);
                    v___x_814_ = lean_box(0);
                    v_isShared_815_ = v_isSharedCheck_836_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_816_ = lean_array_get_size(v_ks_811_);
                v___x_817_ = lean_nat_dec_lt(v_x_808_, v___x_816_);
                if v___x_817_ == 0 {
                    lean_dec(v_x_808_);
                    v___x_818_ = lean_array_push(v_ks_811_, v_x_809_);
                    v___x_819_ = lean_array_push(v_vs_812_, v_x_810_);
                    if v_isShared_815_ == 0 {
                        lean_ctor_set(v___x_814_, 1, v___x_819_);
                        lean_ctor_set(v___x_814_, 0, v___x_818_);
                        v___x_821_ = v___x_814_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_822_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_822_, 0, v___x_818_);
                        lean_ctor_set(v_reuseFailAlloc_822_, 1, v___x_819_);
                        v___x_821_ = v_reuseFailAlloc_822_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_823_ = lean_array_fget_borrowed(v_ks_811_, v_x_808_);
                    v___x_824_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_809_,
                            v_k_x27_823_,
                        );
                    if v___x_824_ == 0 {
                        if v_isShared_815_ == 0 {
                            v___x_826_ = v___x_814_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_830_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_830_, 0, v_ks_811_);
                            lean_ctor_set(v_reuseFailAlloc_830_, 1, v_vs_812_);
                            v___x_826_ = v_reuseFailAlloc_830_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_831_ = lean_array_fset(v_ks_811_, v_x_808_, v_x_809_);
                        v___x_832_ = lean_array_fset(v_vs_812_, v_x_808_, v_x_810_);
                        lean_dec(v_x_808_);
                        if v_isShared_815_ == 0 {
                            lean_ctor_set(v___x_814_, 1, v___x_832_);
                            lean_ctor_set(v___x_814_, 0, v___x_831_);
                            v___x_834_ = v___x_814_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_835_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_835_, 0, v___x_831_);
                            lean_ctor_set(v_reuseFailAlloc_835_, 1, v___x_832_);
                            v___x_834_ = v_reuseFailAlloc_835_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_821_;
            }
            3 => {
                v___x_827_ = lean_unsigned_to_nat(1);
                v___x_828_ = lean_nat_add(v_x_808_, v___x_827_);
                lean_dec(v_x_808_);
                v_x_807_ = v___x_826_;
                v_x_808_ = v___x_828_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_834_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4___redArg(
    mut v_n_837_: *mut LeanObject,
    mut v_k_838_: *mut LeanObject,
    mut v_v_839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    v___x_840_ = lean_unsigned_to_nat(0);
    v___x_841_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_n_837_, v___x_840_, v_k_838_, v_v_839_);
    return v___x_841_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_842_: usize = 0;
    let mut v___x_843_: usize = 0;
    let mut v___x_844_: usize = 0;
    v___x_842_ = 5usize;
    v___x_843_ = 1usize;
    v___x_844_ = lean_usize_shift_left(v___x_843_, v___x_842_);
    return v___x_844_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_845_: usize = 0;
    let mut v___x_846_: usize = 0;
    let mut v___x_847_: usize = 0;
    v___x_845_ = 1usize;
    v___x_846_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__0);
    v___x_847_ = lean_usize_sub(v___x_846_, v___x_845_);
    return v___x_847_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_848_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(
    mut v_x_849_: *mut LeanObject,
    mut v_x_850_: usize,
    mut v_x_851_: usize,
    mut v_x_852_: *mut LeanObject,
    mut v_x_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_855_: usize = 0;
    let mut v___x_856_: usize = 0;
    let mut v___x_857_: usize = 0;
    let mut v___x_858_: usize = 0;
    let mut v_j_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_864_: u8 = 0;
    let mut v_v_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_878_: u8 = 0;
    let mut v___x_879_: u8 = 0;
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_885_: u8 = 0;
    let mut v_node_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_889_: u8 = 0;
    let mut v___x_890_: usize = 0;
    let mut v___x_891_: usize = 0;
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_896_: u8 = 0;
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_898_: u8 = 0;
    let mut v_unused_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_904_: u8 = 0;
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_909_: u8 = 0;
    let mut v_ks_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: u8 = 0;
    let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v_reuseFailAlloc_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_921_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_849_) == 0 {
                    v_es_854_ = lean_ctor_get(v_x_849_, 0);
                    v___x_855_ = 5usize;
                    v___x_856_ = 1usize;
                    v___x_857_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_858_ = lean_usize_land(v_x_850_, v___x_857_);
                    v_j_859_ = lean_usize_to_nat(v___x_858_);
                    v___x_860_ = lean_array_get_size(v_es_854_);
                    v___x_861_ = lean_nat_dec_lt(v_j_859_, v___x_860_);
                    if v___x_861_ == 0 {
                        lean_dec(v_j_859_);
                        lean_dec(v_x_853_);
                        lean_dec_ref(v_x_852_);
                        return v_x_849_;
                    } else {
                        lean_inc_ref(v_es_854_);
                        v_isSharedCheck_898_ = (!lean_is_exclusive(v_x_849_)) as u8;
                        if v_isSharedCheck_898_ == 0 {
                            v_unused_899_ = lean_ctor_get(v_x_849_, 0);
                            lean_dec(v_unused_899_);
                            v___x_863_ = v_x_849_;
                            v_isShared_864_ = v_isSharedCheck_898_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_849_);
                            v___x_863_ = lean_box(0);
                            v_isShared_864_ = v_isSharedCheck_898_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_900_ = lean_ctor_get(v_x_849_, 0);
                    v_vs_901_ = lean_ctor_get(v_x_849_, 1);
                    v_isSharedCheck_921_ = (!lean_is_exclusive(v_x_849_)) as u8;
                    if v_isSharedCheck_921_ == 0 {
                        v___x_903_ = v_x_849_;
                        v_isShared_904_ = v_isSharedCheck_921_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_901_);
                        lean_inc(v_ks_900_);
                        lean_dec(v_x_849_);
                        v___x_903_ = lean_box(0);
                        v_isShared_904_ = v_isSharedCheck_921_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_865_ = lean_array_fget(v_es_854_, v_j_859_);
                v___x_866_ = lean_box(0);
                v_xs_x27_867_ = lean_array_fset(v_es_854_, v_j_859_, v___x_866_);
                match lean_obj_tag(v_v_865_) {
                    0 => {
                        v_key_874_ = lean_ctor_get(v_v_865_, 0);
                        v_val_875_ = lean_ctor_get(v_v_865_, 1);
                        v_isSharedCheck_885_ = (!lean_is_exclusive(v_v_865_)) as u8;
                        if v_isSharedCheck_885_ == 0 {
                            v___x_877_ = v_v_865_;
                            v_isShared_878_ = v_isSharedCheck_885_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_875_);
                            lean_inc(v_key_874_);
                            lean_dec(v_v_865_);
                            v___x_877_ = lean_box(0);
                            v_isShared_878_ = v_isSharedCheck_885_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_886_ = lean_ctor_get(v_v_865_, 0);
                        v_isSharedCheck_896_ = (!lean_is_exclusive(v_v_865_)) as u8;
                        if v_isSharedCheck_896_ == 0 {
                            v___x_888_ = v_v_865_;
                            v_isShared_889_ = v_isSharedCheck_896_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_886_);
                            lean_dec(v_v_865_);
                            v___x_888_ = lean_box(0);
                            v_isShared_889_ = v_isSharedCheck_896_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_897_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_897_, 0, v_x_852_);
                        lean_ctor_set(v___x_897_, 1, v_x_853_);
                        v___y_869_ = v___x_897_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_870_ = lean_array_fset(v_xs_x27_867_, v_j_859_, v___y_869_);
                lean_dec(v_j_859_);
                if v_isShared_864_ == 0 {
                    lean_ctor_set(v___x_863_, 0, v___x_870_);
                    v___x_872_ = v___x_863_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_872_;
            }
            4 => {
                v___x_879_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_852_, v_key_874_,
                    );
                if v___x_879_ == 0 {
                    lean_del_object(v___x_877_);
                    v___x_880_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_874_, v_val_875_, v_x_852_, v_x_853_,
                    );
                    v___x_881_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_881_, 0, v___x_880_);
                    v___y_869_ = v___x_881_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_875_);
                    lean_dec(v_key_874_);
                    if v_isShared_878_ == 0 {
                        lean_ctor_set(v___x_877_, 1, v_x_853_);
                        lean_ctor_set(v___x_877_, 0, v_x_852_);
                        v___x_883_ = v___x_877_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_884_, 0, v_x_852_);
                        lean_ctor_set(v_reuseFailAlloc_884_, 1, v_x_853_);
                        v___x_883_ = v_reuseFailAlloc_884_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_869_ = v___x_883_;
                state = 2;
                continue;
            }
            6 => {
                v___x_890_ = lean_usize_shift_right(v_x_850_, v___x_855_);
                v___x_891_ = lean_usize_add(v_x_851_, v___x_856_);
                v___x_892_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(v_node_886_, v___x_890_, v___x_891_, v_x_852_, v_x_853_);
                if v_isShared_889_ == 0 {
                    lean_ctor_set(v___x_888_, 0, v___x_892_);
                    v___x_894_ = v___x_888_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_895_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_892_);
                    v___x_894_ = v_reuseFailAlloc_895_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_869_ = v___x_894_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_904_ == 0 {
                    v___x_906_ = v___x_903_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_920_, 0, v_ks_900_);
                    lean_ctor_set(v_reuseFailAlloc_920_, 1, v_vs_901_);
                    v___x_906_ = v_reuseFailAlloc_920_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_907_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v___x_906_, v_x_852_, v_x_853_);
                v___x_915_ = 7usize;
                v___x_916_ = lean_usize_dec_le(v___x_915_, v_x_851_);
                if v___x_916_ == 0 {
                    v___x_917_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_907_);
                    v___x_918_ = lean_unsigned_to_nat(4);
                    v___x_919_ = lean_nat_dec_lt(v___x_917_, v___x_918_);
                    lean_dec(v___x_917_);
                    v___y_909_ = v___x_919_;
                    state = 10;
                    continue;
                } else {
                    v___y_909_ = v___x_916_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_909_ == 0 {
                    v_ks_910_ = lean_ctor_get(v_newNode_907_, 0);
                    lean_inc_ref(v_ks_910_);
                    v_vs_911_ = lean_ctor_get(v_newNode_907_, 1);
                    lean_inc_ref(v_vs_911_);
                    lean_dec_ref(v_newNode_907_);
                    v___x_912_ = lean_unsigned_to_nat(0);
                    v___x_913_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__2);
                    v___x_914_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_x_851_, v_ks_910_, v_vs_911_, v___x_912_, v___x_913_);
                    lean_dec_ref(v_vs_911_);
                    lean_dec_ref(v_ks_910_);
                    return v___x_914_;
                } else {
                    return v_newNode_907_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___redArg(
    mut v_depth_922_: usize,
    mut v_keys_923_: *mut LeanObject,
    mut v_vals_924_: *mut LeanObject,
    mut v_i_925_: *mut LeanObject,
    mut v_entries_926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: u8 = 0;
    let mut v_k_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u64 = 0;
    let mut v_h_932_: usize = 0;
    let mut v___x_933_: usize = 0;
    let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: usize = 0;
    let mut v___x_936_: usize = 0;
    let mut v___x_937_: usize = 0;
    let mut v_h_938_: usize = 0;
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_927_ = lean_array_get_size(v_keys_923_);
                v___x_928_ = lean_nat_dec_lt(v_i_925_, v___x_927_);
                if v___x_928_ == 0 {
                    lean_dec(v_i_925_);
                    return v_entries_926_;
                } else {
                    v_k_929_ = lean_array_fget_borrowed(v_keys_923_, v_i_925_);
                    v_v_930_ = lean_array_fget_borrowed(v_vals_924_, v_i_925_);
                    v___x_931_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_929_);
                    v_h_932_ = lean_uint64_to_usize(v___x_931_);
                    v___x_933_ = 5usize;
                    v___x_934_ = lean_unsigned_to_nat(1);
                    v___x_935_ = 1usize;
                    v___x_936_ = lean_usize_sub(v_depth_922_, v___x_935_);
                    v___x_937_ = lean_usize_mul(v___x_933_, v___x_936_);
                    v_h_938_ = lean_usize_shift_right(v_h_932_, v___x_937_);
                    v___x_939_ = lean_nat_add(v_i_925_, v___x_934_);
                    lean_dec(v_i_925_);
                    lean_inc(v_v_930_);
                    lean_inc(v_k_929_);
                    v___x_940_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(v_entries_926_, v_h_938_, v_depth_922_, v_k_929_, v_v_930_);
                    v_i_925_ = v___x_939_;
                    v_entries_926_ = v___x_940_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___redArg___boxed(
    mut v_depth_942_: *mut LeanObject,
    mut v_keys_943_: *mut LeanObject,
    mut v_vals_944_: *mut LeanObject,
    mut v_i_945_: *mut LeanObject,
    mut v_entries_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_947_: usize = 0;
    let mut v_res_948_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_947_ = lean_unbox_usize(v_depth_942_);
    lean_dec(v_depth_942_);
    v_res_948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_boxed_947_, v_keys_943_, v_vals_944_, v_i_945_, v_entries_946_);
    lean_dec_ref(v_vals_944_);
    lean_dec_ref(v_keys_943_);
    return v_res_948_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_949_: *mut LeanObject,
    mut v_x_950_: *mut LeanObject,
    mut v_x_951_: *mut LeanObject,
    mut v_x_952_: *mut LeanObject,
    mut v_x_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4452__boxed_954_: usize = 0;
    let mut v_x_4453__boxed_955_: usize = 0;
    let mut v_res_956_: *mut LeanObject = core::ptr::null_mut();
    v_x_4452__boxed_954_ = lean_unbox_usize(v_x_950_);
    lean_dec(v_x_950_);
    v_x_4453__boxed_955_ = lean_unbox_usize(v_x_951_);
    lean_dec(v_x_951_);
    v_res_956_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(v_x_949_, v_x_4452__boxed_954_, v_x_4453__boxed_955_, v_x_952_, v_x_953_);
    return v_res_956_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1___redArg(
    mut v_x_957_: *mut LeanObject,
    mut v_x_958_: *mut LeanObject,
    mut v_x_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_960_: u64 = 0;
    let mut v___x_961_: usize = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    v___x_960_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_958_);
    v___x_961_ = lean_uint64_to_usize(v___x_960_);
    v___x_962_ = 1usize;
    v___x_963_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(v_x_957_, v___x_961_, v___x_962_, v_x_958_, v_x_959_);
    return v___x_963_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_964_: *mut LeanObject,
    mut v_vals_965_: *mut LeanObject,
    mut v_i_966_: *mut LeanObject,
    mut v_k_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: u8 = 0;
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: u8 = 0;
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_968_ = lean_array_get_size(v_keys_964_);
                v___x_969_ = lean_nat_dec_lt(v_i_966_, v___x_968_);
                if v___x_969_ == 0 {
                    lean_dec(v_i_966_);
                    v___x_970_ = lean_box(0);
                    return v___x_970_;
                } else {
                    v_k_x27_971_ = lean_array_fget_borrowed(v_keys_964_, v_i_966_);
                    v___x_972_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_967_,
                            v_k_x27_971_,
                        );
                    if v___x_972_ == 0 {
                        v___x_973_ = lean_unsigned_to_nat(1);
                        v___x_974_ = lean_nat_add(v_i_966_, v___x_973_);
                        lean_dec(v_i_966_);
                        v_i_966_ = v___x_974_;
                        state = 0;
                        continue;
                    } else {
                        v___x_976_ = lean_array_fget_borrowed(v_vals_965_, v_i_966_);
                        lean_dec(v_i_966_);
                        lean_inc(v___x_976_);
                        v___x_977_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_977_, 0, v___x_976_);
                        return v___x_977_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_978_: *mut LeanObject,
    mut v_vals_979_: *mut LeanObject,
    mut v_i_980_: *mut LeanObject,
    mut v_k_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_978_, v_vals_979_, v_i_980_, v_k_981_);
    lean_dec_ref(v_k_981_);
    lean_dec_ref(v_vals_979_);
    lean_dec_ref(v_keys_978_);
    return v_res_982_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___redArg(
    mut v_x_983_: *mut LeanObject,
    mut v_x_984_: usize,
    mut v_x_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: usize = 0;
    let mut v___x_990_: usize = 0;
    let mut v_j_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: usize = 0;
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_983_) == 0 {
                    v_es_986_ = lean_ctor_get(v_x_983_, 0);
                    v___x_987_ = lean_box(2);
                    v___x_988_ = 5usize;
                    v___x_989_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg___closed__1);
                    v___x_990_ = lean_usize_land(v_x_984_, v___x_989_);
                    v_j_991_ = lean_usize_to_nat(v___x_990_);
                    v___x_992_ = lean_array_get_borrowed(v___x_987_, v_es_986_, v_j_991_);
                    lean_dec(v_j_991_);
                    match lean_obj_tag(v___x_992_) {
                        0 => {
                            v_key_993_ = lean_ctor_get(v___x_992_, 0);
                            v_val_994_ = lean_ctor_get(v___x_992_, 1);
                            v___x_995_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_985_, v_key_993_);
                            if v___x_995_ == 0 {
                                v___x_996_ = lean_box(0);
                                return v___x_996_;
                            } else {
                                lean_inc(v_val_994_);
                                v___x_997_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_997_, 0, v_val_994_);
                                return v___x_997_;
                            }
                        }
                        1 => {
                            v_node_998_ = lean_ctor_get(v___x_992_, 0);
                            v___x_999_ = lean_usize_shift_right(v_x_984_, v___x_988_);
                            v_x_983_ = v_node_998_;
                            v_x_984_ = v___x_999_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1001_ = lean_box(0);
                            return v___x_1001_;
                        }
                    }
                } else {
                    v_ks_1002_ = lean_ctor_get(v_x_983_, 0);
                    v_vs_1003_ = lean_ctor_get(v_x_983_, 1);
                    v___x_1004_ = lean_unsigned_to_nat(0);
                    v___x_1005_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1002_, v_vs_1003_, v___x_1004_, v_x_985_);
                    return v___x_1005_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1006_: *mut LeanObject,
    mut v_x_1007_: *mut LeanObject,
    mut v_x_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4652__boxed_1009_: usize = 0;
    let mut v_res_1010_: *mut LeanObject = core::ptr::null_mut();
    v_x_4652__boxed_1009_ = lean_unbox_usize(v_x_1007_);
    lean_dec(v_x_1007_);
    v_res_1010_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___redArg(v_x_1006_, v_x_4652__boxed_1009_, v_x_1008_);
    lean_dec_ref(v_x_1008_);
    lean_dec_ref(v_x_1006_);
    return v_res_1010_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___redArg(
    mut v_x_1011_: *mut LeanObject,
    mut v_x_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1013_: u64 = 0;
    let mut v___x_1014_: usize = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    v___x_1013_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1012_);
    v___x_1014_ = lean_uint64_to_usize(v___x_1013_);
    v___x_1015_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___redArg(v_x_1011_, v___x_1014_, v_x_1012_);
    return v___x_1015_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___redArg___boxed(
    mut v_x_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1018_: *mut LeanObject = core::ptr::null_mut();
    v_res_1018_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___redArg(v_x_1016_, v_x_1017_);
    lean_dec_ref(v_x_1017_);
    lean_dec_ref(v_x_1016_);
    return v_res_1018_;
}
pub unsafe fn l_Lean_Meta_Grind_getReflCmpThm_x3f___redArg(
    mut v_op_1019_: *mut LeanObject,
    mut v_a_1020_: *mut LeanObject,
    mut v_a_1021_: *mut LeanObject,
    mut v_a_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1032_: u8 = 0;
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1036_: u8 = 0;
    let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1041_: u8 = 0;
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_congrThms_1043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simp_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lastTag_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_counters_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_splitDiags_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ematchDiags_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulEqCmpMap_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reflCmpMap_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_anchors_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_instanceMap_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1064_: u8 = 0;
    let mut v_isSharedCheck_1065_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1026_ = lean_st_ref_get(v_a_1020_);
                v_reflCmpMap_1027_ = lean_ctor_get(v___x_1026_, 7);
                lean_inc_ref(v_reflCmpMap_1027_);
                lean_dec(v___x_1026_);
                v___x_1028_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___redArg(v_reflCmpMap_1027_, v_op_1019_);
                lean_dec_ref(v_reflCmpMap_1027_);
                if lean_obj_tag(v___x_1028_) == 1 {
                    lean_dec_ref(v_op_1019_);
                    v_val_1029_ = lean_ctor_get(v___x_1028_, 0);
                    v_isSharedCheck_1036_ = (!lean_is_exclusive(v___x_1028_)) as u8;
                    if v_isSharedCheck_1036_ == 0 {
                        v___x_1031_ = v___x_1028_;
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1029_);
                        lean_dec(v___x_1028_);
                        v___x_1031_ = lean_box(0);
                        v_isShared_1032_ = v_isSharedCheck_1036_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_1028_);
                    lean_inc_ref(v_op_1019_);
                    v___x_1037_ = l___private_Lean_Meta_Tactic_Grind_ReflCmp_0__Lean_Meta_Grind_getReflCmpThm_x3f_go_x3f(v_op_1019_, v_a_1021_, v_a_1022_, v_a_1023_, v_a_1024_);
                    if lean_obj_tag(v___x_1037_) == 0 {
                        v_a_1038_ = lean_ctor_get(v___x_1037_, 0);
                        v_isSharedCheck_1065_ = (!lean_is_exclusive(v___x_1037_)) as u8;
                        if v_isSharedCheck_1065_ == 0 {
                            v___x_1040_ = v___x_1037_;
                            v_isShared_1041_ = v_isSharedCheck_1065_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1038_);
                            lean_dec(v___x_1037_);
                            v___x_1040_ = lean_box(0);
                            v_isShared_1041_ = v_isSharedCheck_1065_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_op_1019_);
                        return v___x_1037_;
                    }
                }
            }
            1 => {
                if v_isShared_1032_ == 0 {
                    lean_ctor_set_tag(v___x_1031_, 0);
                    v___x_1034_ = v___x_1031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1035_, 0, v_val_1029_);
                    v___x_1034_ = v_reuseFailAlloc_1035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1034_;
            }
            3 => {
                v___x_1042_ = lean_st_ref_take(v_a_1020_);
                v_congrThms_1043_ = lean_ctor_get(v___x_1042_, 0);
                v_simp_1044_ = lean_ctor_get(v___x_1042_, 1);
                v_lastTag_1045_ = lean_ctor_get(v___x_1042_, 2);
                v_counters_1046_ = lean_ctor_get(v___x_1042_, 3);
                v_splitDiags_1047_ = lean_ctor_get(v___x_1042_, 4);
                v_ematchDiags_1048_ = lean_ctor_get(v___x_1042_, 5);
                v_lawfulEqCmpMap_1049_ = lean_ctor_get(v___x_1042_, 6);
                v_reflCmpMap_1050_ = lean_ctor_get(v___x_1042_, 7);
                v_anchors_1051_ = lean_ctor_get(v___x_1042_, 8);
                v_instanceMap_1052_ = lean_ctor_get(v___x_1042_, 9);
                v_isSharedCheck_1064_ = (!lean_is_exclusive(v___x_1042_)) as u8;
                if v_isSharedCheck_1064_ == 0 {
                    v___x_1054_ = v___x_1042_;
                    v_isShared_1055_ = v_isSharedCheck_1064_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_instanceMap_1052_);
                    lean_inc(v_anchors_1051_);
                    lean_inc(v_reflCmpMap_1050_);
                    lean_inc(v_lawfulEqCmpMap_1049_);
                    lean_inc(v_ematchDiags_1048_);
                    lean_inc(v_splitDiags_1047_);
                    lean_inc(v_counters_1046_);
                    lean_inc(v_lastTag_1045_);
                    lean_inc(v_simp_1044_);
                    lean_inc(v_congrThms_1043_);
                    lean_dec(v___x_1042_);
                    v___x_1054_ = lean_box(0);
                    v_isShared_1055_ = v_isSharedCheck_1064_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_1038_);
                v___x_1056_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1___redArg(v_reflCmpMap_1050_, v_op_1019_, v_a_1038_);
                if v_isShared_1055_ == 0 {
                    lean_ctor_set(v___x_1054_, 7, v___x_1056_);
                    v___x_1058_ = v___x_1054_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1063_ = lean_alloc_ctor(0, 10, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 0, v_congrThms_1043_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 1, v_simp_1044_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 2, v_lastTag_1045_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 3, v_counters_1046_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 4, v_splitDiags_1047_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 5, v_ematchDiags_1048_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 6, v_lawfulEqCmpMap_1049_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 7, v___x_1056_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 8, v_anchors_1051_);
                    lean_ctor_set(v_reuseFailAlloc_1063_, 9, v_instanceMap_1052_);
                    v___x_1058_ = v_reuseFailAlloc_1063_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_1059_ = lean_st_ref_set(v_a_1020_, v___x_1058_);
                if v_isShared_1041_ == 0 {
                    v___x_1061_ = v___x_1040_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1062_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1062_, 0, v_a_1038_);
                    v___x_1061_ = v_reuseFailAlloc_1062_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_getReflCmpThm_x3f___redArg___boxed(
    mut v_op_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
    mut v_a_1070_: *mut LeanObject,
    mut v_a_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1073_: *mut LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_Lean_Meta_Grind_getReflCmpThm_x3f___redArg(
        v_op_1066_, v_a_1067_, v_a_1068_, v_a_1069_, v_a_1070_, v_a_1071_,
    );
    lean_dec(v_a_1071_);
    lean_dec_ref(v_a_1070_);
    lean_dec(v_a_1069_);
    lean_dec_ref(v_a_1068_);
    lean_dec(v_a_1067_);
    return v_res_1073_;
}
pub unsafe fn l_Lean_Meta_Grind_getReflCmpThm_x3f(
    mut v_op_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
    mut v_a_1077_: *mut LeanObject,
    mut v_a_1078_: *mut LeanObject,
    mut v_a_1079_: *mut LeanObject,
    mut v_a_1080_: *mut LeanObject,
    mut v_a_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_a_1083_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1085_: *mut LeanObject = core::ptr::null_mut();
    v___x_1085_ = l_Lean_Meta_Grind_getReflCmpThm_x3f___redArg(
        v_op_1074_, v_a_1077_, v_a_1080_, v_a_1081_, v_a_1082_, v_a_1083_,
    );
    return v___x_1085_;
}
pub unsafe fn l_Lean_Meta_Grind_getReflCmpThm_x3f___boxed(
    mut v_op_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
    mut v_a_1091_: *mut LeanObject,
    mut v_a_1092_: *mut LeanObject,
    mut v_a_1093_: *mut LeanObject,
    mut v_a_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
    mut v_a_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1097_: *mut LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Lean_Meta_Grind_getReflCmpThm_x3f(
        v_op_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_,
        v_a_1094_, v_a_1095_,
    );
    lean_dec(v_a_1095_);
    lean_dec_ref(v_a_1094_);
    lean_dec(v_a_1093_);
    lean_dec_ref(v_a_1092_);
    lean_dec(v_a_1091_);
    lean_dec_ref(v_a_1090_);
    lean_dec(v_a_1089_);
    lean_dec_ref(v_a_1088_);
    lean_dec(v_a_1087_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0(
    mut v_00_u03b2_1098_: *mut LeanObject,
    mut v_x_1099_: *mut LeanObject,
    mut v_x_1100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    v___x_1101_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___redArg(v_x_1099_, v_x_1100_);
    return v___x_1101_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0___boxed(
    mut v_00_u03b2_1102_: *mut LeanObject,
    mut v_x_1103_: *mut LeanObject,
    mut v_x_1104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1105_: *mut LeanObject = core::ptr::null_mut();
    v_res_1105_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0(
            v_00_u03b2_1102_,
            v_x_1103_,
            v_x_1104_,
        );
    lean_dec_ref(v_x_1104_);
    lean_dec_ref(v_x_1103_);
    return v_res_1105_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1(
    mut v_00_u03b2_1106_: *mut LeanObject,
    mut v_x_1107_: *mut LeanObject,
    mut v_x_1108_: *mut LeanObject,
    mut v_x_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    v___x_1110_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1___redArg(
            v_x_1107_, v_x_1108_, v_x_1109_,
        );
    return v___x_1110_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0(
    mut v_00_u03b2_1111_: *mut LeanObject,
    mut v_x_1112_: *mut LeanObject,
    mut v_x_1113_: usize,
    mut v_x_1114_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    v___x_1115_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___redArg(v_x_1112_, v_x_1113_, v_x_1114_);
    return v___x_1115_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1116_: *mut LeanObject,
    mut v_x_1117_: *mut LeanObject,
    mut v_x_1118_: *mut LeanObject,
    mut v_x_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4796__boxed_1120_: usize = 0;
    let mut v_res_1121_: *mut LeanObject = core::ptr::null_mut();
    v_x_4796__boxed_1120_ = lean_unbox_usize(v_x_1118_);
    lean_dec(v_x_1118_);
    v_res_1121_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0(v_00_u03b2_1116_, v_x_1117_, v_x_4796__boxed_1120_, v_x_1119_);
    lean_dec_ref(v_x_1119_);
    lean_dec_ref(v_x_1117_);
    return v_res_1121_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2(
    mut v_00_u03b2_1122_: *mut LeanObject,
    mut v_x_1123_: *mut LeanObject,
    mut v_x_1124_: usize,
    mut v_x_1125_: usize,
    mut v_x_1126_: *mut LeanObject,
    mut v_x_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    v___x_1128_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___redArg(v_x_1123_, v_x_1124_, v_x_1125_, v_x_1126_, v_x_1127_);
    return v___x_1128_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_1129_: *mut LeanObject,
    mut v_x_1130_: *mut LeanObject,
    mut v_x_1131_: *mut LeanObject,
    mut v_x_1132_: *mut LeanObject,
    mut v_x_1133_: *mut LeanObject,
    mut v_x_1134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4807__boxed_1135_: usize = 0;
    let mut v_x_4808__boxed_1136_: usize = 0;
    let mut v_res_1137_: *mut LeanObject = core::ptr::null_mut();
    v_x_4807__boxed_1135_ = lean_unbox_usize(v_x_1131_);
    lean_dec(v_x_1131_);
    v_x_4808__boxed_1136_ = lean_unbox_usize(v_x_1132_);
    lean_dec(v_x_1132_);
    v_res_1137_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2(v_00_u03b2_1129_, v_x_1130_, v_x_4807__boxed_1135_, v_x_4808__boxed_1136_, v_x_1133_, v_x_1134_);
    return v_res_1137_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1138_: *mut LeanObject,
    mut v_keys_1139_: *mut LeanObject,
    mut v_vals_1140_: *mut LeanObject,
    mut v_heq_1141_: *mut LeanObject,
    mut v_i_1142_: *mut LeanObject,
    mut v_k_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1144_: *mut LeanObject = core::ptr::null_mut();
    v___x_1144_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1139_, v_vals_1140_, v_i_1142_, v_k_1143_);
    return v___x_1144_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1145_: *mut LeanObject,
    mut v_keys_1146_: *mut LeanObject,
    mut v_vals_1147_: *mut LeanObject,
    mut v_heq_1148_: *mut LeanObject,
    mut v_i_1149_: *mut LeanObject,
    mut v_k_1150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1151_: *mut LeanObject = core::ptr::null_mut();
    v_res_1151_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1145_, v_keys_1146_, v_vals_1147_, v_heq_1148_, v_i_1149_, v_k_1150_);
    lean_dec_ref(v_k_1150_);
    lean_dec_ref(v_vals_1147_);
    lean_dec_ref(v_keys_1146_);
    return v_res_1151_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4(
    mut v_00_u03b2_1152_: *mut LeanObject,
    mut v_n_1153_: *mut LeanObject,
    mut v_k_1154_: *mut LeanObject,
    mut v_v_1155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1156_: *mut LeanObject = core::ptr::null_mut();
    v___x_1156_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4___redArg(v_n_1153_, v_k_1154_, v_v_1155_);
    return v___x_1156_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5(
    mut v_00_u03b2_1157_: *mut LeanObject,
    mut v_depth_1158_: usize,
    mut v_keys_1159_: *mut LeanObject,
    mut v_vals_1160_: *mut LeanObject,
    mut v_heq_1161_: *mut LeanObject,
    mut v_i_1162_: *mut LeanObject,
    mut v_entries_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
    v___x_1164_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___redArg(v_depth_1158_, v_keys_1159_, v_vals_1160_, v_i_1162_, v_entries_1163_);
    return v___x_1164_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5___boxed(
    mut v_00_u03b2_1165_: *mut LeanObject,
    mut v_depth_1166_: *mut LeanObject,
    mut v_keys_1167_: *mut LeanObject,
    mut v_vals_1168_: *mut LeanObject,
    mut v_heq_1169_: *mut LeanObject,
    mut v_i_1170_: *mut LeanObject,
    mut v_entries_1171_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1172_: usize = 0;
    let mut v_res_1173_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1172_ = lean_unbox_usize(v_depth_1166_);
    lean_dec(v_depth_1166_);
    v_res_1173_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__5(v_00_u03b2_1165_, v_depth_boxed_1172_, v_keys_1167_, v_vals_1168_, v_heq_1169_, v_i_1170_, v_entries_1171_);
    lean_dec_ref(v_vals_1168_);
    lean_dec_ref(v_keys_1167_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1174_: *mut LeanObject,
    mut v_x_1175_: *mut LeanObject,
    mut v_x_1176_: *mut LeanObject,
    mut v_x_1177_: *mut LeanObject,
    mut v_x_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
    v___x_1179_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_getReflCmpThm_x3f_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1175_, v_x_1176_, v_x_1177_, v_x_1178_);
    return v___x_1179_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateReflCmp(
    mut v_e_1180_: *mut LeanObject,
    mut v_a_1181_: *mut LeanObject,
    mut v_a_1182_: *mut LeanObject,
    mut v_a_1183_: *mut LeanObject,
    mut v_a_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
    mut v_a_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1198_: u8 = 0;
    let mut v_val_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1207_: u8 = 0;
    let mut v___x_1208_: u8 = 0;
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: u8 = 0;
    let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1223_: u8 = 0;
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1227_: u8 = 0;
    let mut v_a_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1231_: u8 = 0;
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_isSharedCheck_1236_: u8 = 0;
    let mut v_a_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1244_: u8 = 0;
    let mut v___x_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut v_a_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1192_ = l_Lean_Meta_Grind_getBinOp(v_e_1180_);
                if lean_obj_tag(v___x_1192_) == 1 {
                    v_val_1193_ = lean_ctor_get(v___x_1192_, 0);
                    lean_inc(v_val_1193_);
                    lean_dec_ref_known(v___x_1192_, 1);
                    v___x_1194_ = l_Lean_Meta_Grind_getReflCmpThm_x3f___redArg(
                        v_val_1193_,
                        v_a_1184_,
                        v_a_1187_,
                        v_a_1188_,
                        v_a_1189_,
                        v_a_1190_,
                    );
                    if lean_obj_tag(v___x_1194_) == 0 {
                        v_a_1195_ = lean_ctor_get(v___x_1194_, 0);
                        v_isSharedCheck_1249_ = (!lean_is_exclusive(v___x_1194_)) as u8;
                        if v_isSharedCheck_1249_ == 0 {
                            v___x_1197_ = v___x_1194_;
                            v_isShared_1198_ = v_isSharedCheck_1249_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1195_);
                            lean_dec(v___x_1194_);
                            v___x_1197_ = lean_box(0);
                            v_isShared_1198_ = v_isSharedCheck_1249_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_1180_);
                        v_a_1250_ = lean_ctor_get(v___x_1194_, 0);
                        v_isSharedCheck_1257_ = (!lean_is_exclusive(v___x_1194_)) as u8;
                        if v_isSharedCheck_1257_ == 0 {
                            v___x_1252_ = v___x_1194_;
                            v_isShared_1253_ = v_isSharedCheck_1257_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_1250_);
                            lean_dec(v___x_1194_);
                            v___x_1252_ = lean_box(0);
                            v_isShared_1253_ = v_isSharedCheck_1257_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_1192_);
                    lean_dec_ref(v_e_1180_);
                    v___x_1258_ = lean_box(0);
                    v___x_1259_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1259_, 0, v___x_1258_);
                    return v___x_1259_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1195_) == 1 {
                    lean_del_object(v___x_1197_);
                    v_val_1199_ = lean_ctor_get(v_a_1195_, 0);
                    lean_inc(v_val_1199_);
                    lean_dec_ref_known(v_a_1195_, 1);
                    v___x_1200_ = l_Lean_Expr_appFn_x21(v_e_1180_);
                    v___x_1201_ = l_Lean_Expr_appArg_x21(v___x_1200_);
                    lean_dec_ref(v___x_1200_);
                    v___x_1202_ = l_Lean_Expr_appArg_x21(v_e_1180_);
                    v___x_1203_ =
                        l_Lean_Meta_Grind_isEqv___redArg(v___x_1201_, v___x_1202_, v_a_1181_);
                    if lean_obj_tag(v___x_1203_) == 0 {
                        v_a_1204_ = lean_ctor_get(v___x_1203_, 0);
                        v_isSharedCheck_1236_ = (!lean_is_exclusive(v___x_1203_)) as u8;
                        if v_isSharedCheck_1236_ == 0 {
                            v___x_1206_ = v___x_1203_;
                            v_isShared_1207_ = v_isSharedCheck_1236_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1204_);
                            lean_dec(v___x_1203_);
                            v___x_1206_ = lean_box(0);
                            v_isShared_1207_ = v_isSharedCheck_1236_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_1202_);
                        lean_dec_ref(v___x_1201_);
                        lean_dec(v_val_1199_);
                        lean_dec_ref(v_e_1180_);
                        v_a_1237_ = lean_ctor_get(v___x_1203_, 0);
                        v_isSharedCheck_1244_ = (!lean_is_exclusive(v___x_1203_)) as u8;
                        if v_isSharedCheck_1244_ == 0 {
                            v___x_1239_ = v___x_1203_;
                            v_isShared_1240_ = v_isSharedCheck_1244_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_1237_);
                            lean_dec(v___x_1203_);
                            v___x_1239_ = lean_box(0);
                            v_isShared_1240_ = v_isSharedCheck_1244_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1195_);
                    lean_dec_ref(v_e_1180_);
                    v___x_1245_ = lean_box(0);
                    if v_isShared_1198_ == 0 {
                        lean_ctor_set(v___x_1197_, 0, v___x_1245_);
                        v___x_1247_ = v___x_1197_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1248_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
                        v___x_1247_ = v_reuseFailAlloc_1248_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1208_ = (lean_unbox(v_a_1204_) as u8);
                lean_dec(v_a_1204_);
                if v___x_1208_ == 0 {
                    lean_dec_ref(v___x_1202_);
                    lean_dec_ref(v___x_1201_);
                    lean_dec(v_val_1199_);
                    lean_dec_ref(v_e_1180_);
                    v___x_1209_ = lean_box(0);
                    if v_isShared_1207_ == 0 {
                        lean_ctor_set(v___x_1206_, 0, v___x_1209_);
                        v___x_1211_ = v___x_1206_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1212_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1212_, 0, v___x_1209_);
                        v___x_1211_ = v_reuseFailAlloc_1212_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1206_);
                    v___x_1213_ = l_Lean_Meta_Sym_getOrderingEqExpr___redArg(v_a_1185_);
                    if lean_obj_tag(v___x_1213_) == 0 {
                        v_a_1214_ = lean_ctor_get(v___x_1213_, 0);
                        lean_inc(v_a_1214_);
                        lean_dec_ref_known(v___x_1213_, 1);
                        lean_inc(v_a_1190_);
                        lean_inc_ref(v_a_1189_);
                        lean_inc(v_a_1188_);
                        lean_inc_ref(v_a_1187_);
                        lean_inc(v_a_1186_);
                        lean_inc_ref(v_a_1185_);
                        lean_inc(v_a_1184_);
                        lean_inc_ref(v_a_1183_);
                        lean_inc(v_a_1182_);
                        lean_inc(v_a_1181_);
                        lean_inc_ref(v___x_1202_);
                        lean_inc_ref(v___x_1201_);
                        v___x_1215_ = lean_grind_mk_eq_proof(
                            v___x_1201_,
                            v___x_1202_,
                            v_a_1181_,
                            v_a_1182_,
                            v_a_1183_,
                            v_a_1184_,
                            v_a_1185_,
                            v_a_1186_,
                            v_a_1187_,
                            v_a_1188_,
                            v_a_1189_,
                            v_a_1190_,
                        );
                        if lean_obj_tag(v___x_1215_) == 0 {
                            v_a_1216_ = lean_ctor_get(v___x_1215_, 0);
                            lean_inc(v_a_1216_);
                            lean_dec_ref_known(v___x_1215_, 1);
                            v___x_1217_ =
                                l_Lean_mkApp3(v_val_1199_, v___x_1201_, v___x_1202_, v_a_1216_);
                            v___x_1218_ = 0;
                            v___x_1219_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                v_e_1180_,
                                v_a_1214_,
                                v___x_1217_,
                                v___x_1218_,
                                v_a_1181_,
                                v_a_1183_,
                                v_a_1187_,
                                v_a_1188_,
                                v_a_1189_,
                                v_a_1190_,
                            );
                            return v___x_1219_;
                        } else {
                            lean_dec(v_a_1214_);
                            lean_dec_ref(v___x_1202_);
                            lean_dec_ref(v___x_1201_);
                            lean_dec(v_val_1199_);
                            lean_dec_ref(v_e_1180_);
                            v_a_1220_ = lean_ctor_get(v___x_1215_, 0);
                            v_isSharedCheck_1227_ = (!lean_is_exclusive(v___x_1215_)) as u8;
                            if v_isSharedCheck_1227_ == 0 {
                                v___x_1222_ = v___x_1215_;
                                v_isShared_1223_ = v_isSharedCheck_1227_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1220_);
                                lean_dec(v___x_1215_);
                                v___x_1222_ = lean_box(0);
                                v_isShared_1223_ = v_isSharedCheck_1227_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_1202_);
                        lean_dec_ref(v___x_1201_);
                        lean_dec(v_val_1199_);
                        lean_dec_ref(v_e_1180_);
                        v_a_1228_ = lean_ctor_get(v___x_1213_, 0);
                        v_isSharedCheck_1235_ = (!lean_is_exclusive(v___x_1213_)) as u8;
                        if v_isSharedCheck_1235_ == 0 {
                            v___x_1230_ = v___x_1213_;
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1228_);
                            lean_dec(v___x_1213_);
                            v___x_1230_ = lean_box(0);
                            v_isShared_1231_ = v_isSharedCheck_1235_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            3 => {
                return v___x_1211_;
            }
            4 => {
                if v_isShared_1223_ == 0 {
                    v___x_1225_ = v___x_1222_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1226_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1226_, 0, v_a_1220_);
                    v___x_1225_ = v_reuseFailAlloc_1226_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1225_;
            }
            6 => {
                if v_isShared_1231_ == 0 {
                    v___x_1233_ = v___x_1230_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_a_1228_);
                    v___x_1233_ = v_reuseFailAlloc_1234_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1233_;
            }
            8 => {
                if v_isShared_1240_ == 0 {
                    v___x_1242_ = v___x_1239_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1243_, 0, v_a_1237_);
                    v___x_1242_ = v_reuseFailAlloc_1243_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1242_;
            }
            10 => {
                return v___x_1247_;
            }
            11 => {
                if v_isShared_1253_ == 0 {
                    v___x_1255_ = v___x_1252_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
                    v___x_1255_ = v_reuseFailAlloc_1256_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateReflCmp___boxed(
    mut v_e_1260_: *mut LeanObject,
    mut v_a_1261_: *mut LeanObject,
    mut v_a_1262_: *mut LeanObject,
    mut v_a_1263_: *mut LeanObject,
    mut v_a_1264_: *mut LeanObject,
    mut v_a_1265_: *mut LeanObject,
    mut v_a_1266_: *mut LeanObject,
    mut v_a_1267_: *mut LeanObject,
    mut v_a_1268_: *mut LeanObject,
    mut v_a_1269_: *mut LeanObject,
    mut v_a_1270_: *mut LeanObject,
    mut v_a_1271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1272_: *mut LeanObject = core::ptr::null_mut();
    v_res_1272_ = l_Lean_Meta_Grind_propagateReflCmp(
        v_e_1260_, v_a_1261_, v_a_1262_, v_a_1263_, v_a_1264_, v_a_1265_, v_a_1266_, v_a_1267_,
        v_a_1268_, v_a_1269_, v_a_1270_,
    );
    lean_dec(v_a_1270_);
    lean_dec_ref(v_a_1269_);
    lean_dec(v_a_1268_);
    lean_dec_ref(v_a_1267_);
    lean_dec(v_a_1266_);
    lean_dec_ref(v_a_1265_);
    lean_dec(v_a_1264_);
    lean_dec_ref(v_a_1263_);
    lean_dec(v_a_1262_);
    lean_dec(v_a_1261_);
    return v_res_1272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_SynthInstance(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_ReflCmp(builtin);
}

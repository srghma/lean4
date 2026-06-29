// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.SubExpr
// Imports: Lean.SubExpr
use crate::ffi::{
    lean_array_get_borrowed, lean_array_get_size, lean_expr_instantiate1, lean_mk_array,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
};
use crate::r#gen::Init::Prelude::{l_instInhabitedOfMonad___redArg, l_panic___redArg};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isPrefixOf;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg;
use crate::r#gen::Lean::Data::Options::{l_Lean_Options_empty, l_Lean_Options_mergeBy};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_appArg_x21,
    l_Lean_Expr_appFn_x21, l_Lean_Expr_binderInfo, l_Lean_Expr_bindingBody_x21,
    l_Lean_Expr_bindingDomain_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getBoundedAppFn, l_Lean_Expr_isApp, l_Lean_Expr_sort___override,
    l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_inferType___boxed, l_Lean_Meta_withLetDecl___redArg,
    l_Lean_Meta_withLocalDecl___redArg,
};
use crate::r#gen::Lean::SubExpr::{
    initialize_Lean_SubExpr, l_Lean_SubExpr_Pos_maxChildren, l_Lean_SubExpr_Pos_push,
    l_Lean_SubExpr_Pos_pushNaryArg, l_Lean_SubExpr_Pos_pushNaryFn, l_Lean_SubExpr_Pos_typeCoord,
    runtime_initialize_Lean_SubExpr,
};
use crate::r#gen::Std::Data::DTreeMap::Internal::Balancing::l_Std_DTreeMap_Internal_Impl_balance___redArg;
pub static l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value) as *mut crate::leanh::LeanObject,14231257465488249300 as *mut crate::leanh::LeanObject] };
static mut l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46,
        68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46,
        68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46,
        119, 105, 116, 104, 80, 114, 111, 106, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 77, 68, 97, 116, 97, 69, 120, 112, 114, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<54> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 86, 97, 114, 84, 121, 112, 101, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value: crate::leanh::LeanStringObject<52> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value: crate::leanh::LeanStringObject<51> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 66, 111, 100, 121, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(
    mut v_o_1240_: *mut crate::leanh::LeanObject,
    mut v_k_1241_: *mut crate::leanh::LeanObject,
    mut v_v_1242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1244_: u8 = 0;
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1243_ = crate::leanh::lean_ctor_get(v_o_1240_, 0);
                v_hasTrace_1244_ = crate::leanh::lean_ctor_get_uint8(
                    v_o_1240_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1257_ = (!crate::leanh::lean_is_exclusive(v_o_1240_)) as u8;
                if v_isSharedCheck_1257_ == 0 {
                    v___x_1246_ = v_o_1240_;
                    v_isShared_1247_ = v_isSharedCheck_1257_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_map_1243_);
                    crate::leanh::lean_dec(v_o_1240_);
                    v___x_1246_ = crate::leanh::lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_k_1241_);
                v___x_1248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1241_, v_v_1242_, v_map_1243_);
                if v_hasTrace_1244_ == 0 {
                    v___x_1249_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1;
                    v___x_1250_ = l_Lean_Name_isPrefixOf(v___x_1249_, v_k_1241_);
                    crate::leanh::lean_dec(v_k_1241_);
                    if v_isShared_1247_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1246_, 0, v___x_1248_);
                        v___x_1252_ = v___x_1246_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1253_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1248_);
                        v___x_1252_ = v_reuseFailAlloc_1253_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1241_);
                    if v_isShared_1247_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1246_, 0, v___x_1248_);
                        v___x_1255_ = v___x_1246_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1256_ = crate::leanh::lean_alloc_ctor(0, 1, (1) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1248_);
                        crate::leanh::lean_ctor_set_uint8(
                            v_reuseFailAlloc_1256_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                            v_hasTrace_1244_,
                        );
                        v___x_1255_ = v_reuseFailAlloc_1256_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1252_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_1250_,
                );
                return v___x_1252_;
            }
            3 => {
                return v___x_1255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(
    mut v_k_1258_: *mut crate::leanh::LeanObject,
    mut v_v_1259_: *mut crate::leanh::LeanObject,
    mut v_t_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1268_: u8 = 0;
    let mut v___x_1269_: u8 = 0;
    let mut v___x_1270_: u8 = 0;
    let mut v_impl_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v_size_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_unused_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_unused_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_unused_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v_k_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v_unused_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut v_unused_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_unused_1399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v_size_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_unused_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v_k_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut v_unused_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1260_) == 0 {
                    v_size_1261_ = crate::leanh::lean_ctor_get(v_t_1260_, 0);
                    v_k_1262_ = crate::leanh::lean_ctor_get(v_t_1260_, 1);
                    v_v_1263_ = crate::leanh::lean_ctor_get(v_t_1260_, 2);
                    v_l_1264_ = crate::leanh::lean_ctor_get(v_t_1260_, 3);
                    v_r_1265_ = crate::leanh::lean_ctor_get(v_t_1260_, 4);
                    v_isSharedCheck_1546_ = (!crate::leanh::lean_is_exclusive(v_t_1260_)) as u8;
                    if v_isSharedCheck_1546_ == 0 {
                        v___x_1267_ = v_t_1260_;
                        v_isShared_1268_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1265_);
                        crate::leanh::lean_inc(v_l_1264_);
                        crate::leanh::lean_inc(v_v_1263_);
                        crate::leanh::lean_inc(v_k_1262_);
                        crate::leanh::lean_inc(v_size_1261_);
                        crate::leanh::lean_dec(v_t_1260_);
                        v___x_1267_ = crate::leanh::lean_box(0);
                        v_isShared_1268_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1547_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1548_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1548_, 0, v___x_1547_);
                    crate::leanh::lean_ctor_set(v___x_1548_, 1, v_k_1258_);
                    crate::leanh::lean_ctor_set(v___x_1548_, 2, v_v_1259_);
                    crate::leanh::lean_ctor_set(v___x_1548_, 3, v_t_1260_);
                    crate::leanh::lean_ctor_set(v___x_1548_, 4, v_t_1260_);
                    return v___x_1548_;
                }
            }
            1 => {
                v___x_1269_ = lean_nat_dec_lt(v_k_1258_, v_k_1262_);
                if v___x_1269_ == 0 {
                    v___x_1270_ = lean_nat_dec_eq(v_k_1258_, v_k_1262_);
                    if v___x_1270_ == 0 {
                        crate::leanh::lean_dec(v_size_1261_);
                        v_impl_1271_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1258_, v_v_1259_, v_r_1265_);
                        v___x_1272_ = crate::leanh::lean_unsigned_to_nat(1);
                        if crate::leanh::lean_obj_tag(v_l_1264_) == 0 {
                            v_size_1273_ = crate::leanh::lean_ctor_get(v_l_1264_, 0);
                            v_size_1274_ = crate::leanh::lean_ctor_get(v_impl_1271_, 0);
                            crate::leanh::lean_inc(v_size_1274_);
                            v_k_1275_ = crate::leanh::lean_ctor_get(v_impl_1271_, 1);
                            crate::leanh::lean_inc(v_k_1275_);
                            v_v_1276_ = crate::leanh::lean_ctor_get(v_impl_1271_, 2);
                            crate::leanh::lean_inc(v_v_1276_);
                            v_l_1277_ = crate::leanh::lean_ctor_get(v_impl_1271_, 3);
                            crate::leanh::lean_inc(v_l_1277_);
                            v_r_1278_ = crate::leanh::lean_ctor_get(v_impl_1271_, 4);
                            crate::leanh::lean_inc(v_r_1278_);
                            v___x_1279_ = crate::leanh::lean_unsigned_to_nat(3);
                            v___x_1280_ = lean_nat_mul(v___x_1279_, v_size_1273_);
                            v___x_1281_ = lean_nat_dec_lt(v___x_1280_, v_size_1274_);
                            crate::leanh::lean_dec(v___x_1280_);
                            if v___x_1281_ == 0 {
                                crate::leanh::lean_dec(v_r_1278_);
                                crate::leanh::lean_dec(v_l_1277_);
                                crate::leanh::lean_dec(v_v_1276_);
                                crate::leanh::lean_dec(v_k_1275_);
                                v___x_1282_ = lean_nat_add(v___x_1272_, v_size_1273_);
                                v___x_1283_ = lean_nat_add(v___x_1282_, v_size_1274_);
                                crate::leanh::lean_dec(v_size_1274_);
                                crate::leanh::lean_dec(v___x_1282_);
                                if v_isShared_1268_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v_impl_1271_);
                                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1283_);
                                    v___x_1285_ = v___x_1267_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1286_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1286_,
                                        0,
                                        v___x_1283_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1286_,
                                        1,
                                        v_k_1262_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1286_,
                                        2,
                                        v_v_1263_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1286_,
                                        3,
                                        v_l_1264_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1286_,
                                        4,
                                        v_impl_1271_,
                                    );
                                    v___x_1285_ = v_reuseFailAlloc_1286_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1350_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1271_)) as u8;
                                if v_isSharedCheck_1350_ == 0 {
                                    v_unused_1351_ = crate::leanh::lean_ctor_get(v_impl_1271_, 4);
                                    crate::leanh::lean_dec(v_unused_1351_);
                                    v_unused_1352_ = crate::leanh::lean_ctor_get(v_impl_1271_, 3);
                                    crate::leanh::lean_dec(v_unused_1352_);
                                    v_unused_1353_ = crate::leanh::lean_ctor_get(v_impl_1271_, 2);
                                    crate::leanh::lean_dec(v_unused_1353_);
                                    v_unused_1354_ = crate::leanh::lean_ctor_get(v_impl_1271_, 1);
                                    crate::leanh::lean_dec(v_unused_1354_);
                                    v_unused_1355_ = crate::leanh::lean_ctor_get(v_impl_1271_, 0);
                                    crate::leanh::lean_dec(v_unused_1355_);
                                    v___x_1288_ = v_impl_1271_;
                                    v_isShared_1289_ = v_isSharedCheck_1350_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_impl_1271_);
                                    v___x_1288_ = crate::leanh::lean_box(0);
                                    v_isShared_1289_ = v_isSharedCheck_1350_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1356_ = crate::leanh::lean_ctor_get(v_impl_1271_, 3);
                            crate::leanh::lean_inc(v_l_1356_);
                            if crate::leanh::lean_obj_tag(v_l_1356_) == 0 {
                                v_r_1357_ = crate::leanh::lean_ctor_get(v_impl_1271_, 4);
                                v_k_1358_ = crate::leanh::lean_ctor_get(v_impl_1271_, 1);
                                v_v_1359_ = crate::leanh::lean_ctor_get(v_impl_1271_, 2);
                                v_isSharedCheck_1382_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1271_)) as u8;
                                if v_isSharedCheck_1382_ == 0 {
                                    v_unused_1383_ = crate::leanh::lean_ctor_get(v_impl_1271_, 3);
                                    crate::leanh::lean_dec(v_unused_1383_);
                                    v_unused_1384_ = crate::leanh::lean_ctor_get(v_impl_1271_, 0);
                                    crate::leanh::lean_dec(v_unused_1384_);
                                    v___x_1361_ = v_impl_1271_;
                                    v_isShared_1362_ = v_isSharedCheck_1382_;
                                    state = 13;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_r_1357_);
                                    crate::leanh::lean_inc(v_v_1359_);
                                    crate::leanh::lean_inc(v_k_1358_);
                                    crate::leanh::lean_dec(v_impl_1271_);
                                    v___x_1361_ = crate::leanh::lean_box(0);
                                    v_isShared_1362_ = v_isSharedCheck_1382_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1385_ = crate::leanh::lean_ctor_get(v_impl_1271_, 4);
                                crate::leanh::lean_inc(v_r_1385_);
                                if crate::leanh::lean_obj_tag(v_r_1385_) == 0 {
                                    v_k_1386_ = crate::leanh::lean_ctor_get(v_impl_1271_, 1);
                                    v_v_1387_ = crate::leanh::lean_ctor_get(v_impl_1271_, 2);
                                    v_isSharedCheck_1398_ =
                                        (!crate::leanh::lean_is_exclusive(v_impl_1271_)) as u8;
                                    if v_isSharedCheck_1398_ == 0 {
                                        v_unused_1399_ =
                                            crate::leanh::lean_ctor_get(v_impl_1271_, 4);
                                        crate::leanh::lean_dec(v_unused_1399_);
                                        v_unused_1400_ =
                                            crate::leanh::lean_ctor_get(v_impl_1271_, 3);
                                        crate::leanh::lean_dec(v_unused_1400_);
                                        v_unused_1401_ =
                                            crate::leanh::lean_ctor_get(v_impl_1271_, 0);
                                        crate::leanh::lean_dec(v_unused_1401_);
                                        v___x_1389_ = v_impl_1271_;
                                        v_isShared_1390_ = v_isSharedCheck_1398_;
                                        state = 18;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_v_1387_);
                                        crate::leanh::lean_inc(v_k_1386_);
                                        crate::leanh::lean_dec(v_impl_1271_);
                                        v___x_1389_ = crate::leanh::lean_box(0);
                                        v_isShared_1390_ = v_isSharedCheck_1398_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1402_ = crate::leanh::lean_unsigned_to_nat(2);
                                    if v_isShared_1268_ == 0 {
                                        crate::leanh::lean_ctor_set(v___x_1267_, 4, v_impl_1271_);
                                        crate::leanh::lean_ctor_set(v___x_1267_, 3, v_r_1385_);
                                        crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1402_);
                                        v___x_1404_ = v___x_1267_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1405_ =
                                            crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1405_,
                                            0,
                                            v___x_1402_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1405_,
                                            1,
                                            v_k_1262_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1405_,
                                            2,
                                            v_v_1263_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1405_,
                                            3,
                                            v_r_1385_,
                                        );
                                        crate::leanh::lean_ctor_set(
                                            v_reuseFailAlloc_1405_,
                                            4,
                                            v_impl_1271_,
                                        );
                                        v___x_1404_ = v_reuseFailAlloc_1405_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_v_1263_);
                        crate::leanh::lean_dec(v_k_1262_);
                        if v_isShared_1268_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1259_);
                            crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1258_);
                            v___x_1407_ = v___x_1267_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1408_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_size_1261_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1258_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1259_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_l_1264_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1265_);
                            v___x_1407_ = v_reuseFailAlloc_1408_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_size_1261_);
                    v_impl_1409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1258_, v_v_1259_, v_l_1264_);
                    v___x_1410_ = crate::leanh::lean_unsigned_to_nat(1);
                    if crate::leanh::lean_obj_tag(v_r_1265_) == 0 {
                        v_size_1411_ = crate::leanh::lean_ctor_get(v_r_1265_, 0);
                        v_size_1412_ = crate::leanh::lean_ctor_get(v_impl_1409_, 0);
                        crate::leanh::lean_inc(v_size_1412_);
                        v_k_1413_ = crate::leanh::lean_ctor_get(v_impl_1409_, 1);
                        crate::leanh::lean_inc(v_k_1413_);
                        v_v_1414_ = crate::leanh::lean_ctor_get(v_impl_1409_, 2);
                        crate::leanh::lean_inc(v_v_1414_);
                        v_l_1415_ = crate::leanh::lean_ctor_get(v_impl_1409_, 3);
                        crate::leanh::lean_inc(v_l_1415_);
                        v_r_1416_ = crate::leanh::lean_ctor_get(v_impl_1409_, 4);
                        crate::leanh::lean_inc(v_r_1416_);
                        v___x_1417_ = crate::leanh::lean_unsigned_to_nat(3);
                        v___x_1418_ = lean_nat_mul(v___x_1417_, v_size_1411_);
                        v___x_1419_ = lean_nat_dec_lt(v___x_1418_, v_size_1412_);
                        crate::leanh::lean_dec(v___x_1418_);
                        if v___x_1419_ == 0 {
                            crate::leanh::lean_dec(v_r_1416_);
                            crate::leanh::lean_dec(v_l_1415_);
                            crate::leanh::lean_dec(v_v_1414_);
                            crate::leanh::lean_dec(v_k_1413_);
                            v___x_1420_ = lean_nat_add(v___x_1410_, v_size_1412_);
                            crate::leanh::lean_dec(v_size_1412_);
                            v___x_1421_ = lean_nat_add(v___x_1420_, v_size_1411_);
                            crate::leanh::lean_dec(v___x_1420_);
                            if v_isShared_1268_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1267_, 3, v_impl_1409_);
                                crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1421_);
                                v___x_1423_ = v___x_1267_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1424_ =
                                    crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1262_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1263_);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1424_,
                                    3,
                                    v_impl_1409_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_r_1265_);
                                v___x_1423_ = v_reuseFailAlloc_1424_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_1490_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_1409_)) as u8;
                            if v_isSharedCheck_1490_ == 0 {
                                v_unused_1491_ = crate::leanh::lean_ctor_get(v_impl_1409_, 4);
                                crate::leanh::lean_dec(v_unused_1491_);
                                v_unused_1492_ = crate::leanh::lean_ctor_get(v_impl_1409_, 3);
                                crate::leanh::lean_dec(v_unused_1492_);
                                v_unused_1493_ = crate::leanh::lean_ctor_get(v_impl_1409_, 2);
                                crate::leanh::lean_dec(v_unused_1493_);
                                v_unused_1494_ = crate::leanh::lean_ctor_get(v_impl_1409_, 1);
                                crate::leanh::lean_dec(v_unused_1494_);
                                v_unused_1495_ = crate::leanh::lean_ctor_get(v_impl_1409_, 0);
                                crate::leanh::lean_dec(v_unused_1495_);
                                v___x_1426_ = v_impl_1409_;
                                v_isShared_1427_ = v_isSharedCheck_1490_;
                                state = 24;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_impl_1409_);
                                v___x_1426_ = crate::leanh::lean_box(0);
                                v_isShared_1427_ = v_isSharedCheck_1490_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_1496_ = crate::leanh::lean_ctor_get(v_impl_1409_, 3);
                        crate::leanh::lean_inc(v_l_1496_);
                        if crate::leanh::lean_obj_tag(v_l_1496_) == 0 {
                            v_r_1497_ = crate::leanh::lean_ctor_get(v_impl_1409_, 4);
                            v_k_1498_ = crate::leanh::lean_ctor_get(v_impl_1409_, 1);
                            v_v_1499_ = crate::leanh::lean_ctor_get(v_impl_1409_, 2);
                            v_isSharedCheck_1510_ =
                                (!crate::leanh::lean_is_exclusive(v_impl_1409_)) as u8;
                            if v_isSharedCheck_1510_ == 0 {
                                v_unused_1511_ = crate::leanh::lean_ctor_get(v_impl_1409_, 3);
                                crate::leanh::lean_dec(v_unused_1511_);
                                v_unused_1512_ = crate::leanh::lean_ctor_get(v_impl_1409_, 0);
                                crate::leanh::lean_dec(v_unused_1512_);
                                v___x_1501_ = v_impl_1409_;
                                v_isShared_1502_ = v_isSharedCheck_1510_;
                                state = 34;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_r_1497_);
                                crate::leanh::lean_inc(v_v_1499_);
                                crate::leanh::lean_inc(v_k_1498_);
                                crate::leanh::lean_dec(v_impl_1409_);
                                v___x_1501_ = crate::leanh::lean_box(0);
                                v_isShared_1502_ = v_isSharedCheck_1510_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_1513_ = crate::leanh::lean_ctor_get(v_impl_1409_, 4);
                            crate::leanh::lean_inc(v_r_1513_);
                            if crate::leanh::lean_obj_tag(v_r_1513_) == 0 {
                                v_k_1514_ = crate::leanh::lean_ctor_get(v_impl_1409_, 1);
                                v_v_1515_ = crate::leanh::lean_ctor_get(v_impl_1409_, 2);
                                v_isSharedCheck_1538_ =
                                    (!crate::leanh::lean_is_exclusive(v_impl_1409_)) as u8;
                                if v_isSharedCheck_1538_ == 0 {
                                    v_unused_1539_ = crate::leanh::lean_ctor_get(v_impl_1409_, 4);
                                    crate::leanh::lean_dec(v_unused_1539_);
                                    v_unused_1540_ = crate::leanh::lean_ctor_get(v_impl_1409_, 3);
                                    crate::leanh::lean_dec(v_unused_1540_);
                                    v_unused_1541_ = crate::leanh::lean_ctor_get(v_impl_1409_, 0);
                                    crate::leanh::lean_dec(v_unused_1541_);
                                    v___x_1517_ = v_impl_1409_;
                                    v_isShared_1518_ = v_isSharedCheck_1538_;
                                    state = 37;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_v_1515_);
                                    crate::leanh::lean_inc(v_k_1514_);
                                    crate::leanh::lean_dec(v_impl_1409_);
                                    v___x_1517_ = crate::leanh::lean_box(0);
                                    v_isShared_1518_ = v_isSharedCheck_1538_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_1542_ = crate::leanh::lean_unsigned_to_nat(2);
                                if v_isShared_1268_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v_r_1513_);
                                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v_impl_1409_);
                                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1542_);
                                    v___x_1544_ = v___x_1267_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1545_ =
                                        crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        0,
                                        v___x_1542_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        1,
                                        v_k_1262_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        2,
                                        v_v_1263_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        3,
                                        v_impl_1409_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1545_,
                                        4,
                                        v_r_1513_,
                                    );
                                    v___x_1544_ = v_reuseFailAlloc_1545_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                return v___x_1285_;
            }
            3 => {
                v_size_1290_ = crate::leanh::lean_ctor_get(v_l_1277_, 0);
                v_k_1291_ = crate::leanh::lean_ctor_get(v_l_1277_, 1);
                v_v_1292_ = crate::leanh::lean_ctor_get(v_l_1277_, 2);
                v_l_1293_ = crate::leanh::lean_ctor_get(v_l_1277_, 3);
                v_r_1294_ = crate::leanh::lean_ctor_get(v_l_1277_, 4);
                v_size_1295_ = crate::leanh::lean_ctor_get(v_r_1278_, 0);
                v___x_1296_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1297_ = lean_nat_mul(v___x_1296_, v_size_1295_);
                v___x_1298_ = lean_nat_dec_lt(v_size_1290_, v___x_1297_);
                crate::leanh::lean_dec(v___x_1297_);
                if v___x_1298_ == 0 {
                    crate::leanh::lean_inc(v_r_1294_);
                    crate::leanh::lean_inc(v_l_1293_);
                    crate::leanh::lean_inc(v_v_1292_);
                    crate::leanh::lean_inc(v_k_1291_);
                    v_isSharedCheck_1326_ = (!crate::leanh::lean_is_exclusive(v_l_1277_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v_unused_1327_ = crate::leanh::lean_ctor_get(v_l_1277_, 4);
                        crate::leanh::lean_dec(v_unused_1327_);
                        v_unused_1328_ = crate::leanh::lean_ctor_get(v_l_1277_, 3);
                        crate::leanh::lean_dec(v_unused_1328_);
                        v_unused_1329_ = crate::leanh::lean_ctor_get(v_l_1277_, 2);
                        crate::leanh::lean_dec(v_unused_1329_);
                        v_unused_1330_ = crate::leanh::lean_ctor_get(v_l_1277_, 1);
                        crate::leanh::lean_dec(v_unused_1330_);
                        v_unused_1331_ = crate::leanh::lean_ctor_get(v_l_1277_, 0);
                        crate::leanh::lean_dec(v_unused_1331_);
                        v___x_1300_ = v_l_1277_;
                        v_isShared_1301_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_l_1277_);
                        v___x_1300_ = crate::leanh::lean_box(0);
                        v_isShared_1301_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1267_);
                    v___x_1332_ = lean_nat_add(v___x_1272_, v_size_1273_);
                    v___x_1333_ = lean_nat_add(v___x_1332_, v_size_1274_);
                    crate::leanh::lean_dec(v_size_1274_);
                    v___x_1334_ = lean_nat_add(v___x_1332_, v_size_1290_);
                    crate::leanh::lean_dec(v___x_1332_);
                    crate::leanh::lean_inc_ref(v_l_1264_);
                    if v_isShared_1289_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1288_, 4, v_l_1277_);
                        crate::leanh::lean_ctor_set(v___x_1288_, 3, v_l_1264_);
                        crate::leanh::lean_ctor_set(v___x_1288_, 2, v_v_1263_);
                        crate::leanh::lean_ctor_set(v___x_1288_, 1, v_k_1262_);
                        crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1334_);
                        v___x_1336_ = v___x_1288_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1334_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1262_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1263_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_l_1264_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_l_1277_);
                        v___x_1336_ = v_reuseFailAlloc_1349_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1302_ = lean_nat_add(v___x_1272_, v_size_1273_);
                v___x_1303_ = lean_nat_add(v___x_1302_, v_size_1274_);
                crate::leanh::lean_dec(v_size_1274_);
                if crate::leanh::lean_obj_tag(v_l_1293_) == 0 {
                    v_size_1324_ = crate::leanh::lean_ctor_get(v_l_1293_, 0);
                    crate::leanh::lean_inc(v_size_1324_);
                    v___y_1316_ = v_size_1324_;
                    state = 8;
                    continue;
                } else {
                    v___x_1325_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1316_ = v___x_1325_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1308_ = lean_nat_add(v___y_1306_, v___y_1307_);
                crate::leanh::lean_dec(v___y_1307_);
                crate::leanh::lean_dec(v___y_1306_);
                if v_isShared_1301_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1300_, 4, v_r_1278_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 3, v_r_1294_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 2, v_v_1276_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 1, v_k_1275_);
                    crate::leanh::lean_ctor_set(v___x_1300_, 0, v___x_1308_);
                    v___x_1310_ = v___x_1300_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1308_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_r_1294_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1278_);
                    v___x_1310_ = v_reuseFailAlloc_1314_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1289_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1288_, 4, v___x_1310_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 3, v___y_1305_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 2, v_v_1292_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 1, v_k_1291_);
                    crate::leanh::lean_ctor_set(v___x_1288_, 0, v___x_1303_);
                    v___x_1312_ = v___x_1288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1313_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1303_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1291_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 3, v___y_1305_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1310_);
                    v___x_1312_ = v_reuseFailAlloc_1313_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1312_;
            }
            8 => {
                v___x_1317_ = lean_nat_add(v___x_1302_, v___y_1316_);
                crate::leanh::lean_dec(v___y_1316_);
                crate::leanh::lean_dec(v___x_1302_);
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v_l_1293_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1267_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_l_1264_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_l_1293_);
                    v___x_1319_ = v_reuseFailAlloc_1323_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1320_ = lean_nat_add(v___x_1272_, v_size_1295_);
                if crate::leanh::lean_obj_tag(v_r_1294_) == 0 {
                    v_size_1321_ = crate::leanh::lean_ctor_get(v_r_1294_, 0);
                    crate::leanh::lean_inc(v_size_1321_);
                    v___y_1305_ = v___x_1319_;
                    v___y_1306_ = v___x_1320_;
                    v___y_1307_ = v_size_1321_;
                    state = 5;
                    continue;
                } else {
                    v___x_1322_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1305_ = v___x_1319_;
                    v___y_1306_ = v___x_1320_;
                    v___y_1307_ = v___x_1322_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1343_ = (!crate::leanh::lean_is_exclusive(v_l_1264_)) as u8;
                if v_isSharedCheck_1343_ == 0 {
                    v_unused_1344_ = crate::leanh::lean_ctor_get(v_l_1264_, 4);
                    crate::leanh::lean_dec(v_unused_1344_);
                    v_unused_1345_ = crate::leanh::lean_ctor_get(v_l_1264_, 3);
                    crate::leanh::lean_dec(v_unused_1345_);
                    v_unused_1346_ = crate::leanh::lean_ctor_get(v_l_1264_, 2);
                    crate::leanh::lean_dec(v_unused_1346_);
                    v_unused_1347_ = crate::leanh::lean_ctor_get(v_l_1264_, 1);
                    crate::leanh::lean_dec(v_unused_1347_);
                    v_unused_1348_ = crate::leanh::lean_ctor_get(v_l_1264_, 0);
                    crate::leanh::lean_dec(v_unused_1348_);
                    v___x_1338_ = v_l_1264_;
                    v_isShared_1339_ = v_isSharedCheck_1343_;
                    state = 11;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_l_1264_);
                    v___x_1338_ = crate::leanh::lean_box(0);
                    v_isShared_1339_ = v_isSharedCheck_1343_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1339_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1338_, 4, v_r_1278_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 3, v___x_1336_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 2, v_v_1276_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 1, v_k_1275_);
                    crate::leanh::lean_ctor_set(v___x_1338_, 0, v___x_1333_);
                    v___x_1341_ = v___x_1338_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1333_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1276_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1336_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1278_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1341_;
            }
            13 => {
                v_k_1363_ = crate::leanh::lean_ctor_get(v_l_1356_, 1);
                v_v_1364_ = crate::leanh::lean_ctor_get(v_l_1356_, 2);
                v_isSharedCheck_1378_ = (!crate::leanh::lean_is_exclusive(v_l_1356_)) as u8;
                if v_isSharedCheck_1378_ == 0 {
                    v_unused_1379_ = crate::leanh::lean_ctor_get(v_l_1356_, 4);
                    crate::leanh::lean_dec(v_unused_1379_);
                    v_unused_1380_ = crate::leanh::lean_ctor_get(v_l_1356_, 3);
                    crate::leanh::lean_dec(v_unused_1380_);
                    v_unused_1381_ = crate::leanh::lean_ctor_get(v_l_1356_, 0);
                    crate::leanh::lean_dec(v_unused_1381_);
                    v___x_1366_ = v_l_1356_;
                    v_isShared_1367_ = v_isSharedCheck_1378_;
                    state = 14;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1364_);
                    crate::leanh::lean_inc(v_k_1363_);
                    crate::leanh::lean_dec(v_l_1356_);
                    v___x_1366_ = crate::leanh::lean_box(0);
                    v_isShared_1367_ = v_isSharedCheck_1378_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1368_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc_n(v_r_1357_, 2);
                if v_isShared_1367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1366_, 4, v_r_1357_);
                    crate::leanh::lean_ctor_set(v___x_1366_, 3, v_r_1357_);
                    crate::leanh::lean_ctor_set(v___x_1366_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v___x_1366_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1272_);
                    v___x_1370_ = v___x_1366_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_r_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_r_1357_);
                    v___x_1370_ = v_reuseFailAlloc_1377_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                crate::leanh::lean_inc(v_r_1357_);
                if v_isShared_1362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1361_, 3, v_r_1357_);
                    crate::leanh::lean_ctor_set(v___x_1361_, 0, v___x_1272_);
                    v___x_1372_ = v___x_1361_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1358_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_v_1359_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_r_1357_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_r_1357_);
                    v___x_1372_ = v_reuseFailAlloc_1376_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v___x_1372_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v___x_1370_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1364_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1363_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1368_);
                    v___x_1374_ = v___x_1267_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1368_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1363_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1364_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 3, v___x_1370_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1375_, 4, v___x_1372_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1374_;
            }
            18 => {
                v___x_1391_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1390_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1389_, 4, v_l_1356_);
                    crate::leanh::lean_ctor_set(v___x_1389_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v___x_1389_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v___x_1389_, 0, v___x_1272_);
                    v___x_1393_ = v___x_1389_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1272_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_l_1356_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_l_1356_);
                    v___x_1393_ = v_reuseFailAlloc_1397_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v_r_1385_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v___x_1393_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1387_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1386_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1391_);
                    v___x_1395_ = v___x_1267_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1387_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 3, v___x_1393_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1385_);
                    v___x_1395_ = v_reuseFailAlloc_1396_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1395_;
            }
            21 => {
                return v___x_1404_;
            }
            22 => {
                return v___x_1407_;
            }
            23 => {
                return v___x_1423_;
            }
            24 => {
                v_size_1428_ = crate::leanh::lean_ctor_get(v_l_1415_, 0);
                v_size_1429_ = crate::leanh::lean_ctor_get(v_r_1416_, 0);
                v_k_1430_ = crate::leanh::lean_ctor_get(v_r_1416_, 1);
                v_v_1431_ = crate::leanh::lean_ctor_get(v_r_1416_, 2);
                v_l_1432_ = crate::leanh::lean_ctor_get(v_r_1416_, 3);
                v_r_1433_ = crate::leanh::lean_ctor_get(v_r_1416_, 4);
                v___x_1434_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_1435_ = lean_nat_mul(v___x_1434_, v_size_1428_);
                v___x_1436_ = lean_nat_dec_lt(v_size_1429_, v___x_1435_);
                crate::leanh::lean_dec(v___x_1435_);
                if v___x_1436_ == 0 {
                    crate::leanh::lean_inc(v_r_1433_);
                    crate::leanh::lean_inc(v_l_1432_);
                    crate::leanh::lean_inc(v_v_1431_);
                    crate::leanh::lean_inc(v_k_1430_);
                    v_isSharedCheck_1465_ = (!crate::leanh::lean_is_exclusive(v_r_1416_)) as u8;
                    if v_isSharedCheck_1465_ == 0 {
                        v_unused_1466_ = crate::leanh::lean_ctor_get(v_r_1416_, 4);
                        crate::leanh::lean_dec(v_unused_1466_);
                        v_unused_1467_ = crate::leanh::lean_ctor_get(v_r_1416_, 3);
                        crate::leanh::lean_dec(v_unused_1467_);
                        v_unused_1468_ = crate::leanh::lean_ctor_get(v_r_1416_, 2);
                        crate::leanh::lean_dec(v_unused_1468_);
                        v_unused_1469_ = crate::leanh::lean_ctor_get(v_r_1416_, 1);
                        crate::leanh::lean_dec(v_unused_1469_);
                        v_unused_1470_ = crate::leanh::lean_ctor_get(v_r_1416_, 0);
                        crate::leanh::lean_dec(v_unused_1470_);
                        v___x_1438_ = v_r_1416_;
                        v_isShared_1439_ = v_isSharedCheck_1465_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_r_1416_);
                        v___x_1438_ = crate::leanh::lean_box(0);
                        v_isShared_1439_ = v_isSharedCheck_1465_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1267_);
                    v___x_1471_ = lean_nat_add(v___x_1410_, v_size_1412_);
                    crate::leanh::lean_dec(v_size_1412_);
                    v___x_1472_ = lean_nat_add(v___x_1471_, v_size_1411_);
                    crate::leanh::lean_dec(v___x_1471_);
                    v___x_1473_ = lean_nat_add(v___x_1410_, v_size_1411_);
                    v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1429_);
                    crate::leanh::lean_dec(v___x_1473_);
                    crate::leanh::lean_inc_ref(v_r_1265_);
                    if v_isShared_1427_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1426_, 4, v_r_1265_);
                        crate::leanh::lean_ctor_set(v___x_1426_, 3, v_r_1416_);
                        crate::leanh::lean_ctor_set(v___x_1426_, 2, v_v_1263_);
                        crate::leanh::lean_ctor_set(v___x_1426_, 1, v_k_1262_);
                        crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1474_);
                        v___x_1476_ = v___x_1426_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1489_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1474_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1262_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1263_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_r_1416_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_r_1265_);
                        v___x_1476_ = v_reuseFailAlloc_1489_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1440_ = lean_nat_add(v___x_1410_, v_size_1412_);
                crate::leanh::lean_dec(v_size_1412_);
                v___x_1441_ = lean_nat_add(v___x_1440_, v_size_1411_);
                crate::leanh::lean_dec(v___x_1440_);
                v___x_1453_ = lean_nat_add(v___x_1410_, v_size_1428_);
                if crate::leanh::lean_obj_tag(v_l_1432_) == 0 {
                    v_size_1463_ = crate::leanh::lean_ctor_get(v_l_1432_, 0);
                    crate::leanh::lean_inc(v_size_1463_);
                    v___y_1455_ = v_size_1463_;
                    state = 29;
                    continue;
                } else {
                    v___x_1464_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1455_ = v___x_1464_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1446_ = lean_nat_add(v___y_1444_, v___y_1445_);
                crate::leanh::lean_dec(v___y_1445_);
                crate::leanh::lean_dec(v___y_1444_);
                if v_isShared_1439_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1438_, 4, v_r_1265_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 3, v_r_1433_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v___x_1438_, 0, v___x_1446_);
                    v___x_1448_ = v___x_1438_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_r_1433_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_r_1265_);
                    v___x_1448_ = v_reuseFailAlloc_1452_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1427_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1426_, 4, v___x_1448_);
                    crate::leanh::lean_ctor_set(v___x_1426_, 3, v___y_1443_);
                    crate::leanh::lean_ctor_set(v___x_1426_, 2, v_v_1431_);
                    crate::leanh::lean_ctor_set(v___x_1426_, 1, v_k_1430_);
                    crate::leanh::lean_ctor_set(v___x_1426_, 0, v___x_1441_);
                    v___x_1450_ = v___x_1426_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1441_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1430_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1431_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 3, v___y_1443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1448_);
                    v___x_1450_ = v_reuseFailAlloc_1451_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_1450_;
            }
            29 => {
                v___x_1456_ = lean_nat_add(v___x_1453_, v___y_1455_);
                crate::leanh::lean_dec(v___y_1455_);
                crate::leanh::lean_dec(v___x_1453_);
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v_l_1432_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v_l_1415_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1414_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1413_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1456_);
                    v___x_1458_ = v___x_1267_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_l_1415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_l_1432_);
                    v___x_1458_ = v_reuseFailAlloc_1462_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1459_ = lean_nat_add(v___x_1410_, v_size_1411_);
                if crate::leanh::lean_obj_tag(v_r_1433_) == 0 {
                    v_size_1460_ = crate::leanh::lean_ctor_get(v_r_1433_, 0);
                    crate::leanh::lean_inc(v_size_1460_);
                    v___y_1443_ = v___x_1458_;
                    v___y_1444_ = v___x_1459_;
                    v___y_1445_ = v_size_1460_;
                    state = 26;
                    continue;
                } else {
                    v___x_1461_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___y_1443_ = v___x_1458_;
                    v___y_1444_ = v___x_1459_;
                    v___y_1445_ = v___x_1461_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1483_ = (!crate::leanh::lean_is_exclusive(v_r_1265_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = crate::leanh::lean_ctor_get(v_r_1265_, 4);
                    crate::leanh::lean_dec(v_unused_1484_);
                    v_unused_1485_ = crate::leanh::lean_ctor_get(v_r_1265_, 3);
                    crate::leanh::lean_dec(v_unused_1485_);
                    v_unused_1486_ = crate::leanh::lean_ctor_get(v_r_1265_, 2);
                    crate::leanh::lean_dec(v_unused_1486_);
                    v_unused_1487_ = crate::leanh::lean_ctor_get(v_r_1265_, 1);
                    crate::leanh::lean_dec(v_unused_1487_);
                    v_unused_1488_ = crate::leanh::lean_ctor_get(v_r_1265_, 0);
                    crate::leanh::lean_dec(v_unused_1488_);
                    v___x_1478_ = v_r_1265_;
                    v_isShared_1479_ = v_isSharedCheck_1483_;
                    state = 32;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_r_1265_);
                    v___x_1478_ = crate::leanh::lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1483_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1479_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1478_, 4, v___x_1476_);
                    crate::leanh::lean_ctor_set(v___x_1478_, 3, v_l_1415_);
                    crate::leanh::lean_ctor_set(v___x_1478_, 2, v_v_1414_);
                    crate::leanh::lean_ctor_set(v___x_1478_, 1, v_k_1413_);
                    crate::leanh::lean_ctor_set(v___x_1478_, 0, v___x_1472_);
                    v___x_1481_ = v___x_1478_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1413_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1414_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_l_1415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1482_, 4, v___x_1476_);
                    v___x_1481_ = v_reuseFailAlloc_1482_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1481_;
            }
            34 => {
                v___x_1503_ = crate::leanh::lean_unsigned_to_nat(3);
                crate::leanh::lean_inc(v_r_1497_);
                if v_isShared_1502_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1501_, 3, v_r_1497_);
                    crate::leanh::lean_ctor_set(v___x_1501_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v___x_1501_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v___x_1501_, 0, v___x_1410_);
                    v___x_1505_ = v___x_1501_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_r_1497_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1497_);
                    v___x_1505_ = v_reuseFailAlloc_1509_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v___x_1505_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v_l_1496_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1499_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1498_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1503_);
                    v___x_1507_ = v___x_1267_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1499_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_l_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1505_);
                    v___x_1507_ = v_reuseFailAlloc_1508_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1507_;
            }
            37 => {
                v_k_1519_ = crate::leanh::lean_ctor_get(v_r_1513_, 1);
                v_v_1520_ = crate::leanh::lean_ctor_get(v_r_1513_, 2);
                v_isSharedCheck_1534_ = (!crate::leanh::lean_is_exclusive(v_r_1513_)) as u8;
                if v_isSharedCheck_1534_ == 0 {
                    v_unused_1535_ = crate::leanh::lean_ctor_get(v_r_1513_, 4);
                    crate::leanh::lean_dec(v_unused_1535_);
                    v_unused_1536_ = crate::leanh::lean_ctor_get(v_r_1513_, 3);
                    crate::leanh::lean_dec(v_unused_1536_);
                    v_unused_1537_ = crate::leanh::lean_ctor_get(v_r_1513_, 0);
                    crate::leanh::lean_dec(v_unused_1537_);
                    v___x_1522_ = v_r_1513_;
                    v_isShared_1523_ = v_isSharedCheck_1534_;
                    state = 38;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_v_1520_);
                    crate::leanh::lean_inc(v_k_1519_);
                    crate::leanh::lean_dec(v_r_1513_);
                    v___x_1522_ = crate::leanh::lean_box(0);
                    v_isShared_1523_ = v_isSharedCheck_1534_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1524_ = crate::leanh::lean_unsigned_to_nat(3);
                if v_isShared_1523_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1522_, 4, v_l_1496_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 3, v_l_1496_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 2, v_v_1515_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 1, v_k_1514_);
                    crate::leanh::lean_ctor_set(v___x_1522_, 0, v___x_1410_);
                    v___x_1526_ = v___x_1522_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1533_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1514_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1515_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_l_1496_);
                    v___x_1526_ = v_reuseFailAlloc_1533_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1518_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1517_, 4, v_l_1496_);
                    crate::leanh::lean_ctor_set(v___x_1517_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v___x_1517_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v___x_1517_, 0, v___x_1410_);
                    v___x_1528_ = v___x_1517_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1263_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_l_1496_);
                    v___x_1528_ = v_reuseFailAlloc_1532_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1268_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1267_, 4, v___x_1528_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 3, v___x_1526_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 2, v_v_1520_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 1, v_k_1519_);
                    crate::leanh::lean_ctor_set(v___x_1267_, 0, v___x_1524_);
                    v___x_1530_ = v___x_1267_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1519_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1520_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___x_1526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1531_, 4, v___x_1528_);
                    v___x_1530_ = v_reuseFailAlloc_1531_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_1530_;
            }
            42 => {
                return v___x_1544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(
    mut v_t_1549_: *mut crate::leanh::LeanObject,
    mut v_k_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1549_) == 0 {
                    v_k_1551_ = crate::leanh::lean_ctor_get(v_t_1549_, 1);
                    v_v_1552_ = crate::leanh::lean_ctor_get(v_t_1549_, 2);
                    v_l_1553_ = crate::leanh::lean_ctor_get(v_t_1549_, 3);
                    v_r_1554_ = crate::leanh::lean_ctor_get(v_t_1549_, 4);
                    v___x_1555_ = lean_nat_dec_lt(v_k_1550_, v_k_1551_);
                    if v___x_1555_ == 0 {
                        v___x_1556_ = lean_nat_dec_eq(v_k_1550_, v_k_1551_);
                        if v___x_1556_ == 0 {
                            v_t_1549_ = v_r_1554_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_v_1552_);
                            v___x_1558_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1558_, 0, v_v_1552_);
                            return v___x_1558_;
                        }
                    } else {
                        v_t_1549_ = v_l_1553_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1560_ = crate::leanh::lean_box(0);
                    return v___x_1560_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg___boxed(
    mut v_t_1561_: *mut crate::leanh::LeanObject,
    mut v_k_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_1561_, v_k_1562_);
    crate::leanh::lean_dec(v_k_1562_);
    crate::leanh::lean_dec(v_t_1561_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt(
    mut v_optionsPerPos_1564_: *mut crate::leanh::LeanObject,
    mut v_pos_1565_: *mut crate::leanh::LeanObject,
    mut v_name_1566_: *mut crate::leanh::LeanObject,
    mut v_value_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_optionsPerPos_1564_, v_pos_1565_);
                if crate::leanh::lean_obj_tag(v___x_1572_) == 0 {
                    v___x_1573_ = l_Lean_Options_empty;
                    v___y_1569_ = v___x_1573_;
                    state = 1;
                    continue;
                } else {
                    v_val_1574_ = crate::leanh::lean_ctor_get(v___x_1572_, 0);
                    crate::leanh::lean_inc(v_val_1574_);
                    crate::leanh::lean_dec_ref_known(v___x_1572_, 1);
                    v___y_1569_ = v_val_1574_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1570_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(v___y_1569_, v_name_1566_, v_value_1567_);
                v___x_1571_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_pos_1565_, v___x_1570_, v_optionsPerPos_1564_);
                return v___x_1571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1(
    mut v_00_u03b2_1575_: *mut crate::leanh::LeanObject,
    mut v_k_1576_: *mut crate::leanh::LeanObject,
    mut v_v_1577_: *mut crate::leanh::LeanObject,
    mut v_t_1578_: *mut crate::leanh::LeanObject,
    mut v_hl_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1576_, v_v_1577_, v_t_1578_);
    return v___x_1580_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(
    mut v_00_u03b4_1581_: *mut crate::leanh::LeanObject,
    mut v_t_1582_: *mut crate::leanh::LeanObject,
    mut v_k_1583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_1582_, v_k_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___boxed(
    mut v_00_u03b4_1585_: *mut crate::leanh::LeanObject,
    mut v_t_1586_: *mut crate::leanh::LeanObject,
    mut v_k_1587_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(v_00_u03b4_1585_, v_t_1586_, v_k_1587_);
    crate::leanh::lean_dec(v_k_1587_);
    crate::leanh::lean_dec(v_t_1586_);
    return v_res_1588_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(
    mut v_b_u2082_1589_: *mut crate::leanh::LeanObject,
    mut v___f_1590_: *mut crate::leanh::LeanObject,
    mut v_x_1591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1591_) == 0 {
                    crate::leanh::lean_dec_ref(v___f_1590_);
                    v___x_1592_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1592_, 0, v_b_u2082_1589_);
                    return v___x_1592_;
                } else {
                    v_val_1593_ = crate::leanh::lean_ctor_get(v_x_1591_, 0);
                    v_isSharedCheck_1601_ = (!crate::leanh::lean_is_exclusive(v_x_1591_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v___x_1595_ = v_x_1591_;
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1593_);
                        crate::leanh::lean_dec(v_x_1591_);
                        v___x_1595_ = crate::leanh::lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1597_ = l_Lean_Options_mergeBy(v___f_1590_, v_val_1593_, v_b_u2082_1589_);
                if v_isShared_1596_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1595_, 0, v___x_1597_);
                    v___x_1599_ = v___x_1595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
                    v___x_1599_ = v_reuseFailAlloc_1600_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1599_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(
    mut v_x_1602_: *mut crate::leanh::LeanObject,
    mut v_x_1603_: *mut crate::leanh::LeanObject,
    mut v_dv_1604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v_dv_1604_);
    return v_dv_1604_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed(
    mut v_x_1605_: *mut crate::leanh::LeanObject,
    mut v_x_1606_: *mut crate::leanh::LeanObject,
    mut v_dv_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(v_x_1605_, v_x_1606_, v_dv_1607_);
    crate::leanh::lean_dec_ref(v_dv_1607_);
    crate::leanh::lean_dec_ref(v_x_1606_);
    crate::leanh::lean_dec(v_x_1605_);
    return v_res_1608_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(
    mut v_b_u2082_1610_: *mut crate::leanh::LeanObject,
    mut v_k_1611_: *mut crate::leanh::LeanObject,
    mut v_t_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: u8 = 0;
    let mut v_impl_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_impl_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1613_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0;
                if crate::leanh::lean_obj_tag(v_t_1612_) == 0 {
                    v_size_1614_ = crate::leanh::lean_ctor_get(v_t_1612_, 0);
                    v_k_1615_ = crate::leanh::lean_ctor_get(v_t_1612_, 1);
                    v_v_1616_ = crate::leanh::lean_ctor_get(v_t_1612_, 2);
                    v_l_1617_ = crate::leanh::lean_ctor_get(v_t_1612_, 3);
                    v_r_1618_ = crate::leanh::lean_ctor_get(v_t_1612_, 4);
                    v_isSharedCheck_1634_ = (!crate::leanh::lean_is_exclusive(v_t_1612_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1620_ = v_t_1612_;
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_r_1618_);
                        crate::leanh::lean_inc(v_l_1617_);
                        crate::leanh::lean_inc(v_v_1616_);
                        crate::leanh::lean_inc(v_k_1615_);
                        crate::leanh::lean_inc(v_size_1614_);
                        crate::leanh::lean_dec(v_t_1612_);
                        v___x_1620_ = crate::leanh::lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1635_ = crate::leanh::lean_box(0);
                    v___x_1636_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_1610_, v___f_1613_, v___x_1635_);
                    v_val_1637_ = crate::leanh::lean_ctor_get(v___x_1636_, 0);
                    crate::leanh::lean_inc(v_val_1637_);
                    crate::leanh::lean_dec(v___x_1636_);
                    v___x_1638_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1639_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1639_, 0, v___x_1638_);
                    crate::leanh::lean_ctor_set(v___x_1639_, 1, v_k_1611_);
                    crate::leanh::lean_ctor_set(v___x_1639_, 2, v_val_1637_);
                    crate::leanh::lean_ctor_set(v___x_1639_, 3, v_t_1612_);
                    crate::leanh::lean_ctor_set(v___x_1639_, 4, v_t_1612_);
                    return v___x_1639_;
                }
            }
            1 => {
                v___x_1622_ = lean_nat_dec_lt(v_k_1611_, v_k_1615_);
                if v___x_1622_ == 0 {
                    v___x_1623_ = lean_nat_dec_eq(v_k_1611_, v_k_1615_);
                    if v___x_1623_ == 0 {
                        crate::leanh::lean_del_object(v___x_1620_);
                        crate::leanh::lean_dec(v_size_1614_);
                        v_impl_1624_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_1610_, v_k_1611_, v_r_1618_);
                        v___x_1625_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1615_,
                            v_v_1616_,
                            v_l_1617_,
                            v_impl_1624_,
                        );
                        return v___x_1625_;
                    } else {
                        crate::leanh::lean_dec(v_k_1615_);
                        v___x_1626_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1626_, 0, v_v_1616_);
                        v___x_1627_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_1610_, v___f_1613_, v___x_1626_);
                        v_val_1628_ = crate::leanh::lean_ctor_get(v___x_1627_, 0);
                        crate::leanh::lean_inc(v_val_1628_);
                        crate::leanh::lean_dec(v___x_1627_);
                        if v_isShared_1621_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1620_, 2, v_val_1628_);
                            crate::leanh::lean_ctor_set(v___x_1620_, 1, v_k_1611_);
                            v___x_1630_ = v___x_1620_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1631_ =
                                crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_size_1614_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1611_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_val_1628_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1617_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_r_1618_);
                            v___x_1630_ = v_reuseFailAlloc_1631_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1620_);
                    crate::leanh::lean_dec(v_size_1614_);
                    v_impl_1632_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_1610_, v_k_1611_, v_l_1617_);
                    v___x_1633_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                        v_k_1615_,
                        v_v_1616_,
                        v_impl_1632_,
                        v_r_1618_,
                    );
                    return v___x_1633_;
                }
            }
            2 => {
                return v___x_1630_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(
    mut v_init_1640_: *mut crate::leanh::LeanObject,
    mut v_x_1641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1641_) == 0 {
                    v_k_1642_ = crate::leanh::lean_ctor_get(v_x_1641_, 1);
                    crate::leanh::lean_inc(v_k_1642_);
                    v_v_1643_ = crate::leanh::lean_ctor_get(v_x_1641_, 2);
                    crate::leanh::lean_inc(v_v_1643_);
                    v_l_1644_ = crate::leanh::lean_ctor_get(v_x_1641_, 3);
                    crate::leanh::lean_inc(v_l_1644_);
                    v_r_1645_ = crate::leanh::lean_ctor_get(v_x_1641_, 4);
                    crate::leanh::lean_inc(v_r_1645_);
                    crate::leanh::lean_dec_ref_known(v_x_1641_, 5);
                    v___x_1646_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_init_1640_, v_l_1644_);
                    v___x_1647_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_v_1643_, v_k_1642_, v___x_1646_);
                    v_init_1640_ = v___x_1647_;
                    v_x_1641_ = v_r_1645_;
                    state = 0;
                    continue;
                } else {
                    return v_init_1640_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge(
    mut v_t_u2081_1649_: *mut crate::leanh::LeanObject,
    mut v_t_u2082_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_t_u2081_1649_, v_t_u2082_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0(
    mut v_b_u2082_1652_: *mut crate::leanh::LeanObject,
    mut v_k_1653_: *mut crate::leanh::LeanObject,
    mut v_t_1654_: *mut crate::leanh::LeanObject,
    mut v_hl_1655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_1652_, v_k_1653_, v_t_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1(
    mut v_init_1657_: *mut crate::leanh::LeanObject,
    mut v_t_1658_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_init_1657_, v_t_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0(
    mut v_toPure_1660_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_expr_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_expr_1662_ = crate::leanh::lean_ctor_get(v_____do__lift_1661_, 0);
    crate::leanh::lean_inc_ref(v_expr_1662_);
    crate::leanh::lean_dec_ref(v_____do__lift_1661_);
    v___x_1663_ =
        crate::leanh::lean_apply_2(v_toPure_1660_, crate::leanh::lean_box(0), v_expr_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(
    mut v_inst_1664_: *mut crate::leanh::LeanObject,
    mut v_inst_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1666_ = crate::leanh::lean_ctor_get(v_inst_1664_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1666_);
    v_toBind_1667_ = crate::leanh::lean_ctor_get(v_inst_1664_, 1);
    crate::leanh::lean_inc(v_toBind_1667_);
    crate::leanh::lean_dec_ref(v_inst_1664_);
    v_toPure_1668_ = crate::leanh::lean_ctor_get(v_toApplicative_1666_, 1);
    crate::leanh::lean_inc(v_toPure_1668_);
    crate::leanh::lean_dec_ref(v_toApplicative_1666_);
    v___f_1669_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1669_, 0, v_toPure_1668_);
    v___x_1670_ = crate::leanh::lean_apply_4(
        v_toBind_1667_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1665_,
        v___f_1669_,
    );
    return v___x_1670_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr(
    mut v_m_1671_: *mut crate::leanh::LeanObject,
    mut v_inst_1672_: *mut crate::leanh::LeanObject,
    mut v_inst_1673_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1674_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1672_, v_inst_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0(
    mut v_toPure_1675_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1676_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pos_1677_ = crate::leanh::lean_ctor_get(v_____do__lift_1676_, 1);
    crate::leanh::lean_inc(v_pos_1677_);
    crate::leanh::lean_dec_ref(v_____do__lift_1676_);
    v___x_1678_ =
        crate::leanh::lean_apply_2(v_toPure_1675_, crate::leanh::lean_box(0), v_pos_1677_);
    return v___x_1678_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(
    mut v_inst_1679_: *mut crate::leanh::LeanObject,
    mut v_inst_1680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1681_ = crate::leanh::lean_ctor_get(v_inst_1679_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1681_);
    v_toBind_1682_ = crate::leanh::lean_ctor_get(v_inst_1679_, 1);
    crate::leanh::lean_inc(v_toBind_1682_);
    crate::leanh::lean_dec_ref(v_inst_1679_);
    v_toPure_1683_ = crate::leanh::lean_ctor_get(v_toApplicative_1681_, 1);
    crate::leanh::lean_inc(v_toPure_1683_);
    crate::leanh::lean_dec_ref(v_toApplicative_1681_);
    v___f_1684_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1684_, 0, v_toPure_1683_);
    v___x_1685_ = crate::leanh::lean_apply_4(
        v_toBind_1682_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_inst_1680_,
        v___f_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos(
    mut v_m_1686_: *mut crate::leanh::LeanObject,
    mut v_inst_1687_: *mut crate::leanh::LeanObject,
    mut v_inst_1688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1689_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_1687_, v_inst_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0(
    mut v_childIdx_1690_: *mut crate::leanh::LeanObject,
    mut v_child_1691_: *mut crate::leanh::LeanObject,
    mut v_cfg_1692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_1693_ = crate::leanh::lean_ctor_get(v_cfg_1692_, 1);
                v_isSharedCheck_1701_ = (!crate::leanh::lean_is_exclusive(v_cfg_1692_)) as u8;
                if v_isSharedCheck_1701_ == 0 {
                    v_unused_1702_ = crate::leanh::lean_ctor_get(v_cfg_1692_, 0);
                    crate::leanh::lean_dec(v_unused_1702_);
                    v___x_1695_ = v_cfg_1692_;
                    v_isShared_1696_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_pos_1693_);
                    crate::leanh::lean_dec(v_cfg_1692_);
                    v___x_1695_ = crate::leanh::lean_box(0);
                    v_isShared_1696_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1697_ = l_Lean_SubExpr_Pos_push(v_pos_1693_, v_childIdx_1690_);
                crate::leanh::lean_dec(v_pos_1693_);
                if v_isShared_1696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1695_, 1, v___x_1697_);
                    crate::leanh::lean_ctor_set(v___x_1695_, 0, v_child_1691_);
                    v___x_1699_ = v___x_1695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_child_1691_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
                    v___x_1699_ = v_reuseFailAlloc_1700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1699_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
    mut v_inst_1703_: *mut crate::leanh::LeanObject,
    mut v_child_1704_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1705_: *mut crate::leanh::LeanObject,
    mut v_x_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1707_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1707_, 0, v_childIdx_1705_);
    crate::leanh::lean_closure_set(v___f_1707_, 1, v_child_1704_);
    v___x_1708_ = crate::leanh::lean_apply_3(
        v_inst_1703_,
        crate::leanh::lean_box(0),
        v___f_1707_,
        v_x_1706_,
    );
    return v___x_1708_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend(
    mut v_00_u03b1_1709_: *mut crate::leanh::LeanObject,
    mut v_m_1710_: *mut crate::leanh::LeanObject,
    mut v_inst_1711_: *mut crate::leanh::LeanObject,
    mut v_child_1712_: *mut crate::leanh::LeanObject,
    mut v_childIdx_1713_: *mut crate::leanh::LeanObject,
    mut v_x_1714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1711_,
        v_child_1712_,
        v_childIdx_1713_,
        v_x_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(
    mut v_inst_1716_: *mut crate::leanh::LeanObject,
    mut v_x_1717_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Lean_Expr_appFn_x21(v_____do__lift_1718_);
    v___x_1720_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1721_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1716_,
        v___x_1719_,
        v___x_1720_,
        v_x_1717_,
    );
    return v___x_1721_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed(
    mut v_inst_1722_: *mut crate::leanh::LeanObject,
    mut v_x_1723_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(
        v_inst_1722_,
        v_x_1723_,
        v_____do__lift_1724_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1724_);
    return v_res_1725_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
    mut v_inst_1726_: *mut crate::leanh::LeanObject,
    mut v_inst_1727_: *mut crate::leanh::LeanObject,
    mut v_inst_1728_: *mut crate::leanh::LeanObject,
    mut v_x_1729_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1730_ = crate::leanh::lean_ctor_get(v_inst_1726_, 1);
    crate::leanh::lean_inc(v_toBind_1730_);
    v___f_1731_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1731_, 0, v_inst_1728_);
    crate::leanh::lean_closure_set(v___f_1731_, 1, v_x_1729_);
    v___x_1732_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1726_, v_inst_1727_);
    v___x_1733_ = crate::leanh::lean_apply_4(
        v_toBind_1730_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1732_,
        v___f_1731_,
    );
    return v___x_1733_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn(
    mut v_00_u03b1_1734_: *mut crate::leanh::LeanObject,
    mut v_m_1735_: *mut crate::leanh::LeanObject,
    mut v_inst_1736_: *mut crate::leanh::LeanObject,
    mut v_inst_1737_: *mut crate::leanh::LeanObject,
    mut v_inst_1738_: *mut crate::leanh::LeanObject,
    mut v_x_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
        v_inst_1736_,
        v_inst_1737_,
        v_inst_1738_,
        v_x_1739_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(
    mut v_inst_1741_: *mut crate::leanh::LeanObject,
    mut v_x_1742_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Lean_Expr_appArg_x21(v_____do__lift_1743_);
    v___x_1745_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1746_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1741_,
        v___x_1744_,
        v___x_1745_,
        v_x_1742_,
    );
    return v___x_1746_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed(
    mut v_inst_1747_: *mut crate::leanh::LeanObject,
    mut v_x_1748_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(
        v_inst_1747_,
        v_x_1748_,
        v_____do__lift_1749_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1749_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
    mut v_inst_1751_: *mut crate::leanh::LeanObject,
    mut v_inst_1752_: *mut crate::leanh::LeanObject,
    mut v_inst_1753_: *mut crate::leanh::LeanObject,
    mut v_x_1754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1755_ = crate::leanh::lean_ctor_get(v_inst_1751_, 1);
    crate::leanh::lean_inc(v_toBind_1755_);
    v___f_1756_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1756_, 0, v_inst_1753_);
    crate::leanh::lean_closure_set(v___f_1756_, 1, v_x_1754_);
    v___x_1757_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1751_, v_inst_1752_);
    v___x_1758_ = crate::leanh::lean_apply_4(
        v_toBind_1755_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1757_,
        v___f_1756_,
    );
    return v___x_1758_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg(
    mut v_00_u03b1_1759_: *mut crate::leanh::LeanObject,
    mut v_m_1760_: *mut crate::leanh::LeanObject,
    mut v_inst_1761_: *mut crate::leanh::LeanObject,
    mut v_inst_1762_: *mut crate::leanh::LeanObject,
    mut v_inst_1763_: *mut crate::leanh::LeanObject,
    mut v_x_1764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1761_,
        v_inst_1762_,
        v_inst_1763_,
        v_x_1764_,
    );
    return v___x_1765_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0(
    mut v_inst_1766_: *mut crate::leanh::LeanObject,
    mut v_x_1767_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1769_ = l_Lean_SubExpr_Pos_typeCoord;
    v___x_1770_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1766_,
        v_____do__lift_1768_,
        v___x_1769_,
        v_x_1767_,
    );
    return v___x_1770_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1(
    mut v_inst_1771_: *mut crate::leanh::LeanObject,
    mut v_toBind_1772_: *mut crate::leanh::LeanObject,
    mut v___f_1773_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1775_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1775_, 0, v_____do__lift_1774_);
    v___x_1776_ = crate::leanh::lean_apply_2(v_inst_1771_, crate::leanh::lean_box(0), v___x_1775_);
    v___x_1777_ = crate::leanh::lean_apply_4(
        v_toBind_1772_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1776_,
        v___f_1773_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(
    mut v_inst_1778_: *mut crate::leanh::LeanObject,
    mut v_inst_1779_: *mut crate::leanh::LeanObject,
    mut v_inst_1780_: *mut crate::leanh::LeanObject,
    mut v_inst_1781_: *mut crate::leanh::LeanObject,
    mut v_x_1782_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1783_ = crate::leanh::lean_ctor_get(v_inst_1778_, 1);
    crate::leanh::lean_inc_n(v_toBind_1783_, 2);
    v___f_1784_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1784_, 0, v_inst_1780_);
    crate::leanh::lean_closure_set(v___f_1784_, 1, v_x_1782_);
    v___f_1785_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1785_, 0, v_inst_1781_);
    crate::leanh::lean_closure_set(v___f_1785_, 1, v_toBind_1783_);
    crate::leanh::lean_closure_set(v___f_1785_, 2, v___f_1784_);
    v___x_1786_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1778_, v_inst_1779_);
    v___x_1787_ = crate::leanh::lean_apply_4(
        v_toBind_1783_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1786_,
        v___f_1785_,
    );
    return v___x_1787_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType(
    mut v_00_u03b1_1788_: *mut crate::leanh::LeanObject,
    mut v_m_1789_: *mut crate::leanh::LeanObject,
    mut v_inst_1790_: *mut crate::leanh::LeanObject,
    mut v_inst_1791_: *mut crate::leanh::LeanObject,
    mut v_inst_1792_: *mut crate::leanh::LeanObject,
    mut v_inst_1793_: *mut crate::leanh::LeanObject,
    mut v_x_1794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1795_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(
        v_inst_1790_,
        v_inst_1791_,
        v_inst_1792_,
        v_inst_1793_,
        v_x_1794_,
    );
    return v___x_1795_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0(
    mut v_xa_1796_: *mut crate::leanh::LeanObject,
    mut v_inst_1797_: *mut crate::leanh::LeanObject,
    mut v_inst_1798_: *mut crate::leanh::LeanObject,
    mut v_inst_1799_: *mut crate::leanh::LeanObject,
    mut v_acc_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = crate::leanh::lean_apply_1(v_xa_1796_, v_acc_1800_);
    v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1797_,
        v_inst_1798_,
        v_inst_1799_,
        v___x_1801_,
    );
    return v___x_1802_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(
    mut v_xf_1803_: *mut crate::leanh::LeanObject,
    mut v_inst_1804_: *mut crate::leanh::LeanObject,
    mut v_inst_1805_: *mut crate::leanh::LeanObject,
    mut v_inst_1806_: *mut crate::leanh::LeanObject,
    mut v_xa_1807_: *mut crate::leanh::LeanObject,
    mut v_toBind_1808_: *mut crate::leanh::LeanObject,
    mut v___f_1809_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: u8 = 0;
    v___x_1811_ = l_Lean_Expr_isApp(v_____do__lift_1810_);
    if v___x_1811_ == 0 {
        crate::leanh::lean_dec(v___f_1809_);
        crate::leanh::lean_dec(v_toBind_1808_);
        crate::leanh::lean_dec(v_xa_1807_);
        crate::leanh::lean_dec(v_inst_1806_);
        crate::leanh::lean_dec(v_inst_1805_);
        crate::leanh::lean_dec_ref(v_inst_1804_);
        return v_xf_1803_;
    } else {
        let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_inst_1806_);
        crate::leanh::lean_inc(v_inst_1805_);
        crate::leanh::lean_inc_ref(v_inst_1804_);
        v___x_1812_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(
            v_inst_1804_,
            v_inst_1805_,
            v_inst_1806_,
            v_xf_1803_,
            v_xa_1807_,
        );
        v___x_1813_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
            v_inst_1804_,
            v_inst_1805_,
            v_inst_1806_,
            v___x_1812_,
        );
        v___x_1814_ = crate::leanh::lean_apply_4(
            v_toBind_1808_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1813_,
            v___f_1809_,
        );
        return v___x_1814_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed(
    mut v_xf_1815_: *mut crate::leanh::LeanObject,
    mut v_inst_1816_: *mut crate::leanh::LeanObject,
    mut v_inst_1817_: *mut crate::leanh::LeanObject,
    mut v_inst_1818_: *mut crate::leanh::LeanObject,
    mut v_xa_1819_: *mut crate::leanh::LeanObject,
    mut v_toBind_1820_: *mut crate::leanh::LeanObject,
    mut v___f_1821_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1823_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(
        v_xf_1815_,
        v_inst_1816_,
        v_inst_1817_,
        v_inst_1818_,
        v_xa_1819_,
        v_toBind_1820_,
        v___f_1821_,
        v_____do__lift_1822_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1822_);
    return v_res_1823_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(
    mut v_inst_1824_: *mut crate::leanh::LeanObject,
    mut v_inst_1825_: *mut crate::leanh::LeanObject,
    mut v_inst_1826_: *mut crate::leanh::LeanObject,
    mut v_xf_1827_: *mut crate::leanh::LeanObject,
    mut v_xa_1828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1829_ = crate::leanh::lean_ctor_get(v_inst_1824_, 1);
    crate::leanh::lean_inc_n(v_toBind_1829_, 2);
    crate::leanh::lean_inc(v_inst_1826_);
    crate::leanh::lean_inc_n(v_inst_1825_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_1824_, 2);
    crate::leanh::lean_inc(v_xa_1828_);
    v___f_1830_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1830_, 0, v_xa_1828_);
    crate::leanh::lean_closure_set(v___f_1830_, 1, v_inst_1824_);
    crate::leanh::lean_closure_set(v___f_1830_, 2, v_inst_1825_);
    crate::leanh::lean_closure_set(v___f_1830_, 3, v_inst_1826_);
    v___f_1831_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_1831_, 0, v_xf_1827_);
    crate::leanh::lean_closure_set(v___f_1831_, 1, v_inst_1824_);
    crate::leanh::lean_closure_set(v___f_1831_, 2, v_inst_1825_);
    crate::leanh::lean_closure_set(v___f_1831_, 3, v_inst_1826_);
    crate::leanh::lean_closure_set(v___f_1831_, 4, v_xa_1828_);
    crate::leanh::lean_closure_set(v___f_1831_, 5, v_toBind_1829_);
    crate::leanh::lean_closure_set(v___f_1831_, 6, v___f_1830_);
    v___x_1832_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1824_, v_inst_1825_);
    v___x_1833_ = crate::leanh::lean_apply_4(
        v_toBind_1829_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1832_,
        v___f_1831_,
    );
    return v___x_1833_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs(
    mut v_00_u03b1_1834_: *mut crate::leanh::LeanObject,
    mut v_m_1835_: *mut crate::leanh::LeanObject,
    mut v_inst_1836_: *mut crate::leanh::LeanObject,
    mut v_inst_1837_: *mut crate::leanh::LeanObject,
    mut v_inst_1838_: *mut crate::leanh::LeanObject,
    mut v_xf_1839_: *mut crate::leanh::LeanObject,
    mut v_xa_1840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1841_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(
        v_inst_1836_,
        v_inst_1837_,
        v_inst_1838_,
        v_xf_1839_,
        v_xa_1840_,
    );
    return v___x_1841_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0(
    mut v_xa_1842_: *mut crate::leanh::LeanObject,
    mut v_inst_1843_: *mut crate::leanh::LeanObject,
    mut v_inst_1844_: *mut crate::leanh::LeanObject,
    mut v_inst_1845_: *mut crate::leanh::LeanObject,
    mut v_acc_1846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1847_ = crate::leanh::lean_apply_1(v_xa_1842_, v_acc_1846_);
    v___x_1848_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1843_,
        v_inst_1844_,
        v_inst_1845_,
        v___x_1847_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(
    mut v_maxArgs_1849_: *mut crate::leanh::LeanObject,
    mut v_inst_1850_: *mut crate::leanh::LeanObject,
    mut v_inst_1851_: *mut crate::leanh::LeanObject,
    mut v_inst_1852_: *mut crate::leanh::LeanObject,
    mut v_xf_1853_: *mut crate::leanh::LeanObject,
    mut v_xa_1854_: *mut crate::leanh::LeanObject,
    mut v_toBind_1855_: *mut crate::leanh::LeanObject,
    mut v___f_1856_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1857_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1859_: u8 = 0;
    v_zero_1858_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1859_ = lean_nat_dec_eq(v_maxArgs_1849_, v_zero_1858_);
    if v_isZero_1859_ == 0 {
        if crate::leanh::lean_obj_tag(v_____do__lift_1857_) == 5 {
            let mut v_one_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_one_1860_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1861_ = lean_nat_sub(v_maxArgs_1849_, v_one_1860_);
            crate::leanh::lean_inc(v_inst_1852_);
            crate::leanh::lean_inc(v_inst_1851_);
            crate::leanh::lean_inc_ref(v_inst_1850_);
            v___x_1862_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(
                v_inst_1850_,
                v_inst_1851_,
                v_inst_1852_,
                v_n_1861_,
                v_xf_1853_,
                v_xa_1854_,
            );
            v___x_1863_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
                v_inst_1850_,
                v_inst_1851_,
                v_inst_1852_,
                v___x_1862_,
            );
            v___x_1864_ = crate::leanh::lean_apply_4(
                v_toBind_1855_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1863_,
                v___f_1856_,
            );
            return v___x_1864_;
        } else {
            crate::leanh::lean_dec(v___f_1856_);
            crate::leanh::lean_dec(v_toBind_1855_);
            crate::leanh::lean_dec(v_xa_1854_);
            crate::leanh::lean_dec(v_inst_1852_);
            crate::leanh::lean_dec(v_inst_1851_);
            crate::leanh::lean_dec_ref(v_inst_1850_);
            return v_xf_1853_;
        }
    } else {
        crate::leanh::lean_dec(v___f_1856_);
        crate::leanh::lean_dec(v_toBind_1855_);
        crate::leanh::lean_dec(v_xa_1854_);
        crate::leanh::lean_dec(v_inst_1852_);
        crate::leanh::lean_dec(v_inst_1851_);
        crate::leanh::lean_dec_ref(v_inst_1850_);
        return v_xf_1853_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed(
    mut v_maxArgs_1865_: *mut crate::leanh::LeanObject,
    mut v_inst_1866_: *mut crate::leanh::LeanObject,
    mut v_inst_1867_: *mut crate::leanh::LeanObject,
    mut v_inst_1868_: *mut crate::leanh::LeanObject,
    mut v_xf_1869_: *mut crate::leanh::LeanObject,
    mut v_xa_1870_: *mut crate::leanh::LeanObject,
    mut v_toBind_1871_: *mut crate::leanh::LeanObject,
    mut v___f_1872_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1873_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1874_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(
        v_maxArgs_1865_,
        v_inst_1866_,
        v_inst_1867_,
        v_inst_1868_,
        v_xf_1869_,
        v_xa_1870_,
        v_toBind_1871_,
        v___f_1872_,
        v_____do__lift_1873_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1873_);
    crate::leanh::lean_dec(v_maxArgs_1865_);
    return v_res_1874_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(
    mut v_inst_1875_: *mut crate::leanh::LeanObject,
    mut v_inst_1876_: *mut crate::leanh::LeanObject,
    mut v_inst_1877_: *mut crate::leanh::LeanObject,
    mut v_maxArgs_1878_: *mut crate::leanh::LeanObject,
    mut v_xf_1879_: *mut crate::leanh::LeanObject,
    mut v_xa_1880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1881_ = crate::leanh::lean_ctor_get(v_inst_1875_, 1);
    crate::leanh::lean_inc_n(v_toBind_1881_, 2);
    crate::leanh::lean_inc(v_inst_1877_);
    crate::leanh::lean_inc_n(v_inst_1876_, 2);
    crate::leanh::lean_inc_ref_n(v_inst_1875_, 2);
    crate::leanh::lean_inc(v_xa_1880_);
    v___f_1882_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1882_, 0, v_xa_1880_);
    crate::leanh::lean_closure_set(v___f_1882_, 1, v_inst_1875_);
    crate::leanh::lean_closure_set(v___f_1882_, 2, v_inst_1876_);
    crate::leanh::lean_closure_set(v___f_1882_, 3, v_inst_1877_);
    v___f_1883_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    crate::leanh::lean_closure_set(v___f_1883_, 0, v_maxArgs_1878_);
    crate::leanh::lean_closure_set(v___f_1883_, 1, v_inst_1875_);
    crate::leanh::lean_closure_set(v___f_1883_, 2, v_inst_1876_);
    crate::leanh::lean_closure_set(v___f_1883_, 3, v_inst_1877_);
    crate::leanh::lean_closure_set(v___f_1883_, 4, v_xf_1879_);
    crate::leanh::lean_closure_set(v___f_1883_, 5, v_xa_1880_);
    crate::leanh::lean_closure_set(v___f_1883_, 6, v_toBind_1881_);
    crate::leanh::lean_closure_set(v___f_1883_, 7, v___f_1882_);
    v___x_1884_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1875_, v_inst_1876_);
    v___x_1885_ = crate::leanh::lean_apply_4(
        v_toBind_1881_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1884_,
        v___f_1883_,
    );
    return v___x_1885_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs(
    mut v_00_u03b1_1886_: *mut crate::leanh::LeanObject,
    mut v_m_1887_: *mut crate::leanh::LeanObject,
    mut v_inst_1888_: *mut crate::leanh::LeanObject,
    mut v_inst_1889_: *mut crate::leanh::LeanObject,
    mut v_inst_1890_: *mut crate::leanh::LeanObject,
    mut v_maxArgs_1891_: *mut crate::leanh::LeanObject,
    mut v_xf_1892_: *mut crate::leanh::LeanObject,
    mut v_xa_1893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1894_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(
        v_inst_1888_,
        v_inst_1889_,
        v_inst_1890_,
        v_maxArgs_1891_,
        v_xf_1892_,
        v_xa_1893_,
    );
    return v___x_1894_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(
    mut v___y_1895_: *mut crate::leanh::LeanObject,
    mut v_e_1896_: *mut crate::leanh::LeanObject,
    mut v_newPos_1897_: *mut crate::leanh::LeanObject,
    mut v_cfg_1898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1899_ = l_Lean_Expr_getBoundedAppFn(v___y_1895_, v_e_1896_);
    v___x_1900_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    crate::leanh::lean_ctor_set(v___x_1900_, 1, v_newPos_1897_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed(
    mut v___y_1901_: *mut crate::leanh::LeanObject,
    mut v_e_1902_: *mut crate::leanh::LeanObject,
    mut v_newPos_1903_: *mut crate::leanh::LeanObject,
    mut v_cfg_1904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(
        v___y_1901_,
        v_e_1902_,
        v_newPos_1903_,
        v_cfg_1904_,
    );
    crate::leanh::lean_dec_ref(v_cfg_1904_);
    crate::leanh::lean_dec_ref(v_e_1902_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(
    mut v___y_1906_: *mut crate::leanh::LeanObject,
    mut v_e_1907_: *mut crate::leanh::LeanObject,
    mut v_inst_1908_: *mut crate::leanh::LeanObject,
    mut v_xf_1909_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_newPos_1911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_newPos_1911_ = l_Lean_SubExpr_Pos_pushNaryFn(v___y_1906_, v_____do__lift_1910_);
    v___f_1912_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1912_, 0, v___y_1906_);
    crate::leanh::lean_closure_set(v___f_1912_, 1, v_e_1907_);
    crate::leanh::lean_closure_set(v___f_1912_, 2, v_newPos_1911_);
    v___x_1913_ = crate::leanh::lean_apply_3(
        v_inst_1908_,
        crate::leanh::lean_box(0),
        v___f_1912_,
        v_xf_1909_,
    );
    return v___x_1913_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed(
    mut v___y_1914_: *mut crate::leanh::LeanObject,
    mut v_e_1915_: *mut crate::leanh::LeanObject,
    mut v_inst_1916_: *mut crate::leanh::LeanObject,
    mut v_xf_1917_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(
        v___y_1914_,
        v_e_1915_,
        v_inst_1916_,
        v_xf_1917_,
        v_____do__lift_1918_,
    );
    crate::leanh::lean_dec(v_____do__lift_1918_);
    return v_res_1919_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2(
    mut v_inst_1920_: *mut crate::leanh::LeanObject,
    mut v_xf_1921_: *mut crate::leanh::LeanObject,
    mut v_inst_1922_: *mut crate::leanh::LeanObject,
    mut v_inst_1923_: *mut crate::leanh::LeanObject,
    mut v_toBind_1924_: *mut crate::leanh::LeanObject,
    mut v_maxArgs_1925_: *mut crate::leanh::LeanObject,
    mut v_e_1926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = l_Lean_Expr_getAppNumArgs(v_e_1926_);
                v___x_1933_ = lean_nat_dec_le(v_maxArgs_1925_, v___x_1932_);
                if v___x_1933_ == 0 {
                    crate::leanh::lean_dec(v_maxArgs_1925_);
                    v___y_1928_ = v___x_1932_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1932_);
                    v___y_1928_ = v_maxArgs_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1929_ = crate::leanh::lean_alloc_closure(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 4);
                crate::leanh::lean_closure_set(v___f_1929_, 0, v___y_1928_);
                crate::leanh::lean_closure_set(v___f_1929_, 1, v_e_1926_);
                crate::leanh::lean_closure_set(v___f_1929_, 2, v_inst_1920_);
                crate::leanh::lean_closure_set(v___f_1929_, 3, v_xf_1921_);
                v___x_1930_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(
                    v_inst_1922_,
                    v_inst_1923_,
                );
                v___x_1931_ = crate::leanh::lean_apply_4(
                    v_toBind_1924_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___x_1930_,
                    v___f_1929_,
                );
                return v___x_1931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg(
    mut v_inst_1934_: *mut crate::leanh::LeanObject,
    mut v_inst_1935_: *mut crate::leanh::LeanObject,
    mut v_inst_1936_: *mut crate::leanh::LeanObject,
    mut v_maxArgs_1937_: *mut crate::leanh::LeanObject,
    mut v_xf_1938_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1939_ = crate::leanh::lean_ctor_get(v_inst_1934_, 1);
    crate::leanh::lean_inc_n(v_toBind_1939_, 2);
    crate::leanh::lean_inc(v_inst_1935_);
    crate::leanh::lean_inc_ref(v_inst_1934_);
    v___f_1940_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2
            as *mut core::ffi::c_void,
        7,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1940_, 0, v_inst_1936_);
    crate::leanh::lean_closure_set(v___f_1940_, 1, v_xf_1938_);
    crate::leanh::lean_closure_set(v___f_1940_, 2, v_inst_1934_);
    crate::leanh::lean_closure_set(v___f_1940_, 3, v_inst_1935_);
    crate::leanh::lean_closure_set(v___f_1940_, 4, v_toBind_1939_);
    crate::leanh::lean_closure_set(v___f_1940_, 5, v_maxArgs_1937_);
    v___x_1941_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1934_, v_inst_1935_);
    v___x_1942_ = crate::leanh::lean_apply_4(
        v_toBind_1939_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1941_,
        v___f_1940_,
    );
    return v___x_1942_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn(
    mut v_00_u03b1_1943_: *mut crate::leanh::LeanObject,
    mut v_m_1944_: *mut crate::leanh::LeanObject,
    mut v_inst_1945_: *mut crate::leanh::LeanObject,
    mut v_inst_1946_: *mut crate::leanh::LeanObject,
    mut v_inst_1947_: *mut crate::leanh::LeanObject,
    mut v_maxArgs_1948_: *mut crate::leanh::LeanObject,
    mut v_xf_1949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1950_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg(
        v_inst_1945_,
        v_inst_1946_,
        v_inst_1947_,
        v_maxArgs_1948_,
        v_xf_1949_,
    );
    return v___x_1950_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(
    mut v_inst_1951_: *mut crate::leanh::LeanObject,
    mut v_x_1952_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1954_ = l_Lean_Expr_bindingDomain_x21(v_____do__lift_1953_);
    v___x_1955_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1956_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1951_,
        v___x_1954_,
        v___x_1955_,
        v_x_1952_,
    );
    return v___x_1956_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed(
    mut v_inst_1957_: *mut crate::leanh::LeanObject,
    mut v_x_1958_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(
        v_inst_1957_,
        v_x_1958_,
        v_____do__lift_1959_,
    );
    crate::leanh::lean_dec_ref(v_____do__lift_1959_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(
    mut v_inst_1961_: *mut crate::leanh::LeanObject,
    mut v_inst_1962_: *mut crate::leanh::LeanObject,
    mut v_inst_1963_: *mut crate::leanh::LeanObject,
    mut v_x_1964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_1965_ = crate::leanh::lean_ctor_get(v_inst_1961_, 1);
    crate::leanh::lean_inc(v_toBind_1965_);
    v___f_1966_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1966_, 0, v_inst_1963_);
    crate::leanh::lean_closure_set(v___f_1966_, 1, v_x_1964_);
    v___x_1967_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1961_, v_inst_1962_);
    v___x_1968_ = crate::leanh::lean_apply_4(
        v_toBind_1965_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1967_,
        v___f_1966_,
    );
    return v___x_1968_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain(
    mut v_00_u03b1_1969_: *mut crate::leanh::LeanObject,
    mut v_m_1970_: *mut crate::leanh::LeanObject,
    mut v_inst_1971_: *mut crate::leanh::LeanObject,
    mut v_inst_1972_: *mut crate::leanh::LeanObject,
    mut v_inst_1973_: *mut crate::leanh::LeanObject,
    mut v_x_1974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(
        v_inst_1971_,
        v_inst_1972_,
        v_inst_1973_,
        v_x_1974_,
    );
    return v___x_1975_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(
    mut v_e_1976_: *mut crate::leanh::LeanObject,
    mut v_fvar_1977_: *mut crate::leanh::LeanObject,
    mut v_x_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_b_1980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1981_ = l_Lean_Expr_bindingBody_x21(v_e_1976_);
    v___x_1982_ = lean_expr_instantiate1(v___x_1981_, v_fvar_1977_);
    crate::leanh::lean_dec_ref(v___x_1981_);
    v___x_1983_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1984_ = crate::leanh::lean_apply_1(v_x_1978_, v_b_1980_);
    v___x_1985_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1979_,
        v___x_1982_,
        v___x_1983_,
        v___x_1984_,
    );
    return v___x_1985_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed(
    mut v_e_1986_: *mut crate::leanh::LeanObject,
    mut v_fvar_1987_: *mut crate::leanh::LeanObject,
    mut v_x_1988_: *mut crate::leanh::LeanObject,
    mut v_inst_1989_: *mut crate::leanh::LeanObject,
    mut v_b_1990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(
        v_e_1986_,
        v_fvar_1987_,
        v_x_1988_,
        v_inst_1989_,
        v_b_1990_,
    );
    crate::leanh::lean_dec_ref(v_fvar_1987_);
    crate::leanh::lean_dec_ref(v_e_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1(
    mut v_e_1992_: *mut crate::leanh::LeanObject,
    mut v_x_1993_: *mut crate::leanh::LeanObject,
    mut v_inst_1994_: *mut crate::leanh::LeanObject,
    mut v_v_1995_: *mut crate::leanh::LeanObject,
    mut v_toBind_1996_: *mut crate::leanh::LeanObject,
    mut v_fvar_1997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_fvar_1997_);
    v___f_1998_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1998_, 0, v_e_1992_);
    crate::leanh::lean_closure_set(v___f_1998_, 1, v_fvar_1997_);
    crate::leanh::lean_closure_set(v___f_1998_, 2, v_x_1993_);
    crate::leanh::lean_closure_set(v___f_1998_, 3, v_inst_1994_);
    v___x_1999_ = crate::leanh::lean_apply_1(v_v_1995_, v_fvar_1997_);
    v___x_2000_ = crate::leanh::lean_apply_4(
        v_toBind_1996_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1999_,
        v___f_1998_,
    );
    return v___x_2000_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2(
    mut v_x_2001_: *mut crate::leanh::LeanObject,
    mut v_inst_2002_: *mut crate::leanh::LeanObject,
    mut v_v_2003_: *mut crate::leanh::LeanObject,
    mut v_toBind_2004_: *mut crate::leanh::LeanObject,
    mut v_inst_2005_: *mut crate::leanh::LeanObject,
    mut v_inst_2006_: *mut crate::leanh::LeanObject,
    mut v_n_2007_: *mut crate::leanh::LeanObject,
    mut v_e_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_e_2008_);
    v___f_2009_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2009_, 0, v_e_2008_);
    crate::leanh::lean_closure_set(v___f_2009_, 1, v_x_2001_);
    crate::leanh::lean_closure_set(v___f_2009_, 2, v_inst_2002_);
    crate::leanh::lean_closure_set(v___f_2009_, 3, v_v_2003_);
    crate::leanh::lean_closure_set(v___f_2009_, 4, v_toBind_2004_);
    v___x_2010_ = l_Lean_Expr_binderInfo(v_e_2008_);
    v___x_2011_ = l_Lean_Expr_bindingDomain_x21(v_e_2008_);
    crate::leanh::lean_dec_ref(v_e_2008_);
    v___x_2012_ = 0;
    v___x_2013_ = l_Lean_Meta_withLocalDecl___redArg(
        v_inst_2005_,
        v_inst_2006_,
        v_n_2007_,
        v___x_2010_,
        v___x_2011_,
        v___f_2009_,
        v___x_2012_,
    );
    return v___x_2013_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(
    mut v_inst_2014_: *mut crate::leanh::LeanObject,
    mut v_inst_2015_: *mut crate::leanh::LeanObject,
    mut v_inst_2016_: *mut crate::leanh::LeanObject,
    mut v_inst_2017_: *mut crate::leanh::LeanObject,
    mut v_n_2018_: *mut crate::leanh::LeanObject,
    mut v_v_2019_: *mut crate::leanh::LeanObject,
    mut v_x_2020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2021_ = crate::leanh::lean_ctor_get(v_inst_2014_, 1);
    crate::leanh::lean_inc_n(v_toBind_2021_, 2);
    crate::leanh::lean_inc_ref(v_inst_2014_);
    v___f_2022_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2022_, 0, v_x_2020_);
    crate::leanh::lean_closure_set(v___f_2022_, 1, v_inst_2016_);
    crate::leanh::lean_closure_set(v___f_2022_, 2, v_v_2019_);
    crate::leanh::lean_closure_set(v___f_2022_, 3, v_toBind_2021_);
    crate::leanh::lean_closure_set(v___f_2022_, 4, v_inst_2017_);
    crate::leanh::lean_closure_set(v___f_2022_, 5, v_inst_2014_);
    crate::leanh::lean_closure_set(v___f_2022_, 6, v_n_2018_);
    v___x_2023_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2014_, v_inst_2015_);
    v___x_2024_ = crate::leanh::lean_apply_4(
        v_toBind_2021_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2023_,
        v___f_2022_,
    );
    return v___x_2024_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27(
    mut v_00_u03b1_2025_: *mut crate::leanh::LeanObject,
    mut v_m_2026_: *mut crate::leanh::LeanObject,
    mut v_inst_2027_: *mut crate::leanh::LeanObject,
    mut v_inst_2028_: *mut crate::leanh::LeanObject,
    mut v_inst_2029_: *mut crate::leanh::LeanObject,
    mut v_inst_2030_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2031_: *mut crate::leanh::LeanObject,
    mut v_n_2032_: *mut crate::leanh::LeanObject,
    mut v_v_2033_: *mut crate::leanh::LeanObject,
    mut v_x_2034_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2035_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(
        v_inst_2027_,
        v_inst_2028_,
        v_inst_2029_,
        v_inst_2030_,
        v_n_2032_,
        v_v_2033_,
        v_x_2034_,
    );
    return v___x_2035_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(
    mut v_x_2036_: *mut crate::leanh::LeanObject,
    mut v_x_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_2036_);
    return v_x_2036_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed(
    mut v_x_2038_: *mut crate::leanh::LeanObject,
    mut v_x_2039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2040_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(
        v_x_2038_, v_x_2039_,
    );
    crate::leanh::lean_dec(v_x_2038_);
    return v_res_2040_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(
    mut v_toPure_2041_: *mut crate::leanh::LeanObject,
    mut v_x_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = crate::leanh::lean_box(0);
    v___x_2044_ =
        crate::leanh::lean_apply_2(v_toPure_2041_, crate::leanh::lean_box(0), v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed(
    mut v_toPure_2045_: *mut crate::leanh::LeanObject,
    mut v_x_2046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(
        v_toPure_2045_,
        v_x_2046_,
    );
    crate::leanh::lean_dec_ref(v_x_2046_);
    return v_res_2047_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(
    mut v_inst_2048_: *mut crate::leanh::LeanObject,
    mut v_inst_2049_: *mut crate::leanh::LeanObject,
    mut v_inst_2050_: *mut crate::leanh::LeanObject,
    mut v_inst_2051_: *mut crate::leanh::LeanObject,
    mut v_n_2052_: *mut crate::leanh::LeanObject,
    mut v_x_2053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2054_ = crate::leanh::lean_ctor_get(v_inst_2048_, 0);
    v_toPure_2055_ = crate::leanh::lean_ctor_get(v_toApplicative_2054_, 1);
    v___f_2056_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2056_, 0, v_x_2053_);
    crate::leanh::lean_inc(v_toPure_2055_);
    v___f_2057_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2057_, 0, v_toPure_2055_);
    v___x_2058_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg(
        v_inst_2048_,
        v_inst_2049_,
        v_inst_2050_,
        v_inst_2051_,
        v_n_2052_,
        v___f_2057_,
        v___f_2056_,
    );
    return v___x_2058_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody(
    mut v_00_u03b1_2059_: *mut crate::leanh::LeanObject,
    mut v_m_2060_: *mut crate::leanh::LeanObject,
    mut v_inst_2061_: *mut crate::leanh::LeanObject,
    mut v_inst_2062_: *mut crate::leanh::LeanObject,
    mut v_inst_2063_: *mut crate::leanh::LeanObject,
    mut v_inst_2064_: *mut crate::leanh::LeanObject,
    mut v_n_2065_: *mut crate::leanh::LeanObject,
    mut v_x_2066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2067_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(
        v_inst_2061_,
        v_inst_2062_,
        v_inst_2063_,
        v_inst_2064_,
        v_n_2065_,
        v_x_2066_,
    );
    return v___x_2067_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2072_ = crate::leanh::lean_unsigned_to_nat(34);
    v___x_2073_ = crate::leanh::lean_unsigned_to_nat(110);
    v___x_2074_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1;
    v___x_2075_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0;
    v___x_2076_ = l_mkPanicMessageWithDecl(
        v___x_2075_,
        v___x_2074_,
        v___x_2073_,
        v___x_2072_,
        v___x_2071_,
    );
    return v___x_2076_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(
    mut v_inst_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
    mut v___x_2079_: *mut crate::leanh::LeanObject,
    mut v_____x_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2080_) == 11 {
        let mut v_struct_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_struct_2081_ = crate::leanh::lean_ctor_get(v_____x_2080_, 2);
        crate::leanh::lean_inc_ref(v_struct_2081_);
        crate::leanh::lean_dec_ref_known(v_____x_2080_, 3);
        v___x_2082_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2083_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2077_,
            v_struct_2081_,
            v___x_2082_,
            v_x_2078_,
        );
        return v___x_2083_;
    } else {
        let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____x_2080_);
        crate::leanh::lean_dec(v_x_2078_);
        crate::leanh::lean_dec(v_inst_2077_);
        v___x_2084_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3);
        v___x_2085_ = l_panic___redArg(v___x_2079_, v___x_2084_);
        return v___x_2085_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed(
    mut v_inst_2086_: *mut crate::leanh::LeanObject,
    mut v_x_2087_: *mut crate::leanh::LeanObject,
    mut v___x_2088_: *mut crate::leanh::LeanObject,
    mut v_____x_2089_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(
        v_inst_2086_,
        v_x_2087_,
        v___x_2088_,
        v_____x_2089_,
    );
    crate::leanh::lean_dec(v___x_2088_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(
    mut v_inst_2091_: *mut crate::leanh::LeanObject,
    mut v_inst_2092_: *mut crate::leanh::LeanObject,
    mut v_inst_2093_: *mut crate::leanh::LeanObject,
    mut v_inst_2094_: *mut crate::leanh::LeanObject,
    mut v_x_2095_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2096_ = crate::leanh::lean_ctor_get(v_inst_2092_, 1);
    crate::leanh::lean_inc(v_toBind_2096_);
    crate::leanh::lean_inc_ref(v_inst_2092_);
    v___x_2097_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2092_, v_inst_2093_);
    v___x_2098_ = l_instInhabitedOfMonad___redArg(v_inst_2092_, v_inst_2091_);
    v___f_2099_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2099_, 0, v_inst_2094_);
    crate::leanh::lean_closure_set(v___f_2099_, 1, v_x_2095_);
    crate::leanh::lean_closure_set(v___f_2099_, 2, v___x_2098_);
    v___x_2100_ = crate::leanh::lean_apply_4(
        v_toBind_2096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2097_,
        v___f_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj(
    mut v_00_u03b1_2101_: *mut crate::leanh::LeanObject,
    mut v_inst_2102_: *mut crate::leanh::LeanObject,
    mut v_m_2103_: *mut crate::leanh::LeanObject,
    mut v_inst_2104_: *mut crate::leanh::LeanObject,
    mut v_inst_2105_: *mut crate::leanh::LeanObject,
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2108_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(
        v_inst_2102_,
        v_inst_2104_,
        v_inst_2105_,
        v_inst_2106_,
        v_x_2107_,
    );
    return v___x_2108_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0(
    mut v_expr_2109_: *mut crate::leanh::LeanObject,
    mut v_ctx_2110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_unused_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2111_ = crate::leanh::lean_ctor_get(v_ctx_2110_, 1);
                v_isSharedCheck_2118_ = (!crate::leanh::lean_is_exclusive(v_ctx_2110_)) as u8;
                if v_isSharedCheck_2118_ == 0 {
                    v_unused_2119_ = crate::leanh::lean_ctor_get(v_ctx_2110_, 0);
                    crate::leanh::lean_dec(v_unused_2119_);
                    v___x_2113_ = v_ctx_2110_;
                    v_isShared_2114_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_pos_2111_);
                    crate::leanh::lean_dec(v_ctx_2110_);
                    v___x_2113_ = crate::leanh::lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2114_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2113_, 0, v_expr_2109_);
                    v___x_2116_ = v___x_2113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_expr_2109_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_pos_2111_);
                    v___x_2116_ = v_reuseFailAlloc_2117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2122_ = crate::leanh::lean_unsigned_to_nat(33);
    v___x_2123_ = crate::leanh::lean_unsigned_to_nat(114);
    v___x_2124_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0;
    v___x_2125_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0;
    v___x_2126_ = l_mkPanicMessageWithDecl(
        v___x_2125_,
        v___x_2124_,
        v___x_2123_,
        v___x_2122_,
        v___x_2121_,
    );
    return v___x_2126_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(
    mut v_inst_2127_: *mut crate::leanh::LeanObject,
    mut v_x_2128_: *mut crate::leanh::LeanObject,
    mut v___x_2129_: *mut crate::leanh::LeanObject,
    mut v_____x_2130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2130_) == 10 {
        let mut v_expr_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_expr_2131_ = crate::leanh::lean_ctor_get(v_____x_2130_, 1);
        crate::leanh::lean_inc_ref(v_expr_2131_);
        crate::leanh::lean_dec_ref_known(v_____x_2130_, 2);
        v___f_2132_ = crate::leanh::lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0
                as *mut core::ffi::c_void,
            2,
            1,
        );
        crate::leanh::lean_closure_set(v___f_2132_, 0, v_expr_2131_);
        v___x_2133_ = crate::leanh::lean_apply_3(
            v_inst_2127_,
            crate::leanh::lean_box(0),
            v___f_2132_,
            v_x_2128_,
        );
        return v___x_2133_;
    } else {
        let mut v___x_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____x_2130_);
        crate::leanh::lean_dec(v_x_2128_);
        crate::leanh::lean_dec(v_inst_2127_);
        v___x_2134_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1);
        v___x_2135_ = l_panic___redArg(v___x_2129_, v___x_2134_);
        return v___x_2135_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed(
    mut v_inst_2136_: *mut crate::leanh::LeanObject,
    mut v_x_2137_: *mut crate::leanh::LeanObject,
    mut v___x_2138_: *mut crate::leanh::LeanObject,
    mut v_____x_2139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(
        v_inst_2136_,
        v_x_2137_,
        v___x_2138_,
        v_____x_2139_,
    );
    crate::leanh::lean_dec(v___x_2138_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(
    mut v_inst_2141_: *mut crate::leanh::LeanObject,
    mut v_inst_2142_: *mut crate::leanh::LeanObject,
    mut v_inst_2143_: *mut crate::leanh::LeanObject,
    mut v_inst_2144_: *mut crate::leanh::LeanObject,
    mut v_x_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2146_ = crate::leanh::lean_ctor_get(v_inst_2142_, 1);
    crate::leanh::lean_inc(v_toBind_2146_);
    crate::leanh::lean_inc_ref(v_inst_2142_);
    v___x_2147_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2142_, v_inst_2143_);
    v___x_2148_ = l_instInhabitedOfMonad___redArg(v_inst_2142_, v_inst_2141_);
    v___f_2149_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2149_, 0, v_inst_2144_);
    crate::leanh::lean_closure_set(v___f_2149_, 1, v_x_2145_);
    crate::leanh::lean_closure_set(v___f_2149_, 2, v___x_2148_);
    v___x_2150_ = crate::leanh::lean_apply_4(
        v_toBind_2146_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2147_,
        v___f_2149_,
    );
    return v___x_2150_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr(
    mut v_00_u03b1_2151_: *mut crate::leanh::LeanObject,
    mut v_inst_2152_: *mut crate::leanh::LeanObject,
    mut v_m_2153_: *mut crate::leanh::LeanObject,
    mut v_inst_2154_: *mut crate::leanh::LeanObject,
    mut v_inst_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_x_2157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2158_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(
        v_inst_2152_,
        v_inst_2154_,
        v_inst_2155_,
        v_inst_2156_,
        v_x_2157_,
    );
    return v___x_2158_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2161_ = crate::leanh::lean_unsigned_to_nat(38);
    v___x_2162_ = crate::leanh::lean_unsigned_to_nat(118);
    v___x_2163_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0;
    v___x_2164_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0;
    v___x_2165_ = l_mkPanicMessageWithDecl(
        v___x_2164_,
        v___x_2163_,
        v___x_2162_,
        v___x_2161_,
        v___x_2160_,
    );
    return v___x_2165_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(
    mut v_inst_2166_: *mut crate::leanh::LeanObject,
    mut v_x_2167_: *mut crate::leanh::LeanObject,
    mut v___x_2168_: *mut crate::leanh::LeanObject,
    mut v_____x_2169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2169_) == 8 {
        let mut v_type_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_type_2170_ = crate::leanh::lean_ctor_get(v_____x_2169_, 1);
        crate::leanh::lean_inc_ref(v_type_2170_);
        crate::leanh::lean_dec_ref_known(v_____x_2169_, 4);
        v___x_2171_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_2172_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2166_,
            v_type_2170_,
            v___x_2171_,
            v_x_2167_,
        );
        return v___x_2172_;
    } else {
        let mut v___x_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____x_2169_);
        crate::leanh::lean_dec(v_x_2167_);
        crate::leanh::lean_dec(v_inst_2166_);
        v___x_2173_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1);
        v___x_2174_ = l_panic___redArg(v___x_2168_, v___x_2173_);
        return v___x_2174_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed(
    mut v_inst_2175_: *mut crate::leanh::LeanObject,
    mut v_x_2176_: *mut crate::leanh::LeanObject,
    mut v___x_2177_: *mut crate::leanh::LeanObject,
    mut v_____x_2178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(
        v_inst_2175_,
        v_x_2176_,
        v___x_2177_,
        v_____x_2178_,
    );
    crate::leanh::lean_dec(v___x_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(
    mut v_inst_2180_: *mut crate::leanh::LeanObject,
    mut v_inst_2181_: *mut crate::leanh::LeanObject,
    mut v_inst_2182_: *mut crate::leanh::LeanObject,
    mut v_inst_2183_: *mut crate::leanh::LeanObject,
    mut v_x_2184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2185_ = crate::leanh::lean_ctor_get(v_inst_2181_, 1);
    crate::leanh::lean_inc(v_toBind_2185_);
    crate::leanh::lean_inc_ref(v_inst_2181_);
    v___x_2186_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2181_, v_inst_2182_);
    v___x_2187_ = l_instInhabitedOfMonad___redArg(v_inst_2181_, v_inst_2180_);
    v___f_2188_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2188_, 0, v_inst_2183_);
    crate::leanh::lean_closure_set(v___f_2188_, 1, v_x_2184_);
    crate::leanh::lean_closure_set(v___f_2188_, 2, v___x_2187_);
    v___x_2189_ = crate::leanh::lean_apply_4(
        v_toBind_2185_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2186_,
        v___f_2188_,
    );
    return v___x_2189_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType(
    mut v_00_u03b1_2190_: *mut crate::leanh::LeanObject,
    mut v_inst_2191_: *mut crate::leanh::LeanObject,
    mut v_m_2192_: *mut crate::leanh::LeanObject,
    mut v_inst_2193_: *mut crate::leanh::LeanObject,
    mut v_inst_2194_: *mut crate::leanh::LeanObject,
    mut v_inst_2195_: *mut crate::leanh::LeanObject,
    mut v_x_2196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2197_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(
        v_inst_2191_,
        v_inst_2193_,
        v_inst_2194_,
        v_inst_2195_,
        v_x_2196_,
    );
    return v___x_2197_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2199_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2200_ = crate::leanh::lean_unsigned_to_nat(38);
    v___x_2201_ = crate::leanh::lean_unsigned_to_nat(122);
    v___x_2202_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0;
    v___x_2203_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0;
    v___x_2204_ = l_mkPanicMessageWithDecl(
        v___x_2203_,
        v___x_2202_,
        v___x_2201_,
        v___x_2200_,
        v___x_2199_,
    );
    return v___x_2204_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(
    mut v_inst_2205_: *mut crate::leanh::LeanObject,
    mut v_x_2206_: *mut crate::leanh::LeanObject,
    mut v___x_2207_: *mut crate::leanh::LeanObject,
    mut v_____x_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2208_) == 8 {
        let mut v_value_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_value_2209_ = crate::leanh::lean_ctor_get(v_____x_2208_, 2);
        crate::leanh::lean_inc_ref(v_value_2209_);
        crate::leanh::lean_dec_ref_known(v_____x_2208_, 4);
        v___x_2210_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_2211_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2205_,
            v_value_2209_,
            v___x_2210_,
            v_x_2206_,
        );
        return v___x_2211_;
    } else {
        let mut v___x_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____x_2208_);
        crate::leanh::lean_dec(v_x_2206_);
        crate::leanh::lean_dec(v_inst_2205_);
        v___x_2212_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1);
        v___x_2213_ = l_panic___redArg(v___x_2207_, v___x_2212_);
        return v___x_2213_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed(
    mut v_inst_2214_: *mut crate::leanh::LeanObject,
    mut v_x_2215_: *mut crate::leanh::LeanObject,
    mut v___x_2216_: *mut crate::leanh::LeanObject,
    mut v_____x_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(
        v_inst_2214_,
        v_x_2215_,
        v___x_2216_,
        v_____x_2217_,
    );
    crate::leanh::lean_dec(v___x_2216_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(
    mut v_inst_2219_: *mut crate::leanh::LeanObject,
    mut v_inst_2220_: *mut crate::leanh::LeanObject,
    mut v_inst_2221_: *mut crate::leanh::LeanObject,
    mut v_inst_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2224_ = crate::leanh::lean_ctor_get(v_inst_2220_, 1);
    crate::leanh::lean_inc(v_toBind_2224_);
    crate::leanh::lean_inc_ref(v_inst_2220_);
    v___x_2225_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2220_, v_inst_2221_);
    v___x_2226_ = l_instInhabitedOfMonad___redArg(v_inst_2220_, v_inst_2219_);
    v___f_2227_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2227_, 0, v_inst_2222_);
    crate::leanh::lean_closure_set(v___f_2227_, 1, v_x_2223_);
    crate::leanh::lean_closure_set(v___f_2227_, 2, v___x_2226_);
    v___x_2228_ = crate::leanh::lean_apply_4(
        v_toBind_2224_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2225_,
        v___f_2227_,
    );
    return v___x_2228_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue(
    mut v_00_u03b1_2229_: *mut crate::leanh::LeanObject,
    mut v_inst_2230_: *mut crate::leanh::LeanObject,
    mut v_m_2231_: *mut crate::leanh::LeanObject,
    mut v_inst_2232_: *mut crate::leanh::LeanObject,
    mut v_inst_2233_: *mut crate::leanh::LeanObject,
    mut v_inst_2234_: *mut crate::leanh::LeanObject,
    mut v_x_2235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2236_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(
        v_inst_2230_,
        v_inst_2232_,
        v_inst_2233_,
        v_inst_2234_,
        v_x_2235_,
    );
    return v___x_2236_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(
    mut v_body_2237_: *mut crate::leanh::LeanObject,
    mut v_inst_2238_: *mut crate::leanh::LeanObject,
    mut v_x_2239_: *mut crate::leanh::LeanObject,
    mut v_fvar_2240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_b_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_b_2241_ = lean_expr_instantiate1(v_body_2237_, v_fvar_2240_);
    v___x_2242_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2243_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_2238_,
        v_b_2241_,
        v___x_2242_,
        v_x_2239_,
    );
    return v___x_2243_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed(
    mut v_body_2244_: *mut crate::leanh::LeanObject,
    mut v_inst_2245_: *mut crate::leanh::LeanObject,
    mut v_x_2246_: *mut crate::leanh::LeanObject,
    mut v_fvar_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2248_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(
        v_body_2244_,
        v_inst_2245_,
        v_x_2246_,
        v_fvar_2247_,
    );
    crate::leanh::lean_dec_ref(v_fvar_2247_);
    crate::leanh::lean_dec_ref(v_body_2244_);
    return v_res_2248_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2251_ = crate::leanh::lean_unsigned_to_nat(43);
    v___x_2252_ = crate::leanh::lean_unsigned_to_nat(126);
    v___x_2253_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0;
    v___x_2254_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0;
    v___x_2255_ = l_mkPanicMessageWithDecl(
        v___x_2254_,
        v___x_2253_,
        v___x_2252_,
        v___x_2251_,
        v___x_2250_,
    );
    return v___x_2255_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(
    mut v_inst_2256_: *mut crate::leanh::LeanObject,
    mut v_x_2257_: *mut crate::leanh::LeanObject,
    mut v_inst_2258_: *mut crate::leanh::LeanObject,
    mut v_inst_2259_: *mut crate::leanh::LeanObject,
    mut v___x_2260_: *mut crate::leanh::LeanObject,
    mut v_____x_2261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____x_2261_) == 8 {
        let mut v_declName_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_type_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_value_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_body_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_nondep_2266_: u8 = 0;
        let mut v___f_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: u8 = 0;
        let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_declName_2262_ = crate::leanh::lean_ctor_get(v_____x_2261_, 0);
        crate::leanh::lean_inc(v_declName_2262_);
        v_type_2263_ = crate::leanh::lean_ctor_get(v_____x_2261_, 1);
        crate::leanh::lean_inc_ref(v_type_2263_);
        v_value_2264_ = crate::leanh::lean_ctor_get(v_____x_2261_, 2);
        crate::leanh::lean_inc_ref(v_value_2264_);
        v_body_2265_ = crate::leanh::lean_ctor_get(v_____x_2261_, 3);
        crate::leanh::lean_inc_ref(v_body_2265_);
        v_nondep_2266_ = crate::leanh::lean_ctor_get_uint8(
            v_____x_2261_,
            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8) as u32,
        );
        crate::leanh::lean_dec_ref_known(v_____x_2261_, 4);
        v___f_2267_ = crate::leanh::lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_2267_, 0, v_body_2265_);
        crate::leanh::lean_closure_set(v___f_2267_, 1, v_inst_2256_);
        crate::leanh::lean_closure_set(v___f_2267_, 2, v_x_2257_);
        v___x_2268_ = 0;
        v___x_2269_ = l_Lean_Meta_withLetDecl___redArg(
            v_inst_2258_,
            v_inst_2259_,
            v_declName_2262_,
            v_type_2263_,
            v_value_2264_,
            v___f_2267_,
            v_nondep_2266_,
            v___x_2268_,
        );
        return v___x_2269_;
    } else {
        let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_____x_2261_);
        crate::leanh::lean_dec_ref(v_inst_2259_);
        crate::leanh::lean_dec_ref(v_inst_2258_);
        crate::leanh::lean_dec(v_x_2257_);
        crate::leanh::lean_dec(v_inst_2256_);
        v___x_2270_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1);
        v___x_2271_ = l_panic___redArg(v___x_2260_, v___x_2270_);
        return v___x_2271_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed(
    mut v_inst_2272_: *mut crate::leanh::LeanObject,
    mut v_x_2273_: *mut crate::leanh::LeanObject,
    mut v_inst_2274_: *mut crate::leanh::LeanObject,
    mut v_inst_2275_: *mut crate::leanh::LeanObject,
    mut v___x_2276_: *mut crate::leanh::LeanObject,
    mut v_____x_2277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(
        v_inst_2272_,
        v_x_2273_,
        v_inst_2274_,
        v_inst_2275_,
        v___x_2276_,
        v_____x_2277_,
    );
    crate::leanh::lean_dec(v___x_2276_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(
    mut v_inst_2279_: *mut crate::leanh::LeanObject,
    mut v_inst_2280_: *mut crate::leanh::LeanObject,
    mut v_inst_2281_: *mut crate::leanh::LeanObject,
    mut v_inst_2282_: *mut crate::leanh::LeanObject,
    mut v_inst_2283_: *mut crate::leanh::LeanObject,
    mut v_x_2284_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2285_ = crate::leanh::lean_ctor_get(v_inst_2280_, 1);
    crate::leanh::lean_inc(v_toBind_2285_);
    crate::leanh::lean_inc_ref_n(v_inst_2280_, 2);
    v___x_2286_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2280_, v_inst_2281_);
    v___x_2287_ = l_instInhabitedOfMonad___redArg(v_inst_2280_, v_inst_2279_);
    v___f_2288_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2288_, 0, v_inst_2282_);
    crate::leanh::lean_closure_set(v___f_2288_, 1, v_x_2284_);
    crate::leanh::lean_closure_set(v___f_2288_, 2, v_inst_2283_);
    crate::leanh::lean_closure_set(v___f_2288_, 3, v_inst_2280_);
    crate::leanh::lean_closure_set(v___f_2288_, 4, v___x_2287_);
    v___x_2289_ = crate::leanh::lean_apply_4(
        v_toBind_2285_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2286_,
        v___f_2288_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody(
    mut v_00_u03b1_2290_: *mut crate::leanh::LeanObject,
    mut v_inst_2291_: *mut crate::leanh::LeanObject,
    mut v_m_2292_: *mut crate::leanh::LeanObject,
    mut v_inst_2293_: *mut crate::leanh::LeanObject,
    mut v_inst_2294_: *mut crate::leanh::LeanObject,
    mut v_inst_2295_: *mut crate::leanh::LeanObject,
    mut v_inst_2296_: *mut crate::leanh::LeanObject,
    mut v_x_2297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2298_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(
        v_inst_2291_,
        v_inst_2293_,
        v_inst_2294_,
        v_inst_2295_,
        v_inst_2296_,
        v_x_2297_,
    );
    return v___x_2298_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(
    mut v_e_2299_: *mut crate::leanh::LeanObject,
    mut v_newPos_2300_: *mut crate::leanh::LeanObject,
    mut v_cfg_2301_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Lean_Expr_getAppFn(v_e_2299_);
    v___x_2303_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2303_, 0, v___x_2302_);
    crate::leanh::lean_ctor_set(v___x_2303_, 1, v_newPos_2300_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed(
    mut v_e_2304_: *mut crate::leanh::LeanObject,
    mut v_newPos_2305_: *mut crate::leanh::LeanObject,
    mut v_cfg_2306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2307_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(
        v_e_2304_,
        v_newPos_2305_,
        v_cfg_2306_,
    );
    crate::leanh::lean_dec_ref(v_cfg_2306_);
    crate::leanh::lean_dec_ref(v_e_2304_);
    return v_res_2307_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(
    mut v_e_2308_: *mut crate::leanh::LeanObject,
    mut v_inst_2309_: *mut crate::leanh::LeanObject,
    mut v_x_2310_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newPos_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_Expr_getAppNumArgs(v_e_2308_);
    v_newPos_2313_ = l_Lean_SubExpr_Pos_pushNaryFn(v___x_2312_, v_____do__lift_2311_);
    crate::leanh::lean_dec(v___x_2312_);
    v___f_2314_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2314_, 0, v_e_2308_);
    crate::leanh::lean_closure_set(v___f_2314_, 1, v_newPos_2313_);
    v___x_2315_ = crate::leanh::lean_apply_3(
        v_inst_2309_,
        crate::leanh::lean_box(0),
        v___f_2314_,
        v_x_2310_,
    );
    return v___x_2315_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed(
    mut v_e_2316_: *mut crate::leanh::LeanObject,
    mut v_inst_2317_: *mut crate::leanh::LeanObject,
    mut v_x_2318_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(
        v_e_2316_,
        v_inst_2317_,
        v_x_2318_,
        v_____do__lift_2319_,
    );
    crate::leanh::lean_dec(v_____do__lift_2319_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2(
    mut v_inst_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
    mut v_inst_2323_: *mut crate::leanh::LeanObject,
    mut v_inst_2324_: *mut crate::leanh::LeanObject,
    mut v_toBind_2325_: *mut crate::leanh::LeanObject,
    mut v_e_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2327_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2327_, 0, v_e_2326_);
    crate::leanh::lean_closure_set(v___f_2327_, 1, v_inst_2321_);
    crate::leanh::lean_closure_set(v___f_2327_, 2, v_x_2322_);
    v___x_2328_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_2323_, v_inst_2324_);
    v___x_2329_ = crate::leanh::lean_apply_4(
        v_toBind_2325_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2328_,
        v___f_2327_,
    );
    return v___x_2329_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(
    mut v_inst_2330_: *mut crate::leanh::LeanObject,
    mut v_inst_2331_: *mut crate::leanh::LeanObject,
    mut v_inst_2332_: *mut crate::leanh::LeanObject,
    mut v_x_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2334_ = crate::leanh::lean_ctor_get(v_inst_2330_, 1);
    crate::leanh::lean_inc_n(v_toBind_2334_, 2);
    crate::leanh::lean_inc(v_inst_2331_);
    crate::leanh::lean_inc_ref(v_inst_2330_);
    v___f_2335_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2335_, 0, v_inst_2332_);
    crate::leanh::lean_closure_set(v___f_2335_, 1, v_x_2333_);
    crate::leanh::lean_closure_set(v___f_2335_, 2, v_inst_2330_);
    crate::leanh::lean_closure_set(v___f_2335_, 3, v_inst_2331_);
    crate::leanh::lean_closure_set(v___f_2335_, 4, v_toBind_2334_);
    v___x_2336_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2330_, v_inst_2331_);
    v___x_2337_ = crate::leanh::lean_apply_4(
        v_toBind_2334_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2336_,
        v___f_2335_,
    );
    return v___x_2337_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn(
    mut v_00_u03b1_2338_: *mut crate::leanh::LeanObject,
    mut v_m_2339_: *mut crate::leanh::LeanObject,
    mut v_inst_2340_: *mut crate::leanh::LeanObject,
    mut v_inst_2341_: *mut crate::leanh::LeanObject,
    mut v_inst_2342_: *mut crate::leanh::LeanObject,
    mut v_x_2343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(
        v_inst_2340_,
        v_inst_2341_,
        v_inst_2342_,
        v_x_2343_,
    );
    return v___x_2344_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(
    mut v___x_2345_: *mut crate::leanh::LeanObject,
    mut v_args_2346_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2347_: *mut crate::leanh::LeanObject,
    mut v_newPos_2348_: *mut crate::leanh::LeanObject,
    mut v_cfg_2349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2350_ = lean_array_get_borrowed(v___x_2345_, v_args_2346_, v_argIdx_2347_);
    crate::leanh::lean_inc(v___x_2350_);
    v___x_2351_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2350_);
    crate::leanh::lean_ctor_set(v___x_2351_, 1, v_newPos_2348_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed(
    mut v___x_2352_: *mut crate::leanh::LeanObject,
    mut v_args_2353_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2354_: *mut crate::leanh::LeanObject,
    mut v_newPos_2355_: *mut crate::leanh::LeanObject,
    mut v_cfg_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(
        v___x_2352_,
        v_args_2353_,
        v_argIdx_2354_,
        v_newPos_2355_,
        v_cfg_2356_,
    );
    crate::leanh::lean_dec_ref(v_cfg_2356_);
    crate::leanh::lean_dec(v_argIdx_2354_);
    crate::leanh::lean_dec_ref(v_args_2353_);
    crate::leanh::lean_dec_ref(v___x_2352_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(
    mut v_args_2358_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2359_: *mut crate::leanh::LeanObject,
    mut v___x_2360_: *mut crate::leanh::LeanObject,
    mut v_inst_2361_: *mut crate::leanh::LeanObject,
    mut v_x_2362_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newPos_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2364_ = lean_array_get_size(v_args_2358_);
    v_newPos_2365_ =
        l_Lean_SubExpr_Pos_pushNaryArg(v___x_2364_, v_argIdx_2359_, v_____do__lift_2363_);
    v___f_2366_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2366_, 0, v___x_2360_);
    crate::leanh::lean_closure_set(v___f_2366_, 1, v_args_2358_);
    crate::leanh::lean_closure_set(v___f_2366_, 2, v_argIdx_2359_);
    crate::leanh::lean_closure_set(v___f_2366_, 3, v_newPos_2365_);
    v___x_2367_ = crate::leanh::lean_apply_3(
        v_inst_2361_,
        crate::leanh::lean_box(0),
        v___f_2366_,
        v_x_2362_,
    );
    return v___x_2367_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed(
    mut v_args_2368_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2369_: *mut crate::leanh::LeanObject,
    mut v___x_2370_: *mut crate::leanh::LeanObject,
    mut v_inst_2371_: *mut crate::leanh::LeanObject,
    mut v_x_2372_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(
        v_args_2368_,
        v_argIdx_2369_,
        v___x_2370_,
        v_inst_2371_,
        v_x_2372_,
        v_____do__lift_2373_,
    );
    crate::leanh::lean_dec(v_____do__lift_2373_);
    return v_res_2374_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2375_ = crate::leanh::lean_box(0);
    v_dummy_2376_ = l_Lean_Expr_sort___override(v___x_2375_);
    return v_dummy_2376_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2(
    mut v_argIdx_2377_: *mut crate::leanh::LeanObject,
    mut v___x_2378_: *mut crate::leanh::LeanObject,
    mut v_inst_2379_: *mut crate::leanh::LeanObject,
    mut v_x_2380_: *mut crate::leanh::LeanObject,
    mut v_inst_2381_: *mut crate::leanh::LeanObject,
    mut v_inst_2382_: *mut crate::leanh::LeanObject,
    mut v_toBind_2383_: *mut crate::leanh::LeanObject,
    mut v_e_2384_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_dummy_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_dummy_2385_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0,
    );
    v_nargs_2386_ = l_Lean_Expr_getAppNumArgs(v_e_2384_);
    crate::leanh::lean_inc(v_nargs_2386_);
    v___x_2387_ = lean_mk_array(v_nargs_2386_, v_dummy_2385_);
    v___x_2388_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_2389_ = lean_nat_sub(v_nargs_2386_, v___x_2388_);
    crate::leanh::lean_dec(v_nargs_2386_);
    v_args_2390_ =
        l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2384_, v___x_2387_, v___x_2389_);
    v___f_2391_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_2391_, 0, v_args_2390_);
    crate::leanh::lean_closure_set(v___f_2391_, 1, v_argIdx_2377_);
    crate::leanh::lean_closure_set(v___f_2391_, 2, v___x_2378_);
    crate::leanh::lean_closure_set(v___f_2391_, 3, v_inst_2379_);
    crate::leanh::lean_closure_set(v___f_2391_, 4, v_x_2380_);
    v___x_2392_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_2381_, v_inst_2382_);
    v___x_2393_ = crate::leanh::lean_apply_4(
        v_toBind_2383_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2392_,
        v___f_2391_,
    );
    return v___x_2393_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(
    mut v_inst_2394_: *mut crate::leanh::LeanObject,
    mut v_inst_2395_: *mut crate::leanh::LeanObject,
    mut v_inst_2396_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2397_: *mut crate::leanh::LeanObject,
    mut v_x_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toBind_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toBind_2399_ = crate::leanh::lean_ctor_get(v_inst_2394_, 1);
    crate::leanh::lean_inc_n(v_toBind_2399_, 2);
    v___x_2400_ = l_Lean_instInhabitedExpr;
    crate::leanh::lean_inc(v_inst_2395_);
    crate::leanh::lean_inc_ref(v_inst_2394_);
    v___f_2401_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    crate::leanh::lean_closure_set(v___f_2401_, 0, v_argIdx_2397_);
    crate::leanh::lean_closure_set(v___f_2401_, 1, v___x_2400_);
    crate::leanh::lean_closure_set(v___f_2401_, 2, v_inst_2396_);
    crate::leanh::lean_closure_set(v___f_2401_, 3, v_x_2398_);
    crate::leanh::lean_closure_set(v___f_2401_, 4, v_inst_2394_);
    crate::leanh::lean_closure_set(v___f_2401_, 5, v_inst_2395_);
    crate::leanh::lean_closure_set(v___f_2401_, 6, v_toBind_2399_);
    v___x_2402_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2394_, v_inst_2395_);
    v___x_2403_ = crate::leanh::lean_apply_4(
        v_toBind_2399_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2402_,
        v___f_2401_,
    );
    return v___x_2403_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg(
    mut v_00_u03b1_2404_: *mut crate::leanh::LeanObject,
    mut v_m_2405_: *mut crate::leanh::LeanObject,
    mut v_inst_2406_: *mut crate::leanh::LeanObject,
    mut v_inst_2407_: *mut crate::leanh::LeanObject,
    mut v_inst_2408_: *mut crate::leanh::LeanObject,
    mut v_argIdx_2409_: *mut crate::leanh::LeanObject,
    mut v_x_2410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2411_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(
        v_inst_2406_,
        v_inst_2407_,
        v_inst_2408_,
        v_argIdx_2409_,
        v_x_2410_,
    );
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Lean_SubExpr_Pos_maxChildren;
    v___x_2413_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_2414_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2414_, 0, v___x_2413_);
    crate::leanh::lean_ctor_set(v___x_2414_, 1, v___x_2412_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default;
    return v___x_2416_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(
    mut v_iter_2417_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_curr_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_curr_2418_ = crate::leanh::lean_ctor_get(v_iter_2417_, 0);
    crate::leanh::lean_inc(v_curr_2418_);
    return v_curr_2418_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos___boxed(
    mut v_iter_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(v_iter_2419_);
    crate::leanh::lean_dec_ref(v_iter_2419_);
    return v_res_2420_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(
    mut v_iter_2421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_curr_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_top_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_curr_2422_ = crate::leanh::lean_ctor_get(v_iter_2421_, 0);
                v_top_2423_ = crate::leanh::lean_ctor_get(v_iter_2421_, 1);
                v_isSharedCheck_2440_ = (!crate::leanh::lean_is_exclusive(v_iter_2421_)) as u8;
                if v_isSharedCheck_2440_ == 0 {
                    v___x_2425_ = v_iter_2421_;
                    v_isShared_2426_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_top_2423_);
                    crate::leanh::lean_inc(v_curr_2422_);
                    crate::leanh::lean_dec(v_iter_2421_);
                    v___x_2425_ = crate::leanh::lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2428_ = lean_nat_add(v_curr_2422_, v___x_2427_);
                crate::leanh::lean_dec(v_curr_2422_);
                v___x_2429_ = lean_nat_dec_eq(v___x_2428_, v_top_2423_);
                if v___x_2429_ == 0 {
                    if v_isShared_2426_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2428_);
                        v___x_2431_ = v___x_2425_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2432_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2428_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_top_2423_);
                        v___x_2431_ = v_reuseFailAlloc_2432_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2428_);
                    v___x_2433_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_2434_ = lean_nat_mul(v___x_2433_, v_top_2423_);
                    v___x_2435_ = l_Lean_SubExpr_Pos_maxChildren;
                    v___x_2436_ = lean_nat_mul(v___x_2435_, v_top_2423_);
                    crate::leanh::lean_dec(v_top_2423_);
                    if v_isShared_2426_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2425_, 1, v___x_2436_);
                        crate::leanh::lean_ctor_set(v___x_2425_, 0, v___x_2434_);
                        v___x_2438_ = v___x_2425_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2434_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2436_);
                        v___x_2438_ = v_reuseFailAlloc_2439_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2431_;
            }
            3 => {
                return v___x_2438_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0(
    mut v_s_2441_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2442_ = crate::leanh::lean_box(0);
    v___x_2443_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_s_2441_);
    v___x_2444_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2444_, 0, v___x_2442_);
    crate::leanh::lean_ctor_set(v___x_2444_, 1, v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1(
    mut v_toPure_2445_: *mut crate::leanh::LeanObject,
    mut v_curr_2446_: *mut crate::leanh::LeanObject,
    mut v_____r_2447_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2448_ =
        crate::leanh::lean_apply_2(v_toPure_2445_, crate::leanh::lean_box(0), v_curr_2446_);
    return v___x_2448_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2(
    mut v_toPure_2449_: *mut crate::leanh::LeanObject,
    mut v_modifyGet_2450_: *mut crate::leanh::LeanObject,
    mut v___f_2451_: *mut crate::leanh::LeanObject,
    mut v_toBind_2452_: *mut crate::leanh::LeanObject,
    mut v_iter_2453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_curr_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_curr_2454_ = crate::leanh::lean_ctor_get(v_iter_2453_, 0);
    crate::leanh::lean_inc(v_curr_2454_);
    crate::leanh::lean_dec_ref(v_iter_2453_);
    v___f_2455_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2455_, 0, v_toPure_2449_);
    crate::leanh::lean_closure_set(v___f_2455_, 1, v_curr_2454_);
    v___x_2456_ =
        crate::leanh::lean_apply_2(v_modifyGet_2450_, crate::leanh::lean_box(0), v___f_2451_);
    v___x_2457_ = crate::leanh::lean_apply_4(
        v_toBind_2452_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2456_,
        v___f_2455_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(
    mut v_inst_2459_: *mut crate::leanh::LeanObject,
    mut v_inst_2460_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_get_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2461_ = crate::leanh::lean_ctor_get(v_inst_2459_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2461_);
    v_toBind_2462_ = crate::leanh::lean_ctor_get(v_inst_2459_, 1);
    crate::leanh::lean_inc_n(v_toBind_2462_, 2);
    crate::leanh::lean_dec_ref(v_inst_2459_);
    v_get_2463_ = crate::leanh::lean_ctor_get(v_inst_2460_, 0);
    crate::leanh::lean_inc(v_get_2463_);
    v_modifyGet_2464_ = crate::leanh::lean_ctor_get(v_inst_2460_, 2);
    crate::leanh::lean_inc(v_modifyGet_2464_);
    crate::leanh::lean_dec_ref(v_inst_2460_);
    v_toPure_2465_ = crate::leanh::lean_ctor_get(v_toApplicative_2461_, 1);
    crate::leanh::lean_inc(v_toPure_2465_);
    crate::leanh::lean_dec_ref(v_toApplicative_2461_);
    v___f_2466_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0;
    v___f_2467_ = crate::leanh::lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v___f_2467_, 0, v_toPure_2465_);
    crate::leanh::lean_closure_set(v___f_2467_, 1, v_modifyGet_2464_);
    crate::leanh::lean_closure_set(v___f_2467_, 2, v___f_2466_);
    crate::leanh::lean_closure_set(v___f_2467_, 3, v_toBind_2462_);
    v___x_2468_ = crate::leanh::lean_apply_4(
        v_toBind_2462_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_get_2463_,
        v___f_2467_,
    );
    return v___x_2468_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos(
    mut v_m_2469_: *mut crate::leanh::LeanObject,
    mut v_inst_2470_: *mut crate::leanh::LeanObject,
    mut v_inst_2471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(v_inst_2470_, v_inst_2471_);
    return v___x_2472_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default =
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default();
    crate::leanh::lean_mark_persistent(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default,
    );
    l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator =
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator();
    crate::leanh::lean_mark_persistent(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator,
    );
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(
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
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_SubExpr(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
}

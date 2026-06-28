// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.SubExpr
// Imports: Lean.SubExpr
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_mkStr1, l_instInhabitedOfMonad___redArg, l_panic___redArg,
};
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
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_mul, lean_nat_sub,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_instantiate1;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__0_value) as *mut LeanObject,14231257465488249300 as *mut LeanObject] };
static mut l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value:
    LeanStringObject<39> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__0_value
) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value:
    LeanStringObject<48> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__1_value
) as *mut LeanObject;
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value:
    LeanStringObject<34> = LeanStringObject {
    m_header: LeanObject {
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
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2_value
) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 77, 68, 97, 116, 97, 69, 120, 112, 114, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value: LeanStringObject<54> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 86, 97, 114, 84, 121, 112, 101, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value: LeanStringObject<52> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 52, m_capacity: 52, m_length: 51, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value: LeanStringObject<51> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 51, m_capacity: 51, m_length: 50, m_data: [76, 101, 97, 110, 46, 80, 114, 101, 116, 116, 121, 80, 114, 105, 110, 116, 101, 114, 46, 68, 101, 108, 97, 98, 111, 114, 97, 116, 111, 114, 46, 83, 117, 98, 69, 120, 112, 114, 46, 119, 105, 116, 104, 76, 101, 116, 66, 111, 100, 121, 0]};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__0_value
) as *mut LeanObject;
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value:
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
    m_fun: l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0_value
) as *mut LeanObject;
pub unsafe fn l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0(
    mut v_o_1240_: *mut LeanObject,
    mut v_k_1241_: *mut LeanObject,
    mut v_v_1242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_1244_: u8 = 0;
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1247_: u8 = 0;
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: u8 = 0;
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_map_1243_ = lean_ctor_get(v_o_1240_, 0);
                v_hasTrace_1244_ = lean_ctor_get_uint8(
                    v_o_1240_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_1257_ = (!lean_is_exclusive(v_o_1240_)) as u8;
                if v_isSharedCheck_1257_ == 0 {
                    v___x_1246_ = v_o_1240_;
                    v_isShared_1247_ = v_isSharedCheck_1257_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_map_1243_);
                    lean_dec(v_o_1240_);
                    v___x_1246_ = lean_box(0);
                    v_isShared_1247_ = v_isSharedCheck_1257_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_k_1241_);
                v___x_1248_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_1241_, v_v_1242_, v_map_1243_);
                if v_hasTrace_1244_ == 0 {
                    v___x_1249_ = l_Lean_Options_set___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__0___closed__1;
                    v___x_1250_ = l_Lean_Name_isPrefixOf(v___x_1249_, v_k_1241_);
                    lean_dec(v_k_1241_);
                    if v_isShared_1247_ == 0 {
                        lean_ctor_set(v___x_1246_, 0, v___x_1248_);
                        v___x_1252_ = v___x_1246_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1253_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1253_, 0, v___x_1248_);
                        v___x_1252_ = v_reuseFailAlloc_1253_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_k_1241_);
                    if v_isShared_1247_ == 0 {
                        lean_ctor_set(v___x_1246_, 0, v___x_1248_);
                        v___x_1255_ = v___x_1246_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1256_ = lean_alloc_ctor(0, 1, (1) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1256_, 0, v___x_1248_);
                        lean_ctor_set_uint8(
                            v_reuseFailAlloc_1256_,
                            (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                            v_hasTrace_1244_,
                        );
                        v___x_1255_ = v_reuseFailAlloc_1256_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_1252_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_k_1258_: *mut LeanObject,
    mut v_v_1259_: *mut LeanObject,
    mut v_t_1260_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1268_: u8 = 0;
    let mut v___x_1269_: u8 = 0;
    let mut v___x_1270_: u8 = 0;
    let mut v_impl_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: u8 = 0;
    let mut v___x_1282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1289_: u8 = 0;
    let mut v_size_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: u8 = 0;
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1301_: u8 = 0;
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1313_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1326_: u8 = 0;
    let mut v_unused_1327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1339_: u8 = 0;
    let mut v___x_1341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1343_: u8 = 0;
    let mut v_unused_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1350_: u8 = 0;
    let mut v_unused_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1362_: u8 = 0;
    let mut v_k_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1367_: u8 = 0;
    let mut v___x_1368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1378_: u8 = 0;
    let mut v_unused_1379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1382_: u8 = 0;
    let mut v_unused_1383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1398_: u8 = 0;
    let mut v_unused_1399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1419_: u8 = 0;
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1427_: u8 = 0;
    let mut v_size_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: u8 = 0;
    let mut v___x_1438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1439_: u8 = 0;
    let mut v___x_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1465_: u8 = 0;
    let mut v_unused_1466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1483_: u8 = 0;
    let mut v_unused_1484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1490_: u8 = 0;
    let mut v_unused_1491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1502_: u8 = 0;
    let mut v___x_1503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1510_: u8 = 0;
    let mut v_unused_1511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1518_: u8 = 0;
    let mut v_k_1519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1523_: u8 = 0;
    let mut v___x_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1534_: u8 = 0;
    let mut v_unused_1535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1538_: u8 = 0;
    let mut v_unused_1539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1546_: u8 = 0;
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1260_) == 0 {
                    v_size_1261_ = lean_ctor_get(v_t_1260_, 0);
                    v_k_1262_ = lean_ctor_get(v_t_1260_, 1);
                    v_v_1263_ = lean_ctor_get(v_t_1260_, 2);
                    v_l_1264_ = lean_ctor_get(v_t_1260_, 3);
                    v_r_1265_ = lean_ctor_get(v_t_1260_, 4);
                    v_isSharedCheck_1546_ = (!lean_is_exclusive(v_t_1260_)) as u8;
                    if v_isSharedCheck_1546_ == 0 {
                        v___x_1267_ = v_t_1260_;
                        v_isShared_1268_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1265_);
                        lean_inc(v_l_1264_);
                        lean_inc(v_v_1263_);
                        lean_inc(v_k_1262_);
                        lean_inc(v_size_1261_);
                        lean_dec(v_t_1260_);
                        v___x_1267_ = lean_box(0);
                        v_isShared_1268_ = v_isSharedCheck_1546_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1547_ = lean_unsigned_to_nat(1);
                    v___x_1548_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1548_, 0, v___x_1547_);
                    lean_ctor_set(v___x_1548_, 1, v_k_1258_);
                    lean_ctor_set(v___x_1548_, 2, v_v_1259_);
                    lean_ctor_set(v___x_1548_, 3, v_t_1260_);
                    lean_ctor_set(v___x_1548_, 4, v_t_1260_);
                    return v___x_1548_;
                }
            }
            1 => {
                v___x_1269_ = lean_nat_dec_lt(v_k_1258_, v_k_1262_);
                if v___x_1269_ == 0 {
                    v___x_1270_ = lean_nat_dec_eq(v_k_1258_, v_k_1262_);
                    if v___x_1270_ == 0 {
                        lean_dec(v_size_1261_);
                        v_impl_1271_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1258_, v_v_1259_, v_r_1265_);
                        v___x_1272_ = lean_unsigned_to_nat(1);
                        if lean_obj_tag(v_l_1264_) == 0 {
                            v_size_1273_ = lean_ctor_get(v_l_1264_, 0);
                            v_size_1274_ = lean_ctor_get(v_impl_1271_, 0);
                            lean_inc(v_size_1274_);
                            v_k_1275_ = lean_ctor_get(v_impl_1271_, 1);
                            lean_inc(v_k_1275_);
                            v_v_1276_ = lean_ctor_get(v_impl_1271_, 2);
                            lean_inc(v_v_1276_);
                            v_l_1277_ = lean_ctor_get(v_impl_1271_, 3);
                            lean_inc(v_l_1277_);
                            v_r_1278_ = lean_ctor_get(v_impl_1271_, 4);
                            lean_inc(v_r_1278_);
                            v___x_1279_ = lean_unsigned_to_nat(3);
                            v___x_1280_ = lean_nat_mul(v___x_1279_, v_size_1273_);
                            v___x_1281_ = lean_nat_dec_lt(v___x_1280_, v_size_1274_);
                            lean_dec(v___x_1280_);
                            if v___x_1281_ == 0 {
                                lean_dec(v_r_1278_);
                                lean_dec(v_l_1277_);
                                lean_dec(v_v_1276_);
                                lean_dec(v_k_1275_);
                                v___x_1282_ = lean_nat_add(v___x_1272_, v_size_1273_);
                                v___x_1283_ = lean_nat_add(v___x_1282_, v_size_1274_);
                                lean_dec(v_size_1274_);
                                lean_dec(v___x_1282_);
                                if v_isShared_1268_ == 0 {
                                    lean_ctor_set(v___x_1267_, 4, v_impl_1271_);
                                    lean_ctor_set(v___x_1267_, 0, v___x_1283_);
                                    v___x_1285_ = v___x_1267_;
                                    state = 2;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1286_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1286_, 0, v___x_1283_);
                                    lean_ctor_set(v_reuseFailAlloc_1286_, 1, v_k_1262_);
                                    lean_ctor_set(v_reuseFailAlloc_1286_, 2, v_v_1263_);
                                    lean_ctor_set(v_reuseFailAlloc_1286_, 3, v_l_1264_);
                                    lean_ctor_set(v_reuseFailAlloc_1286_, 4, v_impl_1271_);
                                    v___x_1285_ = v_reuseFailAlloc_1286_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_isSharedCheck_1350_ = (!lean_is_exclusive(v_impl_1271_)) as u8;
                                if v_isSharedCheck_1350_ == 0 {
                                    v_unused_1351_ = lean_ctor_get(v_impl_1271_, 4);
                                    lean_dec(v_unused_1351_);
                                    v_unused_1352_ = lean_ctor_get(v_impl_1271_, 3);
                                    lean_dec(v_unused_1352_);
                                    v_unused_1353_ = lean_ctor_get(v_impl_1271_, 2);
                                    lean_dec(v_unused_1353_);
                                    v_unused_1354_ = lean_ctor_get(v_impl_1271_, 1);
                                    lean_dec(v_unused_1354_);
                                    v_unused_1355_ = lean_ctor_get(v_impl_1271_, 0);
                                    lean_dec(v_unused_1355_);
                                    v___x_1288_ = v_impl_1271_;
                                    v_isShared_1289_ = v_isSharedCheck_1350_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_impl_1271_);
                                    v___x_1288_ = lean_box(0);
                                    v_isShared_1289_ = v_isSharedCheck_1350_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            v_l_1356_ = lean_ctor_get(v_impl_1271_, 3);
                            lean_inc(v_l_1356_);
                            if lean_obj_tag(v_l_1356_) == 0 {
                                v_r_1357_ = lean_ctor_get(v_impl_1271_, 4);
                                v_k_1358_ = lean_ctor_get(v_impl_1271_, 1);
                                v_v_1359_ = lean_ctor_get(v_impl_1271_, 2);
                                v_isSharedCheck_1382_ = (!lean_is_exclusive(v_impl_1271_)) as u8;
                                if v_isSharedCheck_1382_ == 0 {
                                    v_unused_1383_ = lean_ctor_get(v_impl_1271_, 3);
                                    lean_dec(v_unused_1383_);
                                    v_unused_1384_ = lean_ctor_get(v_impl_1271_, 0);
                                    lean_dec(v_unused_1384_);
                                    v___x_1361_ = v_impl_1271_;
                                    v_isShared_1362_ = v_isSharedCheck_1382_;
                                    state = 13;
                                    continue;
                                } else {
                                    lean_inc(v_r_1357_);
                                    lean_inc(v_v_1359_);
                                    lean_inc(v_k_1358_);
                                    lean_dec(v_impl_1271_);
                                    v___x_1361_ = lean_box(0);
                                    v_isShared_1362_ = v_isSharedCheck_1382_;
                                    state = 13;
                                    continue;
                                }
                            } else {
                                v_r_1385_ = lean_ctor_get(v_impl_1271_, 4);
                                lean_inc(v_r_1385_);
                                if lean_obj_tag(v_r_1385_) == 0 {
                                    v_k_1386_ = lean_ctor_get(v_impl_1271_, 1);
                                    v_v_1387_ = lean_ctor_get(v_impl_1271_, 2);
                                    v_isSharedCheck_1398_ =
                                        (!lean_is_exclusive(v_impl_1271_)) as u8;
                                    if v_isSharedCheck_1398_ == 0 {
                                        v_unused_1399_ = lean_ctor_get(v_impl_1271_, 4);
                                        lean_dec(v_unused_1399_);
                                        v_unused_1400_ = lean_ctor_get(v_impl_1271_, 3);
                                        lean_dec(v_unused_1400_);
                                        v_unused_1401_ = lean_ctor_get(v_impl_1271_, 0);
                                        lean_dec(v_unused_1401_);
                                        v___x_1389_ = v_impl_1271_;
                                        v_isShared_1390_ = v_isSharedCheck_1398_;
                                        state = 18;
                                        continue;
                                    } else {
                                        lean_inc(v_v_1387_);
                                        lean_inc(v_k_1386_);
                                        lean_dec(v_impl_1271_);
                                        v___x_1389_ = lean_box(0);
                                        v_isShared_1390_ = v_isSharedCheck_1398_;
                                        state = 18;
                                        continue;
                                    }
                                } else {
                                    v___x_1402_ = lean_unsigned_to_nat(2);
                                    if v_isShared_1268_ == 0 {
                                        lean_ctor_set(v___x_1267_, 4, v_impl_1271_);
                                        lean_ctor_set(v___x_1267_, 3, v_r_1385_);
                                        lean_ctor_set(v___x_1267_, 0, v___x_1402_);
                                        v___x_1404_ = v___x_1267_;
                                        state = 21;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 5, (0) as u32);
                                        lean_ctor_set(v_reuseFailAlloc_1405_, 0, v___x_1402_);
                                        lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_k_1262_);
                                        lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_v_1263_);
                                        lean_ctor_set(v_reuseFailAlloc_1405_, 3, v_r_1385_);
                                        lean_ctor_set(v_reuseFailAlloc_1405_, 4, v_impl_1271_);
                                        v___x_1404_ = v_reuseFailAlloc_1405_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_v_1263_);
                        lean_dec(v_k_1262_);
                        if v_isShared_1268_ == 0 {
                            lean_ctor_set(v___x_1267_, 2, v_v_1259_);
                            lean_ctor_set(v___x_1267_, 1, v_k_1258_);
                            v___x_1407_ = v___x_1267_;
                            state = 22;
                            continue;
                        } else {
                            v_reuseFailAlloc_1408_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1408_, 0, v_size_1261_);
                            lean_ctor_set(v_reuseFailAlloc_1408_, 1, v_k_1258_);
                            lean_ctor_set(v_reuseFailAlloc_1408_, 2, v_v_1259_);
                            lean_ctor_set(v_reuseFailAlloc_1408_, 3, v_l_1264_);
                            lean_ctor_set(v_reuseFailAlloc_1408_, 4, v_r_1265_);
                            v___x_1407_ = v_reuseFailAlloc_1408_;
                            state = 22;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_size_1261_);
                    v_impl_1409_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1258_, v_v_1259_, v_l_1264_);
                    v___x_1410_ = lean_unsigned_to_nat(1);
                    if lean_obj_tag(v_r_1265_) == 0 {
                        v_size_1411_ = lean_ctor_get(v_r_1265_, 0);
                        v_size_1412_ = lean_ctor_get(v_impl_1409_, 0);
                        lean_inc(v_size_1412_);
                        v_k_1413_ = lean_ctor_get(v_impl_1409_, 1);
                        lean_inc(v_k_1413_);
                        v_v_1414_ = lean_ctor_get(v_impl_1409_, 2);
                        lean_inc(v_v_1414_);
                        v_l_1415_ = lean_ctor_get(v_impl_1409_, 3);
                        lean_inc(v_l_1415_);
                        v_r_1416_ = lean_ctor_get(v_impl_1409_, 4);
                        lean_inc(v_r_1416_);
                        v___x_1417_ = lean_unsigned_to_nat(3);
                        v___x_1418_ = lean_nat_mul(v___x_1417_, v_size_1411_);
                        v___x_1419_ = lean_nat_dec_lt(v___x_1418_, v_size_1412_);
                        lean_dec(v___x_1418_);
                        if v___x_1419_ == 0 {
                            lean_dec(v_r_1416_);
                            lean_dec(v_l_1415_);
                            lean_dec(v_v_1414_);
                            lean_dec(v_k_1413_);
                            v___x_1420_ = lean_nat_add(v___x_1410_, v_size_1412_);
                            lean_dec(v_size_1412_);
                            v___x_1421_ = lean_nat_add(v___x_1420_, v_size_1411_);
                            lean_dec(v___x_1420_);
                            if v_isShared_1268_ == 0 {
                                lean_ctor_set(v___x_1267_, 3, v_impl_1409_);
                                lean_ctor_set(v___x_1267_, 0, v___x_1421_);
                                v___x_1423_ = v___x_1267_;
                                state = 23;
                                continue;
                            } else {
                                v_reuseFailAlloc_1424_ = lean_alloc_ctor(0, 5, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1424_, 0, v___x_1421_);
                                lean_ctor_set(v_reuseFailAlloc_1424_, 1, v_k_1262_);
                                lean_ctor_set(v_reuseFailAlloc_1424_, 2, v_v_1263_);
                                lean_ctor_set(v_reuseFailAlloc_1424_, 3, v_impl_1409_);
                                lean_ctor_set(v_reuseFailAlloc_1424_, 4, v_r_1265_);
                                v___x_1423_ = v_reuseFailAlloc_1424_;
                                state = 23;
                                continue;
                            }
                        } else {
                            v_isSharedCheck_1490_ = (!lean_is_exclusive(v_impl_1409_)) as u8;
                            if v_isSharedCheck_1490_ == 0 {
                                v_unused_1491_ = lean_ctor_get(v_impl_1409_, 4);
                                lean_dec(v_unused_1491_);
                                v_unused_1492_ = lean_ctor_get(v_impl_1409_, 3);
                                lean_dec(v_unused_1492_);
                                v_unused_1493_ = lean_ctor_get(v_impl_1409_, 2);
                                lean_dec(v_unused_1493_);
                                v_unused_1494_ = lean_ctor_get(v_impl_1409_, 1);
                                lean_dec(v_unused_1494_);
                                v_unused_1495_ = lean_ctor_get(v_impl_1409_, 0);
                                lean_dec(v_unused_1495_);
                                v___x_1426_ = v_impl_1409_;
                                v_isShared_1427_ = v_isSharedCheck_1490_;
                                state = 24;
                                continue;
                            } else {
                                lean_dec(v_impl_1409_);
                                v___x_1426_ = lean_box(0);
                                v_isShared_1427_ = v_isSharedCheck_1490_;
                                state = 24;
                                continue;
                            }
                        }
                    } else {
                        v_l_1496_ = lean_ctor_get(v_impl_1409_, 3);
                        lean_inc(v_l_1496_);
                        if lean_obj_tag(v_l_1496_) == 0 {
                            v_r_1497_ = lean_ctor_get(v_impl_1409_, 4);
                            v_k_1498_ = lean_ctor_get(v_impl_1409_, 1);
                            v_v_1499_ = lean_ctor_get(v_impl_1409_, 2);
                            v_isSharedCheck_1510_ = (!lean_is_exclusive(v_impl_1409_)) as u8;
                            if v_isSharedCheck_1510_ == 0 {
                                v_unused_1511_ = lean_ctor_get(v_impl_1409_, 3);
                                lean_dec(v_unused_1511_);
                                v_unused_1512_ = lean_ctor_get(v_impl_1409_, 0);
                                lean_dec(v_unused_1512_);
                                v___x_1501_ = v_impl_1409_;
                                v_isShared_1502_ = v_isSharedCheck_1510_;
                                state = 34;
                                continue;
                            } else {
                                lean_inc(v_r_1497_);
                                lean_inc(v_v_1499_);
                                lean_inc(v_k_1498_);
                                lean_dec(v_impl_1409_);
                                v___x_1501_ = lean_box(0);
                                v_isShared_1502_ = v_isSharedCheck_1510_;
                                state = 34;
                                continue;
                            }
                        } else {
                            v_r_1513_ = lean_ctor_get(v_impl_1409_, 4);
                            lean_inc(v_r_1513_);
                            if lean_obj_tag(v_r_1513_) == 0 {
                                v_k_1514_ = lean_ctor_get(v_impl_1409_, 1);
                                v_v_1515_ = lean_ctor_get(v_impl_1409_, 2);
                                v_isSharedCheck_1538_ = (!lean_is_exclusive(v_impl_1409_)) as u8;
                                if v_isSharedCheck_1538_ == 0 {
                                    v_unused_1539_ = lean_ctor_get(v_impl_1409_, 4);
                                    lean_dec(v_unused_1539_);
                                    v_unused_1540_ = lean_ctor_get(v_impl_1409_, 3);
                                    lean_dec(v_unused_1540_);
                                    v_unused_1541_ = lean_ctor_get(v_impl_1409_, 0);
                                    lean_dec(v_unused_1541_);
                                    v___x_1517_ = v_impl_1409_;
                                    v_isShared_1518_ = v_isSharedCheck_1538_;
                                    state = 37;
                                    continue;
                                } else {
                                    lean_inc(v_v_1515_);
                                    lean_inc(v_k_1514_);
                                    lean_dec(v_impl_1409_);
                                    v___x_1517_ = lean_box(0);
                                    v_isShared_1518_ = v_isSharedCheck_1538_;
                                    state = 37;
                                    continue;
                                }
                            } else {
                                v___x_1542_ = lean_unsigned_to_nat(2);
                                if v_isShared_1268_ == 0 {
                                    lean_ctor_set(v___x_1267_, 4, v_r_1513_);
                                    lean_ctor_set(v___x_1267_, 3, v_impl_1409_);
                                    lean_ctor_set(v___x_1267_, 0, v___x_1542_);
                                    v___x_1544_ = v___x_1267_;
                                    state = 42;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1545_ = lean_alloc_ctor(0, 5, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 0, v___x_1542_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 1, v_k_1262_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 2, v_v_1263_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 3, v_impl_1409_);
                                    lean_ctor_set(v_reuseFailAlloc_1545_, 4, v_r_1513_);
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
                v_size_1290_ = lean_ctor_get(v_l_1277_, 0);
                v_k_1291_ = lean_ctor_get(v_l_1277_, 1);
                v_v_1292_ = lean_ctor_get(v_l_1277_, 2);
                v_l_1293_ = lean_ctor_get(v_l_1277_, 3);
                v_r_1294_ = lean_ctor_get(v_l_1277_, 4);
                v_size_1295_ = lean_ctor_get(v_r_1278_, 0);
                v___x_1296_ = lean_unsigned_to_nat(2);
                v___x_1297_ = lean_nat_mul(v___x_1296_, v_size_1295_);
                v___x_1298_ = lean_nat_dec_lt(v_size_1290_, v___x_1297_);
                lean_dec(v___x_1297_);
                if v___x_1298_ == 0 {
                    lean_inc(v_r_1294_);
                    lean_inc(v_l_1293_);
                    lean_inc(v_v_1292_);
                    lean_inc(v_k_1291_);
                    v_isSharedCheck_1326_ = (!lean_is_exclusive(v_l_1277_)) as u8;
                    if v_isSharedCheck_1326_ == 0 {
                        v_unused_1327_ = lean_ctor_get(v_l_1277_, 4);
                        lean_dec(v_unused_1327_);
                        v_unused_1328_ = lean_ctor_get(v_l_1277_, 3);
                        lean_dec(v_unused_1328_);
                        v_unused_1329_ = lean_ctor_get(v_l_1277_, 2);
                        lean_dec(v_unused_1329_);
                        v_unused_1330_ = lean_ctor_get(v_l_1277_, 1);
                        lean_dec(v_unused_1330_);
                        v_unused_1331_ = lean_ctor_get(v_l_1277_, 0);
                        lean_dec(v_unused_1331_);
                        v___x_1300_ = v_l_1277_;
                        v_isShared_1301_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    } else {
                        lean_dec(v_l_1277_);
                        v___x_1300_ = lean_box(0);
                        v_isShared_1301_ = v_isSharedCheck_1326_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1267_);
                    v___x_1332_ = lean_nat_add(v___x_1272_, v_size_1273_);
                    v___x_1333_ = lean_nat_add(v___x_1332_, v_size_1274_);
                    lean_dec(v_size_1274_);
                    v___x_1334_ = lean_nat_add(v___x_1332_, v_size_1290_);
                    lean_dec(v___x_1332_);
                    lean_inc_ref(v_l_1264_);
                    if v_isShared_1289_ == 0 {
                        lean_ctor_set(v___x_1288_, 4, v_l_1277_);
                        lean_ctor_set(v___x_1288_, 3, v_l_1264_);
                        lean_ctor_set(v___x_1288_, 2, v_v_1263_);
                        lean_ctor_set(v___x_1288_, 1, v_k_1262_);
                        lean_ctor_set(v___x_1288_, 0, v___x_1334_);
                        v___x_1336_ = v___x_1288_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_1349_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 0, v___x_1334_);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 1, v_k_1262_);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 2, v_v_1263_);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 3, v_l_1264_);
                        lean_ctor_set(v_reuseFailAlloc_1349_, 4, v_l_1277_);
                        v___x_1336_ = v_reuseFailAlloc_1349_;
                        state = 10;
                        continue;
                    }
                }
            }
            4 => {
                v___x_1302_ = lean_nat_add(v___x_1272_, v_size_1273_);
                v___x_1303_ = lean_nat_add(v___x_1302_, v_size_1274_);
                lean_dec(v_size_1274_);
                if lean_obj_tag(v_l_1293_) == 0 {
                    v_size_1324_ = lean_ctor_get(v_l_1293_, 0);
                    lean_inc(v_size_1324_);
                    v___y_1316_ = v_size_1324_;
                    state = 8;
                    continue;
                } else {
                    v___x_1325_ = lean_unsigned_to_nat(0);
                    v___y_1316_ = v___x_1325_;
                    state = 8;
                    continue;
                }
            }
            5 => {
                v___x_1308_ = lean_nat_add(v___y_1306_, v___y_1307_);
                lean_dec(v___y_1307_);
                lean_dec(v___y_1306_);
                if v_isShared_1301_ == 0 {
                    lean_ctor_set(v___x_1300_, 4, v_r_1278_);
                    lean_ctor_set(v___x_1300_, 3, v_r_1294_);
                    lean_ctor_set(v___x_1300_, 2, v_v_1276_);
                    lean_ctor_set(v___x_1300_, 1, v_k_1275_);
                    lean_ctor_set(v___x_1300_, 0, v___x_1308_);
                    v___x_1310_ = v___x_1300_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1314_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 0, v___x_1308_);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 1, v_k_1275_);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 2, v_v_1276_);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 3, v_r_1294_);
                    lean_ctor_set(v_reuseFailAlloc_1314_, 4, v_r_1278_);
                    v___x_1310_ = v_reuseFailAlloc_1314_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_1289_ == 0 {
                    lean_ctor_set(v___x_1288_, 4, v___x_1310_);
                    lean_ctor_set(v___x_1288_, 3, v___y_1305_);
                    lean_ctor_set(v___x_1288_, 2, v_v_1292_);
                    lean_ctor_set(v___x_1288_, 1, v_k_1291_);
                    lean_ctor_set(v___x_1288_, 0, v___x_1303_);
                    v___x_1312_ = v___x_1288_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 0, v___x_1303_);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 1, v_k_1291_);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 2, v_v_1292_);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 3, v___y_1305_);
                    lean_ctor_set(v_reuseFailAlloc_1313_, 4, v___x_1310_);
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
                lean_dec(v___y_1316_);
                lean_dec(v___x_1302_);
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v_l_1293_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1317_);
                    v___x_1319_ = v___x_1267_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1317_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 3, v_l_1264_);
                    lean_ctor_set(v_reuseFailAlloc_1323_, 4, v_l_1293_);
                    v___x_1319_ = v_reuseFailAlloc_1323_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_1320_ = lean_nat_add(v___x_1272_, v_size_1295_);
                if lean_obj_tag(v_r_1294_) == 0 {
                    v_size_1321_ = lean_ctor_get(v_r_1294_, 0);
                    lean_inc(v_size_1321_);
                    v___y_1305_ = v___x_1319_;
                    v___y_1306_ = v___x_1320_;
                    v___y_1307_ = v_size_1321_;
                    state = 5;
                    continue;
                } else {
                    v___x_1322_ = lean_unsigned_to_nat(0);
                    v___y_1305_ = v___x_1319_;
                    v___y_1306_ = v___x_1320_;
                    v___y_1307_ = v___x_1322_;
                    state = 5;
                    continue;
                }
            }
            10 => {
                v_isSharedCheck_1343_ = (!lean_is_exclusive(v_l_1264_)) as u8;
                if v_isSharedCheck_1343_ == 0 {
                    v_unused_1344_ = lean_ctor_get(v_l_1264_, 4);
                    lean_dec(v_unused_1344_);
                    v_unused_1345_ = lean_ctor_get(v_l_1264_, 3);
                    lean_dec(v_unused_1345_);
                    v_unused_1346_ = lean_ctor_get(v_l_1264_, 2);
                    lean_dec(v_unused_1346_);
                    v_unused_1347_ = lean_ctor_get(v_l_1264_, 1);
                    lean_dec(v_unused_1347_);
                    v_unused_1348_ = lean_ctor_get(v_l_1264_, 0);
                    lean_dec(v_unused_1348_);
                    v___x_1338_ = v_l_1264_;
                    v_isShared_1339_ = v_isSharedCheck_1343_;
                    state = 11;
                    continue;
                } else {
                    lean_dec(v_l_1264_);
                    v___x_1338_ = lean_box(0);
                    v_isShared_1339_ = v_isSharedCheck_1343_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_1339_ == 0 {
                    lean_ctor_set(v___x_1338_, 4, v_r_1278_);
                    lean_ctor_set(v___x_1338_, 3, v___x_1336_);
                    lean_ctor_set(v___x_1338_, 2, v_v_1276_);
                    lean_ctor_set(v___x_1338_, 1, v_k_1275_);
                    lean_ctor_set(v___x_1338_, 0, v___x_1333_);
                    v___x_1341_ = v___x_1338_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_1342_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 0, v___x_1333_);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 1, v_k_1275_);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 2, v_v_1276_);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 3, v___x_1336_);
                    lean_ctor_set(v_reuseFailAlloc_1342_, 4, v_r_1278_);
                    v___x_1341_ = v_reuseFailAlloc_1342_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_1341_;
            }
            13 => {
                v_k_1363_ = lean_ctor_get(v_l_1356_, 1);
                v_v_1364_ = lean_ctor_get(v_l_1356_, 2);
                v_isSharedCheck_1378_ = (!lean_is_exclusive(v_l_1356_)) as u8;
                if v_isSharedCheck_1378_ == 0 {
                    v_unused_1379_ = lean_ctor_get(v_l_1356_, 4);
                    lean_dec(v_unused_1379_);
                    v_unused_1380_ = lean_ctor_get(v_l_1356_, 3);
                    lean_dec(v_unused_1380_);
                    v_unused_1381_ = lean_ctor_get(v_l_1356_, 0);
                    lean_dec(v_unused_1381_);
                    v___x_1366_ = v_l_1356_;
                    v_isShared_1367_ = v_isSharedCheck_1378_;
                    state = 14;
                    continue;
                } else {
                    lean_inc(v_v_1364_);
                    lean_inc(v_k_1363_);
                    lean_dec(v_l_1356_);
                    v___x_1366_ = lean_box(0);
                    v_isShared_1367_ = v_isSharedCheck_1378_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1368_ = lean_unsigned_to_nat(3);
                lean_inc_n(v_r_1357_, 2);
                if v_isShared_1367_ == 0 {
                    lean_ctor_set(v___x_1366_, 4, v_r_1357_);
                    lean_ctor_set(v___x_1366_, 3, v_r_1357_);
                    lean_ctor_set(v___x_1366_, 2, v_v_1263_);
                    lean_ctor_set(v___x_1366_, 1, v_k_1262_);
                    lean_ctor_set(v___x_1366_, 0, v___x_1272_);
                    v___x_1370_ = v___x_1366_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1377_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 0, v___x_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 3, v_r_1357_);
                    lean_ctor_set(v_reuseFailAlloc_1377_, 4, v_r_1357_);
                    v___x_1370_ = v_reuseFailAlloc_1377_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                lean_inc(v_r_1357_);
                if v_isShared_1362_ == 0 {
                    lean_ctor_set(v___x_1361_, 3, v_r_1357_);
                    lean_ctor_set(v___x_1361_, 0, v___x_1272_);
                    v___x_1372_ = v___x_1361_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_1376_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 0, v___x_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 1, v_k_1358_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 2, v_v_1359_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 3, v_r_1357_);
                    lean_ctor_set(v_reuseFailAlloc_1376_, 4, v_r_1357_);
                    v___x_1372_ = v_reuseFailAlloc_1376_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v___x_1372_);
                    lean_ctor_set(v___x_1267_, 3, v___x_1370_);
                    lean_ctor_set(v___x_1267_, 2, v_v_1364_);
                    lean_ctor_set(v___x_1267_, 1, v_k_1363_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1368_);
                    v___x_1374_ = v___x_1267_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1375_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 0, v___x_1368_);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 1, v_k_1363_);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 2, v_v_1364_);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 3, v___x_1370_);
                    lean_ctor_set(v_reuseFailAlloc_1375_, 4, v___x_1372_);
                    v___x_1374_ = v_reuseFailAlloc_1375_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1374_;
            }
            18 => {
                v___x_1391_ = lean_unsigned_to_nat(3);
                if v_isShared_1390_ == 0 {
                    lean_ctor_set(v___x_1389_, 4, v_l_1356_);
                    lean_ctor_set(v___x_1389_, 2, v_v_1263_);
                    lean_ctor_set(v___x_1389_, 1, v_k_1262_);
                    lean_ctor_set(v___x_1389_, 0, v___x_1272_);
                    v___x_1393_ = v___x_1389_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1397_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 0, v___x_1272_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 3, v_l_1356_);
                    lean_ctor_set(v_reuseFailAlloc_1397_, 4, v_l_1356_);
                    v___x_1393_ = v_reuseFailAlloc_1397_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v_r_1385_);
                    lean_ctor_set(v___x_1267_, 3, v___x_1393_);
                    lean_ctor_set(v___x_1267_, 2, v_v_1387_);
                    lean_ctor_set(v___x_1267_, 1, v_k_1386_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1391_);
                    v___x_1395_ = v___x_1267_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1396_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 0, v___x_1391_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_k_1386_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 2, v_v_1387_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 3, v___x_1393_);
                    lean_ctor_set(v_reuseFailAlloc_1396_, 4, v_r_1385_);
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
                v_size_1428_ = lean_ctor_get(v_l_1415_, 0);
                v_size_1429_ = lean_ctor_get(v_r_1416_, 0);
                v_k_1430_ = lean_ctor_get(v_r_1416_, 1);
                v_v_1431_ = lean_ctor_get(v_r_1416_, 2);
                v_l_1432_ = lean_ctor_get(v_r_1416_, 3);
                v_r_1433_ = lean_ctor_get(v_r_1416_, 4);
                v___x_1434_ = lean_unsigned_to_nat(2);
                v___x_1435_ = lean_nat_mul(v___x_1434_, v_size_1428_);
                v___x_1436_ = lean_nat_dec_lt(v_size_1429_, v___x_1435_);
                lean_dec(v___x_1435_);
                if v___x_1436_ == 0 {
                    lean_inc(v_r_1433_);
                    lean_inc(v_l_1432_);
                    lean_inc(v_v_1431_);
                    lean_inc(v_k_1430_);
                    v_isSharedCheck_1465_ = (!lean_is_exclusive(v_r_1416_)) as u8;
                    if v_isSharedCheck_1465_ == 0 {
                        v_unused_1466_ = lean_ctor_get(v_r_1416_, 4);
                        lean_dec(v_unused_1466_);
                        v_unused_1467_ = lean_ctor_get(v_r_1416_, 3);
                        lean_dec(v_unused_1467_);
                        v_unused_1468_ = lean_ctor_get(v_r_1416_, 2);
                        lean_dec(v_unused_1468_);
                        v_unused_1469_ = lean_ctor_get(v_r_1416_, 1);
                        lean_dec(v_unused_1469_);
                        v_unused_1470_ = lean_ctor_get(v_r_1416_, 0);
                        lean_dec(v_unused_1470_);
                        v___x_1438_ = v_r_1416_;
                        v_isShared_1439_ = v_isSharedCheck_1465_;
                        state = 25;
                        continue;
                    } else {
                        lean_dec(v_r_1416_);
                        v___x_1438_ = lean_box(0);
                        v_isShared_1439_ = v_isSharedCheck_1465_;
                        state = 25;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1267_);
                    v___x_1471_ = lean_nat_add(v___x_1410_, v_size_1412_);
                    lean_dec(v_size_1412_);
                    v___x_1472_ = lean_nat_add(v___x_1471_, v_size_1411_);
                    lean_dec(v___x_1471_);
                    v___x_1473_ = lean_nat_add(v___x_1410_, v_size_1411_);
                    v___x_1474_ = lean_nat_add(v___x_1473_, v_size_1429_);
                    lean_dec(v___x_1473_);
                    lean_inc_ref(v_r_1265_);
                    if v_isShared_1427_ == 0 {
                        lean_ctor_set(v___x_1426_, 4, v_r_1265_);
                        lean_ctor_set(v___x_1426_, 3, v_r_1416_);
                        lean_ctor_set(v___x_1426_, 2, v_v_1263_);
                        lean_ctor_set(v___x_1426_, 1, v_k_1262_);
                        lean_ctor_set(v___x_1426_, 0, v___x_1474_);
                        v___x_1476_ = v___x_1426_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_1489_ = lean_alloc_ctor(0, 5, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1489_, 0, v___x_1474_);
                        lean_ctor_set(v_reuseFailAlloc_1489_, 1, v_k_1262_);
                        lean_ctor_set(v_reuseFailAlloc_1489_, 2, v_v_1263_);
                        lean_ctor_set(v_reuseFailAlloc_1489_, 3, v_r_1416_);
                        lean_ctor_set(v_reuseFailAlloc_1489_, 4, v_r_1265_);
                        v___x_1476_ = v_reuseFailAlloc_1489_;
                        state = 31;
                        continue;
                    }
                }
            }
            25 => {
                v___x_1440_ = lean_nat_add(v___x_1410_, v_size_1412_);
                lean_dec(v_size_1412_);
                v___x_1441_ = lean_nat_add(v___x_1440_, v_size_1411_);
                lean_dec(v___x_1440_);
                v___x_1453_ = lean_nat_add(v___x_1410_, v_size_1428_);
                if lean_obj_tag(v_l_1432_) == 0 {
                    v_size_1463_ = lean_ctor_get(v_l_1432_, 0);
                    lean_inc(v_size_1463_);
                    v___y_1455_ = v_size_1463_;
                    state = 29;
                    continue;
                } else {
                    v___x_1464_ = lean_unsigned_to_nat(0);
                    v___y_1455_ = v___x_1464_;
                    state = 29;
                    continue;
                }
            }
            26 => {
                v___x_1446_ = lean_nat_add(v___y_1444_, v___y_1445_);
                lean_dec(v___y_1445_);
                lean_dec(v___y_1444_);
                if v_isShared_1439_ == 0 {
                    lean_ctor_set(v___x_1438_, 4, v_r_1265_);
                    lean_ctor_set(v___x_1438_, 3, v_r_1433_);
                    lean_ctor_set(v___x_1438_, 2, v_v_1263_);
                    lean_ctor_set(v___x_1438_, 1, v_k_1262_);
                    lean_ctor_set(v___x_1438_, 0, v___x_1446_);
                    v___x_1448_ = v___x_1438_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_1452_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 0, v___x_1446_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 3, v_r_1433_);
                    lean_ctor_set(v_reuseFailAlloc_1452_, 4, v_r_1265_);
                    v___x_1448_ = v_reuseFailAlloc_1452_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v_isShared_1427_ == 0 {
                    lean_ctor_set(v___x_1426_, 4, v___x_1448_);
                    lean_ctor_set(v___x_1426_, 3, v___y_1443_);
                    lean_ctor_set(v___x_1426_, 2, v_v_1431_);
                    lean_ctor_set(v___x_1426_, 1, v_k_1430_);
                    lean_ctor_set(v___x_1426_, 0, v___x_1441_);
                    v___x_1450_ = v___x_1426_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_1451_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 0, v___x_1441_);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 1, v_k_1430_);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 2, v_v_1431_);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 3, v___y_1443_);
                    lean_ctor_set(v_reuseFailAlloc_1451_, 4, v___x_1448_);
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
                lean_dec(v___y_1455_);
                lean_dec(v___x_1453_);
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v_l_1432_);
                    lean_ctor_set(v___x_1267_, 3, v_l_1415_);
                    lean_ctor_set(v___x_1267_, 2, v_v_1414_);
                    lean_ctor_set(v___x_1267_, 1, v_k_1413_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1456_);
                    v___x_1458_ = v___x_1267_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_1462_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 0, v___x_1456_);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 1, v_k_1413_);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 2, v_v_1414_);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 3, v_l_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1462_, 4, v_l_1432_);
                    v___x_1458_ = v_reuseFailAlloc_1462_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                v___x_1459_ = lean_nat_add(v___x_1410_, v_size_1411_);
                if lean_obj_tag(v_r_1433_) == 0 {
                    v_size_1460_ = lean_ctor_get(v_r_1433_, 0);
                    lean_inc(v_size_1460_);
                    v___y_1443_ = v___x_1458_;
                    v___y_1444_ = v___x_1459_;
                    v___y_1445_ = v_size_1460_;
                    state = 26;
                    continue;
                } else {
                    v___x_1461_ = lean_unsigned_to_nat(0);
                    v___y_1443_ = v___x_1458_;
                    v___y_1444_ = v___x_1459_;
                    v___y_1445_ = v___x_1461_;
                    state = 26;
                    continue;
                }
            }
            31 => {
                v_isSharedCheck_1483_ = (!lean_is_exclusive(v_r_1265_)) as u8;
                if v_isSharedCheck_1483_ == 0 {
                    v_unused_1484_ = lean_ctor_get(v_r_1265_, 4);
                    lean_dec(v_unused_1484_);
                    v_unused_1485_ = lean_ctor_get(v_r_1265_, 3);
                    lean_dec(v_unused_1485_);
                    v_unused_1486_ = lean_ctor_get(v_r_1265_, 2);
                    lean_dec(v_unused_1486_);
                    v_unused_1487_ = lean_ctor_get(v_r_1265_, 1);
                    lean_dec(v_unused_1487_);
                    v_unused_1488_ = lean_ctor_get(v_r_1265_, 0);
                    lean_dec(v_unused_1488_);
                    v___x_1478_ = v_r_1265_;
                    v_isShared_1479_ = v_isSharedCheck_1483_;
                    state = 32;
                    continue;
                } else {
                    lean_dec(v_r_1265_);
                    v___x_1478_ = lean_box(0);
                    v_isShared_1479_ = v_isSharedCheck_1483_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                if v_isShared_1479_ == 0 {
                    lean_ctor_set(v___x_1478_, 4, v___x_1476_);
                    lean_ctor_set(v___x_1478_, 3, v_l_1415_);
                    lean_ctor_set(v___x_1478_, 2, v_v_1414_);
                    lean_ctor_set(v___x_1478_, 1, v_k_1413_);
                    lean_ctor_set(v___x_1478_, 0, v___x_1472_);
                    v___x_1481_ = v___x_1478_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1482_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 0, v___x_1472_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 1, v_k_1413_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 2, v_v_1414_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 3, v_l_1415_);
                    lean_ctor_set(v_reuseFailAlloc_1482_, 4, v___x_1476_);
                    v___x_1481_ = v_reuseFailAlloc_1482_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1481_;
            }
            34 => {
                v___x_1503_ = lean_unsigned_to_nat(3);
                lean_inc(v_r_1497_);
                if v_isShared_1502_ == 0 {
                    lean_ctor_set(v___x_1501_, 3, v_r_1497_);
                    lean_ctor_set(v___x_1501_, 2, v_v_1263_);
                    lean_ctor_set(v___x_1501_, 1, v_k_1262_);
                    lean_ctor_set(v___x_1501_, 0, v___x_1410_);
                    v___x_1505_ = v___x_1501_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1509_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 0, v___x_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 3, v_r_1497_);
                    lean_ctor_set(v_reuseFailAlloc_1509_, 4, v_r_1497_);
                    v___x_1505_ = v_reuseFailAlloc_1509_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v___x_1505_);
                    lean_ctor_set(v___x_1267_, 3, v_l_1496_);
                    lean_ctor_set(v___x_1267_, 2, v_v_1499_);
                    lean_ctor_set(v___x_1267_, 1, v_k_1498_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1503_);
                    v___x_1507_ = v___x_1267_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_1508_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 0, v___x_1503_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 1, v_k_1498_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 2, v_v_1499_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 3, v_l_1496_);
                    lean_ctor_set(v_reuseFailAlloc_1508_, 4, v___x_1505_);
                    v___x_1507_ = v_reuseFailAlloc_1508_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_1507_;
            }
            37 => {
                v_k_1519_ = lean_ctor_get(v_r_1513_, 1);
                v_v_1520_ = lean_ctor_get(v_r_1513_, 2);
                v_isSharedCheck_1534_ = (!lean_is_exclusive(v_r_1513_)) as u8;
                if v_isSharedCheck_1534_ == 0 {
                    v_unused_1535_ = lean_ctor_get(v_r_1513_, 4);
                    lean_dec(v_unused_1535_);
                    v_unused_1536_ = lean_ctor_get(v_r_1513_, 3);
                    lean_dec(v_unused_1536_);
                    v_unused_1537_ = lean_ctor_get(v_r_1513_, 0);
                    lean_dec(v_unused_1537_);
                    v___x_1522_ = v_r_1513_;
                    v_isShared_1523_ = v_isSharedCheck_1534_;
                    state = 38;
                    continue;
                } else {
                    lean_inc(v_v_1520_);
                    lean_inc(v_k_1519_);
                    lean_dec(v_r_1513_);
                    v___x_1522_ = lean_box(0);
                    v_isShared_1523_ = v_isSharedCheck_1534_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                v___x_1524_ = lean_unsigned_to_nat(3);
                if v_isShared_1523_ == 0 {
                    lean_ctor_set(v___x_1522_, 4, v_l_1496_);
                    lean_ctor_set(v___x_1522_, 3, v_l_1496_);
                    lean_ctor_set(v___x_1522_, 2, v_v_1515_);
                    lean_ctor_set(v___x_1522_, 1, v_k_1514_);
                    lean_ctor_set(v___x_1522_, 0, v___x_1410_);
                    v___x_1526_ = v___x_1522_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_1533_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1533_, 0, v___x_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1533_, 1, v_k_1514_);
                    lean_ctor_set(v_reuseFailAlloc_1533_, 2, v_v_1515_);
                    lean_ctor_set(v_reuseFailAlloc_1533_, 3, v_l_1496_);
                    lean_ctor_set(v_reuseFailAlloc_1533_, 4, v_l_1496_);
                    v___x_1526_ = v_reuseFailAlloc_1533_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_1518_ == 0 {
                    lean_ctor_set(v___x_1517_, 4, v_l_1496_);
                    lean_ctor_set(v___x_1517_, 2, v_v_1263_);
                    lean_ctor_set(v___x_1517_, 1, v_k_1262_);
                    lean_ctor_set(v___x_1517_, 0, v___x_1410_);
                    v___x_1528_ = v___x_1517_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_1532_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 0, v___x_1410_);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 1, v_k_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 2, v_v_1263_);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 3, v_l_1496_);
                    lean_ctor_set(v_reuseFailAlloc_1532_, 4, v_l_1496_);
                    v___x_1528_ = v_reuseFailAlloc_1532_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_1268_ == 0 {
                    lean_ctor_set(v___x_1267_, 4, v___x_1528_);
                    lean_ctor_set(v___x_1267_, 3, v___x_1526_);
                    lean_ctor_set(v___x_1267_, 2, v_v_1520_);
                    lean_ctor_set(v___x_1267_, 1, v_k_1519_);
                    lean_ctor_set(v___x_1267_, 0, v___x_1524_);
                    v___x_1530_ = v___x_1267_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_1531_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 0, v___x_1524_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 1, v_k_1519_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 2, v_v_1520_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 3, v___x_1526_);
                    lean_ctor_set(v_reuseFailAlloc_1531_, 4, v___x_1528_);
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
    mut v_t_1549_: *mut LeanObject,
    mut v_k_1550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: u8 = 0;
    let mut v___x_1556_: u8 = 0;
    let mut v___x_1558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_1549_) == 0 {
                    v_k_1551_ = lean_ctor_get(v_t_1549_, 1);
                    v_v_1552_ = lean_ctor_get(v_t_1549_, 2);
                    v_l_1553_ = lean_ctor_get(v_t_1549_, 3);
                    v_r_1554_ = lean_ctor_get(v_t_1549_, 4);
                    v___x_1555_ = lean_nat_dec_lt(v_k_1550_, v_k_1551_);
                    if v___x_1555_ == 0 {
                        v___x_1556_ = lean_nat_dec_eq(v_k_1550_, v_k_1551_);
                        if v___x_1556_ == 0 {
                            v_t_1549_ = v_r_1554_;
                            state = 0;
                            continue;
                        } else {
                            lean_inc(v_v_1552_);
                            v___x_1558_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_1558_, 0, v_v_1552_);
                            return v___x_1558_;
                        }
                    } else {
                        v_t_1549_ = v_l_1553_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_1560_ = lean_box(0);
                    return v___x_1560_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg___boxed(
    mut v_t_1561_: *mut LeanObject,
    mut v_k_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1563_: *mut LeanObject = core::ptr::null_mut();
    v_res_1563_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_1561_, v_k_1562_);
    lean_dec(v_k_1562_);
    lean_dec(v_t_1561_);
    return v_res_1563_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt(
    mut v_optionsPerPos_1564_: *mut LeanObject,
    mut v_pos_1565_: *mut LeanObject,
    mut v_name_1566_: *mut LeanObject,
    mut v_value_1567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1572_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_optionsPerPos_1564_, v_pos_1565_);
                if lean_obj_tag(v___x_1572_) == 0 {
                    v___x_1573_ = l_Lean_Options_empty;
                    v___y_1569_ = v___x_1573_;
                    state = 1;
                    continue;
                } else {
                    v_val_1574_ = lean_ctor_get(v___x_1572_, 0);
                    lean_inc(v_val_1574_);
                    lean_dec_ref_known(v___x_1572_, 1);
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
    mut v_00_u03b2_1575_: *mut LeanObject,
    mut v_k_1576_: *mut LeanObject,
    mut v_v_1577_: *mut LeanObject,
    mut v_t_1578_: *mut LeanObject,
    mut v_hl_1579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    v___x_1580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__1___redArg(v_k_1576_, v_v_1577_, v_t_1578_);
    return v___x_1580_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(
    mut v_00_u03b4_1581_: *mut LeanObject,
    mut v_t_1582_: *mut LeanObject,
    mut v_k_1583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    v___x_1584_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___redArg(v_t_1582_, v_k_1583_);
    return v___x_1584_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2___boxed(
    mut v_00_u03b4_1585_: *mut LeanObject,
    mut v_t_1586_: *mut LeanObject,
    mut v_k_1587_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1588_: *mut LeanObject = core::ptr::null_mut();
    v_res_1588_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_insertAt_spec__2(v_00_u03b4_1585_, v_t_1586_, v_k_1587_);
    lean_dec(v_k_1587_);
    lean_dec(v_t_1586_);
    return v_res_1588_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(
    mut v_b_u2082_1589_: *mut LeanObject,
    mut v___f_1590_: *mut LeanObject,
    mut v_x_1591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1596_: u8 = 0;
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1591_) == 0 {
                    lean_dec_ref(v___f_1590_);
                    v___x_1592_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1592_, 0, v_b_u2082_1589_);
                    return v___x_1592_;
                } else {
                    v_val_1593_ = lean_ctor_get(v_x_1591_, 0);
                    v_isSharedCheck_1601_ = (!lean_is_exclusive(v_x_1591_)) as u8;
                    if v_isSharedCheck_1601_ == 0 {
                        v___x_1595_ = v_x_1591_;
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_1593_);
                        lean_dec(v_x_1591_);
                        v___x_1595_ = lean_box(0);
                        v_isShared_1596_ = v_isSharedCheck_1601_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1597_ = l_Lean_Options_mergeBy(v___f_1590_, v_val_1593_, v_b_u2082_1589_);
                if v_isShared_1596_ == 0 {
                    lean_ctor_set(v___x_1595_, 0, v___x_1597_);
                    v___x_1599_ = v___x_1595_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1600_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1600_, 0, v___x_1597_);
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
    mut v_x_1602_: *mut LeanObject,
    mut v_x_1603_: *mut LeanObject,
    mut v_dv_1604_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v_dv_1604_);
    return v_dv_1604_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0___boxed(
    mut v_x_1605_: *mut LeanObject,
    mut v_x_1606_: *mut LeanObject,
    mut v_dv_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1608_: *mut LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__0(v_x_1605_, v_x_1606_, v_dv_1607_);
    lean_dec_ref(v_dv_1607_);
    lean_dec_ref(v_x_1606_);
    lean_dec(v_x_1605_);
    return v_res_1608_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(
    mut v_b_u2082_1610_: *mut LeanObject,
    mut v_k_1611_: *mut LeanObject,
    mut v_t_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1621_: u8 = 0;
    let mut v___x_1622_: u8 = 0;
    let mut v___x_1623_: u8 = 0;
    let mut v_impl_1624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_impl_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1634_: u8 = 0;
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1613_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___closed__0;
                if lean_obj_tag(v_t_1612_) == 0 {
                    v_size_1614_ = lean_ctor_get(v_t_1612_, 0);
                    v_k_1615_ = lean_ctor_get(v_t_1612_, 1);
                    v_v_1616_ = lean_ctor_get(v_t_1612_, 2);
                    v_l_1617_ = lean_ctor_get(v_t_1612_, 3);
                    v_r_1618_ = lean_ctor_get(v_t_1612_, 4);
                    v_isSharedCheck_1634_ = (!lean_is_exclusive(v_t_1612_)) as u8;
                    if v_isSharedCheck_1634_ == 0 {
                        v___x_1620_ = v_t_1612_;
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_r_1618_);
                        lean_inc(v_l_1617_);
                        lean_inc(v_v_1616_);
                        lean_inc(v_k_1615_);
                        lean_inc(v_size_1614_);
                        lean_dec(v_t_1612_);
                        v___x_1620_ = lean_box(0);
                        v_isShared_1621_ = v_isSharedCheck_1634_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1635_ = lean_box(0);
                    v___x_1636_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_1610_, v___f_1613_, v___x_1635_);
                    v_val_1637_ = lean_ctor_get(v___x_1636_, 0);
                    lean_inc(v_val_1637_);
                    lean_dec(v___x_1636_);
                    v___x_1638_ = lean_unsigned_to_nat(1);
                    v___x_1639_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v___x_1639_, 0, v___x_1638_);
                    lean_ctor_set(v___x_1639_, 1, v_k_1611_);
                    lean_ctor_set(v___x_1639_, 2, v_val_1637_);
                    lean_ctor_set(v___x_1639_, 3, v_t_1612_);
                    lean_ctor_set(v___x_1639_, 4, v_t_1612_);
                    return v___x_1639_;
                }
            }
            1 => {
                v___x_1622_ = lean_nat_dec_lt(v_k_1611_, v_k_1615_);
                if v___x_1622_ == 0 {
                    v___x_1623_ = lean_nat_dec_eq(v_k_1611_, v_k_1615_);
                    if v___x_1623_ == 0 {
                        lean_del_object(v___x_1620_);
                        lean_dec(v_size_1614_);
                        v_impl_1624_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_1610_, v_k_1611_, v_r_1618_);
                        v___x_1625_ = l_Std_DTreeMap_Internal_Impl_balance___redArg(
                            v_k_1615_,
                            v_v_1616_,
                            v_l_1617_,
                            v_impl_1624_,
                        );
                        return v___x_1625_;
                    } else {
                        lean_dec(v_k_1615_);
                        v___x_1626_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1626_, 0, v_v_1616_);
                        v___x_1627_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg___lam__1(v_b_u2082_1610_, v___f_1613_, v___x_1626_);
                        v_val_1628_ = lean_ctor_get(v___x_1627_, 0);
                        lean_inc(v_val_1628_);
                        lean_dec(v___x_1627_);
                        if v_isShared_1621_ == 0 {
                            lean_ctor_set(v___x_1620_, 2, v_val_1628_);
                            lean_ctor_set(v___x_1620_, 1, v_k_1611_);
                            v___x_1630_ = v___x_1620_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 5, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_size_1614_);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_k_1611_);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_val_1628_);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 3, v_l_1617_);
                            lean_ctor_set(v_reuseFailAlloc_1631_, 4, v_r_1618_);
                            v___x_1630_ = v_reuseFailAlloc_1631_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_1620_);
                    lean_dec(v_size_1614_);
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
    mut v_init_1640_: *mut LeanObject,
    mut v_x_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_1645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1647_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1641_) == 0 {
                    v_k_1642_ = lean_ctor_get(v_x_1641_, 1);
                    lean_inc(v_k_1642_);
                    v_v_1643_ = lean_ctor_get(v_x_1641_, 2);
                    lean_inc(v_v_1643_);
                    v_l_1644_ = lean_ctor_get(v_x_1641_, 3);
                    lean_inc(v_l_1644_);
                    v_r_1645_ = lean_ctor_get(v_x_1641_, 4);
                    lean_inc(v_r_1645_);
                    lean_dec_ref_known(v_x_1641_, 5);
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
    mut v_t_u2081_1649_: *mut LeanObject,
    mut v_t_u2082_1650_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1651_: *mut LeanObject = core::ptr::null_mut();
    v___x_1651_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_t_u2081_1649_, v_t_u2082_1650_);
    return v___x_1651_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0(
    mut v_b_u2082_1652_: *mut LeanObject,
    mut v_k_1653_: *mut LeanObject,
    mut v_t_1654_: *mut LeanObject,
    mut v_hl_1655_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1656_: *mut LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Std_DTreeMap_Internal_Impl_Const_alter___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__0___redArg(v_b_u2082_1652_, v_k_1653_, v_t_1654_);
    return v___x_1656_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1(
    mut v_init_1657_: *mut LeanObject,
    mut v_t_1658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    v___x_1659_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_PrettyPrinter_Delaborator_OptionsPerPos_merge_spec__1_spec__1(v_init_1657_, v_t_1658_);
    return v___x_1659_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0(
    mut v_toPure_1660_: *mut LeanObject,
    mut v_____do__lift_1661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_expr_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut LeanObject = core::ptr::null_mut();
    v_expr_1662_ = lean_ctor_get(v_____do__lift_1661_, 0);
    lean_inc_ref(v_expr_1662_);
    lean_dec_ref(v_____do__lift_1661_);
    v___x_1663_ = lean_apply_2(v_toPure_1660_, lean_box(0), v_expr_1662_);
    return v___x_1663_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(
    mut v_inst_1664_: *mut LeanObject,
    mut v_inst_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1666_ = lean_ctor_get(v_inst_1664_, 0);
    lean_inc_ref(v_toApplicative_1666_);
    v_toBind_1667_ = lean_ctor_get(v_inst_1664_, 1);
    lean_inc(v_toBind_1667_);
    lean_dec_ref(v_inst_1664_);
    v_toPure_1668_ = lean_ctor_get(v_toApplicative_1666_, 1);
    lean_inc(v_toPure_1668_);
    lean_dec_ref(v_toApplicative_1666_);
    v___f_1669_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1669_, 0, v_toPure_1668_);
    v___x_1670_ = lean_apply_4(
        v_toBind_1667_,
        lean_box(0),
        lean_box(0),
        v_inst_1665_,
        v___f_1669_,
    );
    return v___x_1670_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr(
    mut v_m_1671_: *mut LeanObject,
    mut v_inst_1672_: *mut LeanObject,
    mut v_inst_1673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v___x_1674_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1672_, v_inst_1673_);
    return v___x_1674_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0(
    mut v_toPure_1675_: *mut LeanObject,
    mut v_____do__lift_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_1677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut LeanObject = core::ptr::null_mut();
    v_pos_1677_ = lean_ctor_get(v_____do__lift_1676_, 1);
    lean_inc(v_pos_1677_);
    lean_dec_ref(v_____do__lift_1676_);
    v___x_1678_ = lean_apply_2(v_toPure_1675_, lean_box(0), v_pos_1677_);
    return v___x_1678_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(
    mut v_inst_1679_: *mut LeanObject,
    mut v_inst_1680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1681_ = lean_ctor_get(v_inst_1679_, 0);
    lean_inc_ref(v_toApplicative_1681_);
    v_toBind_1682_ = lean_ctor_get(v_inst_1679_, 1);
    lean_inc(v_toBind_1682_);
    lean_dec_ref(v_inst_1679_);
    v_toPure_1683_ = lean_ctor_get(v_toApplicative_1681_, 1);
    lean_inc(v_toPure_1683_);
    lean_dec_ref(v_toApplicative_1681_);
    v___f_1684_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1684_, 0, v_toPure_1683_);
    v___x_1685_ = lean_apply_4(
        v_toBind_1682_,
        lean_box(0),
        lean_box(0),
        v_inst_1680_,
        v___f_1684_,
    );
    return v___x_1685_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos(
    mut v_m_1686_: *mut LeanObject,
    mut v_inst_1687_: *mut LeanObject,
    mut v_inst_1688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1689_: *mut LeanObject = core::ptr::null_mut();
    v___x_1689_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_1687_, v_inst_1688_);
    return v___x_1689_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0(
    mut v_childIdx_1690_: *mut LeanObject,
    mut v_child_1691_: *mut LeanObject,
    mut v_cfg_1692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1696_: u8 = 0;
    let mut v___x_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1701_: u8 = 0;
    let mut v_unused_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_1693_ = lean_ctor_get(v_cfg_1692_, 1);
                v_isSharedCheck_1701_ = (!lean_is_exclusive(v_cfg_1692_)) as u8;
                if v_isSharedCheck_1701_ == 0 {
                    v_unused_1702_ = lean_ctor_get(v_cfg_1692_, 0);
                    lean_dec(v_unused_1702_);
                    v___x_1695_ = v_cfg_1692_;
                    v_isShared_1696_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_1693_);
                    lean_dec(v_cfg_1692_);
                    v___x_1695_ = lean_box(0);
                    v_isShared_1696_ = v_isSharedCheck_1701_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1697_ = l_Lean_SubExpr_Pos_push(v_pos_1693_, v_childIdx_1690_);
                lean_dec(v_pos_1693_);
                if v_isShared_1696_ == 0 {
                    lean_ctor_set(v___x_1695_, 1, v___x_1697_);
                    lean_ctor_set(v___x_1695_, 0, v_child_1691_);
                    v___x_1699_ = v___x_1695_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1700_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1700_, 0, v_child_1691_);
                    lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
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
    mut v_inst_1703_: *mut LeanObject,
    mut v_child_1704_: *mut LeanObject,
    mut v_childIdx_1705_: *mut LeanObject,
    mut v_x_1706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut LeanObject = core::ptr::null_mut();
    v___f_1707_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1707_, 0, v_childIdx_1705_);
    lean_closure_set(v___f_1707_, 1, v_child_1704_);
    v___x_1708_ = lean_apply_3(v_inst_1703_, lean_box(0), v___f_1707_, v_x_1706_);
    return v___x_1708_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_descend(
    mut v_00_u03b1_1709_: *mut LeanObject,
    mut v_m_1710_: *mut LeanObject,
    mut v_inst_1711_: *mut LeanObject,
    mut v_child_1712_: *mut LeanObject,
    mut v_childIdx_1713_: *mut LeanObject,
    mut v_x_1714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1715_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1711_,
        v_child_1712_,
        v_childIdx_1713_,
        v_x_1714_,
    );
    return v___x_1715_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(
    mut v_inst_1716_: *mut LeanObject,
    mut v_x_1717_: *mut LeanObject,
    mut v_____do__lift_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    v___x_1719_ = l_Lean_Expr_appFn_x21(v_____do__lift_1718_);
    v___x_1720_ = lean_unsigned_to_nat(0);
    v___x_1721_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1716_,
        v___x_1719_,
        v___x_1720_,
        v_x_1717_,
    );
    return v___x_1721_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed(
    mut v_inst_1722_: *mut LeanObject,
    mut v_x_1723_: *mut LeanObject,
    mut v_____do__lift_1724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1725_: *mut LeanObject = core::ptr::null_mut();
    v_res_1725_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0(
        v_inst_1722_,
        v_x_1723_,
        v_____do__lift_1724_,
    );
    lean_dec_ref(v_____do__lift_1724_);
    return v_res_1725_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
    mut v_inst_1726_: *mut LeanObject,
    mut v_inst_1727_: *mut LeanObject,
    mut v_inst_1728_: *mut LeanObject,
    mut v_x_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1733_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1730_ = lean_ctor_get(v_inst_1726_, 1);
    lean_inc(v_toBind_1730_);
    v___f_1731_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1731_, 0, v_inst_1728_);
    lean_closure_set(v___f_1731_, 1, v_x_1729_);
    v___x_1732_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1726_, v_inst_1727_);
    v___x_1733_ = lean_apply_4(
        v_toBind_1730_,
        lean_box(0),
        lean_box(0),
        v___x_1732_,
        v___f_1731_,
    );
    return v___x_1733_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn(
    mut v_00_u03b1_1734_: *mut LeanObject,
    mut v_m_1735_: *mut LeanObject,
    mut v_inst_1736_: *mut LeanObject,
    mut v_inst_1737_: *mut LeanObject,
    mut v_inst_1738_: *mut LeanObject,
    mut v_x_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFn___redArg(
        v_inst_1736_,
        v_inst_1737_,
        v_inst_1738_,
        v_x_1739_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(
    mut v_inst_1741_: *mut LeanObject,
    mut v_x_1742_: *mut LeanObject,
    mut v_____do__lift_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ = l_Lean_Expr_appArg_x21(v_____do__lift_1743_);
    v___x_1745_ = lean_unsigned_to_nat(1);
    v___x_1746_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1741_,
        v___x_1744_,
        v___x_1745_,
        v_x_1742_,
    );
    return v___x_1746_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed(
    mut v_inst_1747_: *mut LeanObject,
    mut v_x_1748_: *mut LeanObject,
    mut v_____do__lift_1749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1750_: *mut LeanObject = core::ptr::null_mut();
    v_res_1750_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0(
        v_inst_1747_,
        v_x_1748_,
        v_____do__lift_1749_,
    );
    lean_dec_ref(v_____do__lift_1749_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
    mut v_inst_1751_: *mut LeanObject,
    mut v_inst_1752_: *mut LeanObject,
    mut v_inst_1753_: *mut LeanObject,
    mut v_x_1754_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1758_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1755_ = lean_ctor_get(v_inst_1751_, 1);
    lean_inc(v_toBind_1755_);
    v___f_1756_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1756_, 0, v_inst_1753_);
    lean_closure_set(v___f_1756_, 1, v_x_1754_);
    v___x_1757_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1751_, v_inst_1752_);
    v___x_1758_ = lean_apply_4(
        v_toBind_1755_,
        lean_box(0),
        lean_box(0),
        v___x_1757_,
        v___f_1756_,
    );
    return v___x_1758_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg(
    mut v_00_u03b1_1759_: *mut LeanObject,
    mut v_m_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
    mut v_inst_1763_: *mut LeanObject,
    mut v_x_1764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1765_: *mut LeanObject = core::ptr::null_mut();
    v___x_1765_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1761_,
        v_inst_1762_,
        v_inst_1763_,
        v_x_1764_,
    );
    return v___x_1765_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0(
    mut v_inst_1766_: *mut LeanObject,
    mut v_x_1767_: *mut LeanObject,
    mut v_____do__lift_1768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1771_: *mut LeanObject,
    mut v_toBind_1772_: *mut LeanObject,
    mut v___f_1773_: *mut LeanObject,
    mut v_____do__lift_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    v___x_1775_ = lean_alloc_closure(
        l_Lean_Meta_inferType___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___x_1775_, 0, v_____do__lift_1774_);
    v___x_1776_ = lean_apply_2(v_inst_1771_, lean_box(0), v___x_1775_);
    v___x_1777_ = lean_apply_4(
        v_toBind_1772_,
        lean_box(0),
        lean_box(0),
        v___x_1776_,
        v___f_1773_,
    );
    return v___x_1777_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg(
    mut v_inst_1778_: *mut LeanObject,
    mut v_inst_1779_: *mut LeanObject,
    mut v_inst_1780_: *mut LeanObject,
    mut v_inst_1781_: *mut LeanObject,
    mut v_x_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1783_ = lean_ctor_get(v_inst_1778_, 1);
    lean_inc_n(v_toBind_1783_, 2);
    v___f_1784_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1784_, 0, v_inst_1780_);
    lean_closure_set(v___f_1784_, 1, v_x_1782_);
    v___f_1785_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withType___redArg___lam__1
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1785_, 0, v_inst_1781_);
    lean_closure_set(v___f_1785_, 1, v_toBind_1783_);
    lean_closure_set(v___f_1785_, 2, v___f_1784_);
    v___x_1786_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1778_, v_inst_1779_);
    v___x_1787_ = lean_apply_4(
        v_toBind_1783_,
        lean_box(0),
        lean_box(0),
        v___x_1786_,
        v___f_1785_,
    );
    return v___x_1787_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withType(
    mut v_00_u03b1_1788_: *mut LeanObject,
    mut v_m_1789_: *mut LeanObject,
    mut v_inst_1790_: *mut LeanObject,
    mut v_inst_1791_: *mut LeanObject,
    mut v_inst_1792_: *mut LeanObject,
    mut v_inst_1793_: *mut LeanObject,
    mut v_x_1794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_xa_1796_: *mut LeanObject,
    mut v_inst_1797_: *mut LeanObject,
    mut v_inst_1798_: *mut LeanObject,
    mut v_inst_1799_: *mut LeanObject,
    mut v_acc_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    v___x_1801_ = lean_apply_1(v_xa_1796_, v_acc_1800_);
    v___x_1802_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1797_,
        v_inst_1798_,
        v_inst_1799_,
        v___x_1801_,
    );
    return v___x_1802_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1(
    mut v_xf_1803_: *mut LeanObject,
    mut v_inst_1804_: *mut LeanObject,
    mut v_inst_1805_: *mut LeanObject,
    mut v_inst_1806_: *mut LeanObject,
    mut v_xa_1807_: *mut LeanObject,
    mut v_toBind_1808_: *mut LeanObject,
    mut v___f_1809_: *mut LeanObject,
    mut v_____do__lift_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: u8 = 0;
    v___x_1811_ = l_Lean_Expr_isApp(v_____do__lift_1810_);
    if v___x_1811_ == 0 {
        lean_dec(v___f_1809_);
        lean_dec(v_toBind_1808_);
        lean_dec(v_xa_1807_);
        lean_dec(v_inst_1806_);
        lean_dec(v_inst_1805_);
        lean_dec_ref(v_inst_1804_);
        return v_xf_1803_;
    } else {
        let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_inst_1806_);
        lean_inc(v_inst_1805_);
        lean_inc_ref(v_inst_1804_);
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
        v___x_1814_ = lean_apply_4(
            v_toBind_1808_,
            lean_box(0),
            lean_box(0),
            v___x_1813_,
            v___f_1809_,
        );
        return v___x_1814_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed(
    mut v_xf_1815_: *mut LeanObject,
    mut v_inst_1816_: *mut LeanObject,
    mut v_inst_1817_: *mut LeanObject,
    mut v_inst_1818_: *mut LeanObject,
    mut v_xa_1819_: *mut LeanObject,
    mut v_toBind_1820_: *mut LeanObject,
    mut v___f_1821_: *mut LeanObject,
    mut v_____do__lift_1822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1823_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_____do__lift_1822_);
    return v_res_1823_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg(
    mut v_inst_1824_: *mut LeanObject,
    mut v_inst_1825_: *mut LeanObject,
    mut v_inst_1826_: *mut LeanObject,
    mut v_xf_1827_: *mut LeanObject,
    mut v_xa_1828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1829_ = lean_ctor_get(v_inst_1824_, 1);
    lean_inc_n(v_toBind_1829_, 2);
    lean_inc(v_inst_1826_);
    lean_inc_n(v_inst_1825_, 2);
    lean_inc_ref_n(v_inst_1824_, 2);
    lean_inc(v_xa_1828_);
    v___f_1830_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1830_, 0, v_xa_1828_);
    lean_closure_set(v___f_1830_, 1, v_inst_1824_);
    lean_closure_set(v___f_1830_, 2, v_inst_1825_);
    lean_closure_set(v___f_1830_, 3, v_inst_1826_);
    v___f_1831_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_1831_, 0, v_xf_1827_);
    lean_closure_set(v___f_1831_, 1, v_inst_1824_);
    lean_closure_set(v___f_1831_, 2, v_inst_1825_);
    lean_closure_set(v___f_1831_, 3, v_inst_1826_);
    lean_closure_set(v___f_1831_, 4, v_xa_1828_);
    lean_closure_set(v___f_1831_, 5, v_toBind_1829_);
    lean_closure_set(v___f_1831_, 6, v___f_1830_);
    v___x_1832_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1824_, v_inst_1825_);
    v___x_1833_ = lean_apply_4(
        v_toBind_1829_,
        lean_box(0),
        lean_box(0),
        v___x_1832_,
        v___f_1831_,
    );
    return v___x_1833_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppFnArgs(
    mut v_00_u03b1_1834_: *mut LeanObject,
    mut v_m_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
    mut v_inst_1837_: *mut LeanObject,
    mut v_inst_1838_: *mut LeanObject,
    mut v_xf_1839_: *mut LeanObject,
    mut v_xa_1840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1841_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_xa_1842_: *mut LeanObject,
    mut v_inst_1843_: *mut LeanObject,
    mut v_inst_1844_: *mut LeanObject,
    mut v_inst_1845_: *mut LeanObject,
    mut v_acc_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1847_ = lean_apply_1(v_xa_1842_, v_acc_1846_);
    v___x_1848_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withAppArg___redArg(
        v_inst_1843_,
        v_inst_1844_,
        v_inst_1845_,
        v___x_1847_,
    );
    return v___x_1848_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1(
    mut v_maxArgs_1849_: *mut LeanObject,
    mut v_inst_1850_: *mut LeanObject,
    mut v_inst_1851_: *mut LeanObject,
    mut v_inst_1852_: *mut LeanObject,
    mut v_xf_1853_: *mut LeanObject,
    mut v_xa_1854_: *mut LeanObject,
    mut v_toBind_1855_: *mut LeanObject,
    mut v___f_1856_: *mut LeanObject,
    mut v_____do__lift_1857_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1859_: u8 = 0;
    v_zero_1858_ = lean_unsigned_to_nat(0);
    v_isZero_1859_ = lean_nat_dec_eq(v_maxArgs_1849_, v_zero_1858_);
    if v_isZero_1859_ == 0 {
        if lean_obj_tag(v_____do__lift_1857_) == 5 {
            let mut v_one_1860_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1861_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
            v_one_1860_ = lean_unsigned_to_nat(1);
            v_n_1861_ = lean_nat_sub(v_maxArgs_1849_, v_one_1860_);
            lean_inc(v_inst_1852_);
            lean_inc(v_inst_1851_);
            lean_inc_ref(v_inst_1850_);
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
            v___x_1864_ = lean_apply_4(
                v_toBind_1855_,
                lean_box(0),
                lean_box(0),
                v___x_1863_,
                v___f_1856_,
            );
            return v___x_1864_;
        } else {
            lean_dec(v___f_1856_);
            lean_dec(v_toBind_1855_);
            lean_dec(v_xa_1854_);
            lean_dec(v_inst_1852_);
            lean_dec(v_inst_1851_);
            lean_dec_ref(v_inst_1850_);
            return v_xf_1853_;
        }
    } else {
        lean_dec(v___f_1856_);
        lean_dec(v_toBind_1855_);
        lean_dec(v_xa_1854_);
        lean_dec(v_inst_1852_);
        lean_dec(v_inst_1851_);
        lean_dec_ref(v_inst_1850_);
        return v_xf_1853_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed(
    mut v_maxArgs_1865_: *mut LeanObject,
    mut v_inst_1866_: *mut LeanObject,
    mut v_inst_1867_: *mut LeanObject,
    mut v_inst_1868_: *mut LeanObject,
    mut v_xf_1869_: *mut LeanObject,
    mut v_xa_1870_: *mut LeanObject,
    mut v_toBind_1871_: *mut LeanObject,
    mut v___f_1872_: *mut LeanObject,
    mut v_____do__lift_1873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1874_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_____do__lift_1873_);
    lean_dec(v_maxArgs_1865_);
    return v_res_1874_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg(
    mut v_inst_1875_: *mut LeanObject,
    mut v_inst_1876_: *mut LeanObject,
    mut v_inst_1877_: *mut LeanObject,
    mut v_maxArgs_1878_: *mut LeanObject,
    mut v_xf_1879_: *mut LeanObject,
    mut v_xa_1880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1881_ = lean_ctor_get(v_inst_1875_, 1);
    lean_inc_n(v_toBind_1881_, 2);
    lean_inc(v_inst_1877_);
    lean_inc_n(v_inst_1876_, 2);
    lean_inc_ref_n(v_inst_1875_, 2);
    lean_inc(v_xa_1880_);
    v___f_1882_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__0
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1882_, 0, v_xa_1880_);
    lean_closure_set(v___f_1882_, 1, v_inst_1875_);
    lean_closure_set(v___f_1882_, 2, v_inst_1876_);
    lean_closure_set(v___f_1882_, 3, v_inst_1877_);
    v___f_1883_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        9,
        8,
    );
    lean_closure_set(v___f_1883_, 0, v_maxArgs_1878_);
    lean_closure_set(v___f_1883_, 1, v_inst_1875_);
    lean_closure_set(v___f_1883_, 2, v_inst_1876_);
    lean_closure_set(v___f_1883_, 3, v_inst_1877_);
    lean_closure_set(v___f_1883_, 4, v_xf_1879_);
    lean_closure_set(v___f_1883_, 5, v_xa_1880_);
    lean_closure_set(v___f_1883_, 6, v_toBind_1881_);
    lean_closure_set(v___f_1883_, 7, v___f_1882_);
    v___x_1884_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1875_, v_inst_1876_);
    v___x_1885_ = lean_apply_4(
        v_toBind_1881_,
        lean_box(0),
        lean_box(0),
        v___x_1884_,
        v___f_1883_,
    );
    return v___x_1885_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFnArgs(
    mut v_00_u03b1_1886_: *mut LeanObject,
    mut v_m_1887_: *mut LeanObject,
    mut v_inst_1888_: *mut LeanObject,
    mut v_inst_1889_: *mut LeanObject,
    mut v_inst_1890_: *mut LeanObject,
    mut v_maxArgs_1891_: *mut LeanObject,
    mut v_xf_1892_: *mut LeanObject,
    mut v_xa_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
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
    mut v___y_1895_: *mut LeanObject,
    mut v_e_1896_: *mut LeanObject,
    mut v_newPos_1897_: *mut LeanObject,
    mut v_cfg_1898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    v___x_1899_ = l_Lean_Expr_getBoundedAppFn(v___y_1895_, v_e_1896_);
    v___x_1900_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1900_, 0, v___x_1899_);
    lean_ctor_set(v___x_1900_, 1, v_newPos_1897_);
    return v___x_1900_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed(
    mut v___y_1901_: *mut LeanObject,
    mut v_e_1902_: *mut LeanObject,
    mut v_newPos_1903_: *mut LeanObject,
    mut v_cfg_1904_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1905_: *mut LeanObject = core::ptr::null_mut();
    v_res_1905_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0(
        v___y_1901_,
        v_e_1902_,
        v_newPos_1903_,
        v_cfg_1904_,
    );
    lean_dec_ref(v_cfg_1904_);
    lean_dec_ref(v_e_1902_);
    return v_res_1905_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(
    mut v___y_1906_: *mut LeanObject,
    mut v_e_1907_: *mut LeanObject,
    mut v_inst_1908_: *mut LeanObject,
    mut v_xf_1909_: *mut LeanObject,
    mut v_____do__lift_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_newPos_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    v_newPos_1911_ = l_Lean_SubExpr_Pos_pushNaryFn(v___y_1906_, v_____do__lift_1910_);
    v___f_1912_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_1912_, 0, v___y_1906_);
    lean_closure_set(v___f_1912_, 1, v_e_1907_);
    lean_closure_set(v___f_1912_, 2, v_newPos_1911_);
    v___x_1913_ = lean_apply_3(v_inst_1908_, lean_box(0), v___f_1912_, v_xf_1909_);
    return v___x_1913_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed(
    mut v___y_1914_: *mut LeanObject,
    mut v_e_1915_: *mut LeanObject,
    mut v_inst_1916_: *mut LeanObject,
    mut v_xf_1917_: *mut LeanObject,
    mut v_____do__lift_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1919_: *mut LeanObject = core::ptr::null_mut();
    v_res_1919_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1(
        v___y_1914_,
        v_e_1915_,
        v_inst_1916_,
        v_xf_1917_,
        v_____do__lift_1918_,
    );
    lean_dec(v_____do__lift_1918_);
    return v_res_1919_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2(
    mut v_inst_1920_: *mut LeanObject,
    mut v_xf_1921_: *mut LeanObject,
    mut v_inst_1922_: *mut LeanObject,
    mut v_inst_1923_: *mut LeanObject,
    mut v_toBind_1924_: *mut LeanObject,
    mut v_maxArgs_1925_: *mut LeanObject,
    mut v_e_1926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1932_ = l_Lean_Expr_getAppNumArgs(v_e_1926_);
                v___x_1933_ = lean_nat_dec_le(v_maxArgs_1925_, v___x_1932_);
                if v___x_1933_ == 0 {
                    lean_dec(v_maxArgs_1925_);
                    v___y_1928_ = v___x_1932_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_1932_);
                    v___y_1928_ = v_maxArgs_1925_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1929_ = lean_alloc_closure(l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__1___boxed as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_1929_, 0, v___y_1928_);
                lean_closure_set(v___f_1929_, 1, v_e_1926_);
                lean_closure_set(v___f_1929_, 2, v_inst_1920_);
                lean_closure_set(v___f_1929_, 3, v_xf_1921_);
                v___x_1930_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(
                    v_inst_1922_,
                    v_inst_1923_,
                );
                v___x_1931_ = lean_apply_4(
                    v_toBind_1924_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1934_: *mut LeanObject,
    mut v_inst_1935_: *mut LeanObject,
    mut v_inst_1936_: *mut LeanObject,
    mut v_maxArgs_1937_: *mut LeanObject,
    mut v_xf_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1939_ = lean_ctor_get(v_inst_1934_, 1);
    lean_inc_n(v_toBind_1939_, 2);
    lean_inc(v_inst_1935_);
    lean_inc_ref(v_inst_1934_);
    v___f_1940_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn___redArg___lam__2
            as *mut core::ffi::c_void,
        7,
        6,
    );
    lean_closure_set(v___f_1940_, 0, v_inst_1936_);
    lean_closure_set(v___f_1940_, 1, v_xf_1938_);
    lean_closure_set(v___f_1940_, 2, v_inst_1934_);
    lean_closure_set(v___f_1940_, 3, v_inst_1935_);
    lean_closure_set(v___f_1940_, 4, v_toBind_1939_);
    lean_closure_set(v___f_1940_, 5, v_maxArgs_1937_);
    v___x_1941_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1934_, v_inst_1935_);
    v___x_1942_ = lean_apply_4(
        v_toBind_1939_,
        lean_box(0),
        lean_box(0),
        v___x_1941_,
        v___f_1940_,
    );
    return v___x_1942_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBoundedAppFn(
    mut v_00_u03b1_1943_: *mut LeanObject,
    mut v_m_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
    mut v_inst_1946_: *mut LeanObject,
    mut v_inst_1947_: *mut LeanObject,
    mut v_maxArgs_1948_: *mut LeanObject,
    mut v_xf_1949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_inst_1951_: *mut LeanObject,
    mut v_x_1952_: *mut LeanObject,
    mut v_____do__lift_1953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    v___x_1954_ = l_Lean_Expr_bindingDomain_x21(v_____do__lift_1953_);
    v___x_1955_ = lean_unsigned_to_nat(0);
    v___x_1956_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1951_,
        v___x_1954_,
        v___x_1955_,
        v_x_1952_,
    );
    return v___x_1956_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed(
    mut v_inst_1957_: *mut LeanObject,
    mut v_x_1958_: *mut LeanObject,
    mut v_____do__lift_1959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1960_: *mut LeanObject = core::ptr::null_mut();
    v_res_1960_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0(
        v_inst_1957_,
        v_x_1958_,
        v_____do__lift_1959_,
    );
    lean_dec_ref(v_____do__lift_1959_);
    return v_res_1960_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(
    mut v_inst_1961_: *mut LeanObject,
    mut v_inst_1962_: *mut LeanObject,
    mut v_inst_1963_: *mut LeanObject,
    mut v_x_1964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1968_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_1965_ = lean_ctor_get(v_inst_1961_, 1);
    lean_inc(v_toBind_1965_);
    v___f_1966_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1966_, 0, v_inst_1963_);
    lean_closure_set(v___f_1966_, 1, v_x_1964_);
    v___x_1967_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_1961_, v_inst_1962_);
    v___x_1968_ = lean_apply_4(
        v_toBind_1965_,
        lean_box(0),
        lean_box(0),
        v___x_1967_,
        v___f_1966_,
    );
    return v___x_1968_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain(
    mut v_00_u03b1_1969_: *mut LeanObject,
    mut v_m_1970_: *mut LeanObject,
    mut v_inst_1971_: *mut LeanObject,
    mut v_inst_1972_: *mut LeanObject,
    mut v_inst_1973_: *mut LeanObject,
    mut v_x_1974_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1975_: *mut LeanObject = core::ptr::null_mut();
    v___x_1975_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingDomain___redArg(
        v_inst_1971_,
        v_inst_1972_,
        v_inst_1973_,
        v_x_1974_,
    );
    return v___x_1975_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(
    mut v_e_1976_: *mut LeanObject,
    mut v_fvar_1977_: *mut LeanObject,
    mut v_x_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
    mut v_b_1980_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v___x_1981_ = l_Lean_Expr_bindingBody_x21(v_e_1976_);
    v___x_1982_ = lean_expr_instantiate1(v___x_1981_, v_fvar_1977_);
    lean_dec_ref(v___x_1981_);
    v___x_1983_ = lean_unsigned_to_nat(1);
    v___x_1984_ = lean_apply_1(v_x_1978_, v_b_1980_);
    v___x_1985_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_1979_,
        v___x_1982_,
        v___x_1983_,
        v___x_1984_,
    );
    return v___x_1985_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed(
    mut v_e_1986_: *mut LeanObject,
    mut v_fvar_1987_: *mut LeanObject,
    mut v_x_1988_: *mut LeanObject,
    mut v_inst_1989_: *mut LeanObject,
    mut v_b_1990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1991_: *mut LeanObject = core::ptr::null_mut();
    v_res_1991_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0(
        v_e_1986_,
        v_fvar_1987_,
        v_x_1988_,
        v_inst_1989_,
        v_b_1990_,
    );
    lean_dec_ref(v_fvar_1987_);
    lean_dec_ref(v_e_1986_);
    return v_res_1991_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1(
    mut v_e_1992_: *mut LeanObject,
    mut v_x_1993_: *mut LeanObject,
    mut v_inst_1994_: *mut LeanObject,
    mut v_v_1995_: *mut LeanObject,
    mut v_toBind_1996_: *mut LeanObject,
    mut v_fvar_1997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_fvar_1997_);
    v___f_1998_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_1998_, 0, v_e_1992_);
    lean_closure_set(v___f_1998_, 1, v_fvar_1997_);
    lean_closure_set(v___f_1998_, 2, v_x_1993_);
    lean_closure_set(v___f_1998_, 3, v_inst_1994_);
    v___x_1999_ = lean_apply_1(v_v_1995_, v_fvar_1997_);
    v___x_2000_ = lean_apply_4(
        v_toBind_1996_,
        lean_box(0),
        lean_box(0),
        v___x_1999_,
        v___f_1998_,
    );
    return v___x_2000_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2(
    mut v_x_2001_: *mut LeanObject,
    mut v_inst_2002_: *mut LeanObject,
    mut v_v_2003_: *mut LeanObject,
    mut v_toBind_2004_: *mut LeanObject,
    mut v_inst_2005_: *mut LeanObject,
    mut v_inst_2006_: *mut LeanObject,
    mut v_n_2007_: *mut LeanObject,
    mut v_e_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_e_2008_);
    v___f_2009_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2009_, 0, v_e_2008_);
    lean_closure_set(v___f_2009_, 1, v_x_2001_);
    lean_closure_set(v___f_2009_, 2, v_inst_2002_);
    lean_closure_set(v___f_2009_, 3, v_v_2003_);
    lean_closure_set(v___f_2009_, 4, v_toBind_2004_);
    v___x_2010_ = l_Lean_Expr_binderInfo(v_e_2008_);
    v___x_2011_ = l_Lean_Expr_bindingDomain_x21(v_e_2008_);
    lean_dec_ref(v_e_2008_);
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
    mut v_inst_2014_: *mut LeanObject,
    mut v_inst_2015_: *mut LeanObject,
    mut v_inst_2016_: *mut LeanObject,
    mut v_inst_2017_: *mut LeanObject,
    mut v_n_2018_: *mut LeanObject,
    mut v_v_2019_: *mut LeanObject,
    mut v_x_2020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2021_ = lean_ctor_get(v_inst_2014_, 1);
    lean_inc_n(v_toBind_2021_, 2);
    lean_inc_ref(v_inst_2014_);
    v___f_2022_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2022_, 0, v_x_2020_);
    lean_closure_set(v___f_2022_, 1, v_inst_2016_);
    lean_closure_set(v___f_2022_, 2, v_v_2019_);
    lean_closure_set(v___f_2022_, 3, v_toBind_2021_);
    lean_closure_set(v___f_2022_, 4, v_inst_2017_);
    lean_closure_set(v___f_2022_, 5, v_inst_2014_);
    lean_closure_set(v___f_2022_, 6, v_n_2018_);
    v___x_2023_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2014_, v_inst_2015_);
    v___x_2024_ = lean_apply_4(
        v_toBind_2021_,
        lean_box(0),
        lean_box(0),
        v___x_2023_,
        v___f_2022_,
    );
    return v___x_2024_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody_x27(
    mut v_00_u03b1_2025_: *mut LeanObject,
    mut v_m_2026_: *mut LeanObject,
    mut v_inst_2027_: *mut LeanObject,
    mut v_inst_2028_: *mut LeanObject,
    mut v_inst_2029_: *mut LeanObject,
    mut v_inst_2030_: *mut LeanObject,
    mut v_00_u03b2_2031_: *mut LeanObject,
    mut v_n_2032_: *mut LeanObject,
    mut v_v_2033_: *mut LeanObject,
    mut v_x_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2035_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_x_2036_: *mut LeanObject,
    mut v_x_2037_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_2036_);
    return v_x_2036_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed(
    mut v_x_2038_: *mut LeanObject,
    mut v_x_2039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2040_: *mut LeanObject = core::ptr::null_mut();
    v_res_2040_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0(
        v_x_2038_, v_x_2039_,
    );
    lean_dec(v_x_2038_);
    return v_res_2040_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(
    mut v_toPure_2041_: *mut LeanObject,
    mut v_x_2042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    v___x_2043_ = lean_box(0);
    v___x_2044_ = lean_apply_2(v_toPure_2041_, lean_box(0), v___x_2043_);
    return v___x_2044_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed(
    mut v_toPure_2045_: *mut LeanObject,
    mut v_x_2046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2047_: *mut LeanObject = core::ptr::null_mut();
    v_res_2047_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1(
        v_toPure_2045_,
        v_x_2046_,
    );
    lean_dec_ref(v_x_2046_);
    return v_res_2047_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg(
    mut v_inst_2048_: *mut LeanObject,
    mut v_inst_2049_: *mut LeanObject,
    mut v_inst_2050_: *mut LeanObject,
    mut v_inst_2051_: *mut LeanObject,
    mut v_n_2052_: *mut LeanObject,
    mut v_x_2053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2054_ = lean_ctor_get(v_inst_2048_, 0);
    v_toPure_2055_ = lean_ctor_get(v_toApplicative_2054_, 1);
    v___f_2056_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2056_, 0, v_x_2053_);
    lean_inc(v_toPure_2055_);
    v___f_2057_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withBindingBody___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2057_, 0, v_toPure_2055_);
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
    mut v_00_u03b1_2059_: *mut LeanObject,
    mut v_m_2060_: *mut LeanObject,
    mut v_inst_2061_: *mut LeanObject,
    mut v_inst_2062_: *mut LeanObject,
    mut v_inst_2063_: *mut LeanObject,
    mut v_inst_2064_: *mut LeanObject,
    mut v_n_2065_: *mut LeanObject,
    mut v_x_2066_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    v___x_2071_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2072_ = lean_unsigned_to_nat(34);
    v___x_2073_ = lean_unsigned_to_nat(110);
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
    mut v_inst_2077_: *mut LeanObject,
    mut v_x_2078_: *mut LeanObject,
    mut v___x_2079_: *mut LeanObject,
    mut v_____x_2080_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2080_) == 11 {
        let mut v_struct_2081_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
        v_struct_2081_ = lean_ctor_get(v_____x_2080_, 2);
        lean_inc_ref(v_struct_2081_);
        lean_dec_ref_known(v_____x_2080_, 3);
        v___x_2082_ = lean_unsigned_to_nat(0);
        v___x_2083_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2077_,
            v_struct_2081_,
            v___x_2082_,
            v_x_2078_,
        );
        return v___x_2083_;
    } else {
        let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____x_2080_);
        lean_dec(v_x_2078_);
        lean_dec(v_inst_2077_);
        v___x_2084_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__3);
        v___x_2085_ = l_panic___redArg(v___x_2079_, v___x_2084_);
        return v___x_2085_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed(
    mut v_inst_2086_: *mut LeanObject,
    mut v_x_2087_: *mut LeanObject,
    mut v___x_2088_: *mut LeanObject,
    mut v_____x_2089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2090_: *mut LeanObject = core::ptr::null_mut();
    v_res_2090_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0(
        v_inst_2086_,
        v_x_2087_,
        v___x_2088_,
        v_____x_2089_,
    );
    lean_dec(v___x_2088_);
    return v_res_2090_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg(
    mut v_inst_2091_: *mut LeanObject,
    mut v_inst_2092_: *mut LeanObject,
    mut v_inst_2093_: *mut LeanObject,
    mut v_inst_2094_: *mut LeanObject,
    mut v_x_2095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2096_ = lean_ctor_get(v_inst_2092_, 1);
    lean_inc(v_toBind_2096_);
    lean_inc_ref(v_inst_2092_);
    v___x_2097_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2092_, v_inst_2093_);
    v___x_2098_ = l_instInhabitedOfMonad___redArg(v_inst_2092_, v_inst_2091_);
    v___f_2099_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2099_, 0, v_inst_2094_);
    lean_closure_set(v___f_2099_, 1, v_x_2095_);
    lean_closure_set(v___f_2099_, 2, v___x_2098_);
    v___x_2100_ = lean_apply_4(
        v_toBind_2096_,
        lean_box(0),
        lean_box(0),
        v___x_2097_,
        v___f_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj(
    mut v_00_u03b1_2101_: *mut LeanObject,
    mut v_inst_2102_: *mut LeanObject,
    mut v_m_2103_: *mut LeanObject,
    mut v_inst_2104_: *mut LeanObject,
    mut v_inst_2105_: *mut LeanObject,
    mut v_inst_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_expr_2109_: *mut LeanObject,
    mut v_ctx_2110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pos_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2114_: u8 = 0;
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2118_: u8 = 0;
    let mut v_unused_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pos_2111_ = lean_ctor_get(v_ctx_2110_, 1);
                v_isSharedCheck_2118_ = (!lean_is_exclusive(v_ctx_2110_)) as u8;
                if v_isSharedCheck_2118_ == 0 {
                    v_unused_2119_ = lean_ctor_get(v_ctx_2110_, 0);
                    lean_dec(v_unused_2119_);
                    v___x_2113_ = v_ctx_2110_;
                    v_isShared_2114_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_pos_2111_);
                    lean_dec(v_ctx_2110_);
                    v___x_2113_ = lean_box(0);
                    v_isShared_2114_ = v_isSharedCheck_2118_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2114_ == 0 {
                    lean_ctor_set(v___x_2113_, 0, v_expr_2109_);
                    v___x_2116_ = v___x_2113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2117_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 0, v_expr_2109_);
                    lean_ctor_set(v_reuseFailAlloc_2117_, 1, v_pos_2111_);
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
-> *mut LeanObject {
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut LeanObject = core::ptr::null_mut();
    v___x_2121_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2122_ = lean_unsigned_to_nat(33);
    v___x_2123_ = lean_unsigned_to_nat(114);
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
    mut v_inst_2127_: *mut LeanObject,
    mut v_x_2128_: *mut LeanObject,
    mut v___x_2129_: *mut LeanObject,
    mut v_____x_2130_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2130_) == 10 {
        let mut v_expr_2131_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
        v_expr_2131_ = lean_ctor_get(v_____x_2130_, 1);
        lean_inc_ref(v_expr_2131_);
        lean_dec_ref_known(v_____x_2130_, 2);
        v___f_2132_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__0
                as *mut core::ffi::c_void,
            2,
            1,
        );
        lean_closure_set(v___f_2132_, 0, v_expr_2131_);
        v___x_2133_ = lean_apply_3(v_inst_2127_, lean_box(0), v___f_2132_, v_x_2128_);
        return v___x_2133_;
    } else {
        let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____x_2130_);
        lean_dec(v_x_2128_);
        lean_dec(v_inst_2127_);
        v___x_2134_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___closed__1);
        v___x_2135_ = l_panic___redArg(v___x_2129_, v___x_2134_);
        return v___x_2135_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed(
    mut v_inst_2136_: *mut LeanObject,
    mut v_x_2137_: *mut LeanObject,
    mut v___x_2138_: *mut LeanObject,
    mut v_____x_2139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2140_: *mut LeanObject = core::ptr::null_mut();
    v_res_2140_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1(
        v_inst_2136_,
        v_x_2137_,
        v___x_2138_,
        v_____x_2139_,
    );
    lean_dec(v___x_2138_);
    return v_res_2140_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg(
    mut v_inst_2141_: *mut LeanObject,
    mut v_inst_2142_: *mut LeanObject,
    mut v_inst_2143_: *mut LeanObject,
    mut v_inst_2144_: *mut LeanObject,
    mut v_x_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2146_ = lean_ctor_get(v_inst_2142_, 1);
    lean_inc(v_toBind_2146_);
    lean_inc_ref(v_inst_2142_);
    v___x_2147_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2142_, v_inst_2143_);
    v___x_2148_ = l_instInhabitedOfMonad___redArg(v_inst_2142_, v_inst_2141_);
    v___f_2149_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2149_, 0, v_inst_2144_);
    lean_closure_set(v___f_2149_, 1, v_x_2145_);
    lean_closure_set(v___f_2149_, 2, v___x_2148_);
    v___x_2150_ = lean_apply_4(
        v_toBind_2146_,
        lean_box(0),
        lean_box(0),
        v___x_2147_,
        v___f_2149_,
    );
    return v___x_2150_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withMDataExpr(
    mut v_00_u03b1_2151_: *mut LeanObject,
    mut v_inst_2152_: *mut LeanObject,
    mut v_m_2153_: *mut LeanObject,
    mut v_inst_2154_: *mut LeanObject,
    mut v_inst_2155_: *mut LeanObject,
    mut v_inst_2156_: *mut LeanObject,
    mut v_x_2157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2158_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    v___x_2160_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2161_ = lean_unsigned_to_nat(38);
    v___x_2162_ = lean_unsigned_to_nat(118);
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
    mut v_inst_2166_: *mut LeanObject,
    mut v_x_2167_: *mut LeanObject,
    mut v___x_2168_: *mut LeanObject,
    mut v_____x_2169_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2169_) == 8 {
        let mut v_type_2170_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2172_: *mut LeanObject = core::ptr::null_mut();
        v_type_2170_ = lean_ctor_get(v_____x_2169_, 1);
        lean_inc_ref(v_type_2170_);
        lean_dec_ref_known(v_____x_2169_, 4);
        v___x_2171_ = lean_unsigned_to_nat(0);
        v___x_2172_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2166_,
            v_type_2170_,
            v___x_2171_,
            v_x_2167_,
        );
        return v___x_2172_;
    } else {
        let mut v___x_2173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2174_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____x_2169_);
        lean_dec(v_x_2167_);
        lean_dec(v_inst_2166_);
        v___x_2173_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___closed__1);
        v___x_2174_ = l_panic___redArg(v___x_2168_, v___x_2173_);
        return v___x_2174_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed(
    mut v_inst_2175_: *mut LeanObject,
    mut v_x_2176_: *mut LeanObject,
    mut v___x_2177_: *mut LeanObject,
    mut v_____x_2178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2179_: *mut LeanObject = core::ptr::null_mut();
    v_res_2179_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0(
        v_inst_2175_,
        v_x_2176_,
        v___x_2177_,
        v_____x_2178_,
    );
    lean_dec(v___x_2177_);
    return v_res_2179_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg(
    mut v_inst_2180_: *mut LeanObject,
    mut v_inst_2181_: *mut LeanObject,
    mut v_inst_2182_: *mut LeanObject,
    mut v_inst_2183_: *mut LeanObject,
    mut v_x_2184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2185_ = lean_ctor_get(v_inst_2181_, 1);
    lean_inc(v_toBind_2185_);
    lean_inc_ref(v_inst_2181_);
    v___x_2186_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2181_, v_inst_2182_);
    v___x_2187_ = l_instInhabitedOfMonad___redArg(v_inst_2181_, v_inst_2180_);
    v___f_2188_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2188_, 0, v_inst_2183_);
    lean_closure_set(v___f_2188_, 1, v_x_2184_);
    lean_closure_set(v___f_2188_, 2, v___x_2187_);
    v___x_2189_ = lean_apply_4(
        v_toBind_2185_,
        lean_box(0),
        lean_box(0),
        v___x_2186_,
        v___f_2188_,
    );
    return v___x_2189_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetVarType(
    mut v_00_u03b1_2190_: *mut LeanObject,
    mut v_inst_2191_: *mut LeanObject,
    mut v_m_2192_: *mut LeanObject,
    mut v_inst_2193_: *mut LeanObject,
    mut v_inst_2194_: *mut LeanObject,
    mut v_inst_2195_: *mut LeanObject,
    mut v_x_2196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2197_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut LeanObject = core::ptr::null_mut();
    v___x_2199_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2200_ = lean_unsigned_to_nat(38);
    v___x_2201_ = lean_unsigned_to_nat(122);
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
    mut v_inst_2205_: *mut LeanObject,
    mut v_x_2206_: *mut LeanObject,
    mut v___x_2207_: *mut LeanObject,
    mut v_____x_2208_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2208_) == 8 {
        let mut v_value_2209_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
        v_value_2209_ = lean_ctor_get(v_____x_2208_, 2);
        lean_inc_ref(v_value_2209_);
        lean_dec_ref_known(v_____x_2208_, 4);
        v___x_2210_ = lean_unsigned_to_nat(1);
        v___x_2211_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
            v_inst_2205_,
            v_value_2209_,
            v___x_2210_,
            v_x_2206_,
        );
        return v___x_2211_;
    } else {
        let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2213_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____x_2208_);
        lean_dec(v_x_2206_);
        lean_dec(v_inst_2205_);
        v___x_2212_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___closed__1);
        v___x_2213_ = l_panic___redArg(v___x_2207_, v___x_2212_);
        return v___x_2213_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed(
    mut v_inst_2214_: *mut LeanObject,
    mut v_x_2215_: *mut LeanObject,
    mut v___x_2216_: *mut LeanObject,
    mut v_____x_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2218_: *mut LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0(
        v_inst_2214_,
        v_x_2215_,
        v___x_2216_,
        v_____x_2217_,
    );
    lean_dec(v___x_2216_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg(
    mut v_inst_2219_: *mut LeanObject,
    mut v_inst_2220_: *mut LeanObject,
    mut v_inst_2221_: *mut LeanObject,
    mut v_inst_2222_: *mut LeanObject,
    mut v_x_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2224_ = lean_ctor_get(v_inst_2220_, 1);
    lean_inc(v_toBind_2224_);
    lean_inc_ref(v_inst_2220_);
    v___x_2225_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2220_, v_inst_2221_);
    v___x_2226_ = l_instInhabitedOfMonad___redArg(v_inst_2220_, v_inst_2219_);
    v___f_2227_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2227_, 0, v_inst_2222_);
    lean_closure_set(v___f_2227_, 1, v_x_2223_);
    lean_closure_set(v___f_2227_, 2, v___x_2226_);
    v___x_2228_ = lean_apply_4(
        v_toBind_2224_,
        lean_box(0),
        lean_box(0),
        v___x_2225_,
        v___f_2227_,
    );
    return v___x_2228_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetValue(
    mut v_00_u03b1_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_m_2231_: *mut LeanObject,
    mut v_inst_2232_: *mut LeanObject,
    mut v_inst_2233_: *mut LeanObject,
    mut v_inst_2234_: *mut LeanObject,
    mut v_x_2235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_body_2237_: *mut LeanObject,
    mut v_inst_2238_: *mut LeanObject,
    mut v_x_2239_: *mut LeanObject,
    mut v_fvar_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_b_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v_b_2241_ = lean_expr_instantiate1(v_body_2237_, v_fvar_2240_);
    v___x_2242_ = lean_unsigned_to_nat(2);
    v___x_2243_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_descend___redArg(
        v_inst_2238_,
        v_b_2241_,
        v___x_2242_,
        v_x_2239_,
    );
    return v___x_2243_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed(
    mut v_body_2244_: *mut LeanObject,
    mut v_inst_2245_: *mut LeanObject,
    mut v_x_2246_: *mut LeanObject,
    mut v_fvar_2247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2248_: *mut LeanObject = core::ptr::null_mut();
    v_res_2248_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0(
        v_body_2244_,
        v_inst_2245_,
        v_x_2246_,
        v_fvar_2247_,
    );
    lean_dec_ref(v_fvar_2247_);
    lean_dec_ref(v_body_2244_);
    return v_res_2248_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1()
-> *mut LeanObject {
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    v___x_2250_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withProj___redArg___lam__0___closed__2;
    v___x_2251_ = lean_unsigned_to_nat(43);
    v___x_2252_ = lean_unsigned_to_nat(126);
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
    mut v_inst_2256_: *mut LeanObject,
    mut v_x_2257_: *mut LeanObject,
    mut v_inst_2258_: *mut LeanObject,
    mut v_inst_2259_: *mut LeanObject,
    mut v___x_2260_: *mut LeanObject,
    mut v_____x_2261_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____x_2261_) == 8 {
        let mut v_declName_2262_: *mut LeanObject = core::ptr::null_mut();
        let mut v_type_2263_: *mut LeanObject = core::ptr::null_mut();
        let mut v_value_2264_: *mut LeanObject = core::ptr::null_mut();
        let mut v_body_2265_: *mut LeanObject = core::ptr::null_mut();
        let mut v_nondep_2266_: u8 = 0;
        let mut v___f_2267_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2268_: u8 = 0;
        let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
        v_declName_2262_ = lean_ctor_get(v_____x_2261_, 0);
        lean_inc(v_declName_2262_);
        v_type_2263_ = lean_ctor_get(v_____x_2261_, 1);
        lean_inc_ref(v_type_2263_);
        v_value_2264_ = lean_ctor_get(v_____x_2261_, 2);
        lean_inc_ref(v_value_2264_);
        v_body_2265_ = lean_ctor_get(v_____x_2261_, 3);
        lean_inc_ref(v_body_2265_);
        v_nondep_2266_ = lean_ctor_get_uint8(
            v_____x_2261_,
            (core::mem::size_of::<*mut LeanObject>() * 4 + 8) as u32,
        );
        lean_dec_ref_known(v_____x_2261_, 4);
        v___f_2267_ = lean_alloc_closure(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_2267_, 0, v_body_2265_);
        lean_closure_set(v___f_2267_, 1, v_inst_2256_);
        lean_closure_set(v___f_2267_, 2, v_x_2257_);
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
        let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2271_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_____x_2261_);
        lean_dec_ref(v_inst_2259_);
        lean_dec_ref(v_inst_2258_);
        lean_dec(v_x_2257_);
        lean_dec(v_inst_2256_);
        v___x_2270_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___closed__1);
        v___x_2271_ = l_panic___redArg(v___x_2260_, v___x_2270_);
        return v___x_2271_;
    }
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed(
    mut v_inst_2272_: *mut LeanObject,
    mut v_x_2273_: *mut LeanObject,
    mut v_inst_2274_: *mut LeanObject,
    mut v_inst_2275_: *mut LeanObject,
    mut v___x_2276_: *mut LeanObject,
    mut v_____x_2277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2278_: *mut LeanObject = core::ptr::null_mut();
    v_res_2278_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1(
        v_inst_2272_,
        v_x_2273_,
        v_inst_2274_,
        v_inst_2275_,
        v___x_2276_,
        v_____x_2277_,
    );
    lean_dec(v___x_2276_);
    return v_res_2278_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg(
    mut v_inst_2279_: *mut LeanObject,
    mut v_inst_2280_: *mut LeanObject,
    mut v_inst_2281_: *mut LeanObject,
    mut v_inst_2282_: *mut LeanObject,
    mut v_inst_2283_: *mut LeanObject,
    mut v_x_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2285_ = lean_ctor_get(v_inst_2280_, 1);
    lean_inc(v_toBind_2285_);
    lean_inc_ref_n(v_inst_2280_, 2);
    v___x_2286_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2280_, v_inst_2281_);
    v___x_2287_ = l_instInhabitedOfMonad___redArg(v_inst_2280_, v_inst_2279_);
    v___f_2288_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2288_, 0, v_inst_2282_);
    lean_closure_set(v___f_2288_, 1, v_x_2284_);
    lean_closure_set(v___f_2288_, 2, v_inst_2283_);
    lean_closure_set(v___f_2288_, 3, v_inst_2280_);
    lean_closure_set(v___f_2288_, 4, v___x_2287_);
    v___x_2289_ = lean_apply_4(
        v_toBind_2285_,
        lean_box(0),
        lean_box(0),
        v___x_2286_,
        v___f_2288_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withLetBody(
    mut v_00_u03b1_2290_: *mut LeanObject,
    mut v_inst_2291_: *mut LeanObject,
    mut v_m_2292_: *mut LeanObject,
    mut v_inst_2293_: *mut LeanObject,
    mut v_inst_2294_: *mut LeanObject,
    mut v_inst_2295_: *mut LeanObject,
    mut v_inst_2296_: *mut LeanObject,
    mut v_x_2297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_e_2299_: *mut LeanObject,
    mut v_newPos_2300_: *mut LeanObject,
    mut v_cfg_2301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: *mut LeanObject = core::ptr::null_mut();
    v___x_2302_ = l_Lean_Expr_getAppFn(v_e_2299_);
    v___x_2303_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2303_, 0, v___x_2302_);
    lean_ctor_set(v___x_2303_, 1, v_newPos_2300_);
    return v___x_2303_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed(
    mut v_e_2304_: *mut LeanObject,
    mut v_newPos_2305_: *mut LeanObject,
    mut v_cfg_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2307_: *mut LeanObject = core::ptr::null_mut();
    v_res_2307_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0(
        v_e_2304_,
        v_newPos_2305_,
        v_cfg_2306_,
    );
    lean_dec_ref(v_cfg_2306_);
    lean_dec_ref(v_e_2304_);
    return v_res_2307_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(
    mut v_e_2308_: *mut LeanObject,
    mut v_inst_2309_: *mut LeanObject,
    mut v_x_2310_: *mut LeanObject,
    mut v_____do__lift_2311_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newPos_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    v___x_2312_ = l_Lean_Expr_getAppNumArgs(v_e_2308_);
    v_newPos_2313_ = l_Lean_SubExpr_Pos_pushNaryFn(v___x_2312_, v_____do__lift_2311_);
    lean_dec(v___x_2312_);
    v___f_2314_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2314_, 0, v_e_2308_);
    lean_closure_set(v___f_2314_, 1, v_newPos_2313_);
    v___x_2315_ = lean_apply_3(v_inst_2309_, lean_box(0), v___f_2314_, v_x_2310_);
    return v___x_2315_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed(
    mut v_e_2316_: *mut LeanObject,
    mut v_inst_2317_: *mut LeanObject,
    mut v_x_2318_: *mut LeanObject,
    mut v_____do__lift_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2320_: *mut LeanObject = core::ptr::null_mut();
    v_res_2320_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1(
        v_e_2316_,
        v_inst_2317_,
        v_x_2318_,
        v_____do__lift_2319_,
    );
    lean_dec(v_____do__lift_2319_);
    return v_res_2320_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2(
    mut v_inst_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
    mut v_inst_2323_: *mut LeanObject,
    mut v_inst_2324_: *mut LeanObject,
    mut v_toBind_2325_: *mut LeanObject,
    mut v_e_2326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut LeanObject = core::ptr::null_mut();
    v___f_2327_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2327_, 0, v_e_2326_);
    lean_closure_set(v___f_2327_, 1, v_inst_2321_);
    lean_closure_set(v___f_2327_, 2, v_x_2322_);
    v___x_2328_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_2323_, v_inst_2324_);
    v___x_2329_ = lean_apply_4(
        v_toBind_2325_,
        lean_box(0),
        lean_box(0),
        v___x_2328_,
        v___f_2327_,
    );
    return v___x_2329_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(
    mut v_inst_2330_: *mut LeanObject,
    mut v_inst_2331_: *mut LeanObject,
    mut v_inst_2332_: *mut LeanObject,
    mut v_x_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2334_ = lean_ctor_get(v_inst_2330_, 1);
    lean_inc_n(v_toBind_2334_, 2);
    lean_inc(v_inst_2331_);
    lean_inc_ref(v_inst_2330_);
    v___f_2335_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg___lam__2
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2335_, 0, v_inst_2332_);
    lean_closure_set(v___f_2335_, 1, v_x_2333_);
    lean_closure_set(v___f_2335_, 2, v_inst_2330_);
    lean_closure_set(v___f_2335_, 3, v_inst_2331_);
    lean_closure_set(v___f_2335_, 4, v_toBind_2334_);
    v___x_2336_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2330_, v_inst_2331_);
    v___x_2337_ = lean_apply_4(
        v_toBind_2334_,
        lean_box(0),
        lean_box(0),
        v___x_2336_,
        v___f_2335_,
    );
    return v___x_2337_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn(
    mut v_00_u03b1_2338_: *mut LeanObject,
    mut v_m_2339_: *mut LeanObject,
    mut v_inst_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_inst_2342_: *mut LeanObject,
    mut v_x_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2344_: *mut LeanObject = core::ptr::null_mut();
    v___x_2344_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryFn___redArg(
        v_inst_2340_,
        v_inst_2341_,
        v_inst_2342_,
        v_x_2343_,
    );
    return v___x_2344_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(
    mut v___x_2345_: *mut LeanObject,
    mut v_args_2346_: *mut LeanObject,
    mut v_argIdx_2347_: *mut LeanObject,
    mut v_newPos_2348_: *mut LeanObject,
    mut v_cfg_2349_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350_ = lean_array_get_borrowed(v___x_2345_, v_args_2346_, v_argIdx_2347_);
    lean_inc(v___x_2350_);
    v___x_2351_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2351_, 0, v___x_2350_);
    lean_ctor_set(v___x_2351_, 1, v_newPos_2348_);
    return v___x_2351_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed(
    mut v___x_2352_: *mut LeanObject,
    mut v_args_2353_: *mut LeanObject,
    mut v_argIdx_2354_: *mut LeanObject,
    mut v_newPos_2355_: *mut LeanObject,
    mut v_cfg_2356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2357_: *mut LeanObject = core::ptr::null_mut();
    v_res_2357_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0(
        v___x_2352_,
        v_args_2353_,
        v_argIdx_2354_,
        v_newPos_2355_,
        v_cfg_2356_,
    );
    lean_dec_ref(v_cfg_2356_);
    lean_dec(v_argIdx_2354_);
    lean_dec_ref(v_args_2353_);
    lean_dec_ref(v___x_2352_);
    return v_res_2357_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(
    mut v_args_2358_: *mut LeanObject,
    mut v_argIdx_2359_: *mut LeanObject,
    mut v___x_2360_: *mut LeanObject,
    mut v_inst_2361_: *mut LeanObject,
    mut v_x_2362_: *mut LeanObject,
    mut v_____do__lift_2363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newPos_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut LeanObject = core::ptr::null_mut();
    v___x_2364_ = lean_array_get_size(v_args_2358_);
    v_newPos_2365_ =
        l_Lean_SubExpr_Pos_pushNaryArg(v___x_2364_, v_argIdx_2359_, v_____do__lift_2363_);
    v___f_2366_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2366_, 0, v___x_2360_);
    lean_closure_set(v___f_2366_, 1, v_args_2358_);
    lean_closure_set(v___f_2366_, 2, v_argIdx_2359_);
    lean_closure_set(v___f_2366_, 3, v_newPos_2365_);
    v___x_2367_ = lean_apply_3(v_inst_2361_, lean_box(0), v___f_2366_, v_x_2362_);
    return v___x_2367_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed(
    mut v_args_2368_: *mut LeanObject,
    mut v_argIdx_2369_: *mut LeanObject,
    mut v___x_2370_: *mut LeanObject,
    mut v_inst_2371_: *mut LeanObject,
    mut v_x_2372_: *mut LeanObject,
    mut v_____do__lift_2373_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_res_2374_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1(
        v_args_2368_,
        v_argIdx_2369_,
        v___x_2370_,
        v_inst_2371_,
        v_x_2372_,
        v_____do__lift_2373_,
    );
    lean_dec(v_____do__lift_2373_);
    return v_res_2374_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0()
-> *mut LeanObject {
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_2376_: *mut LeanObject = core::ptr::null_mut();
    v___x_2375_ = lean_box(0);
    v_dummy_2376_ = l_Lean_Expr_sort___override(v___x_2375_);
    return v_dummy_2376_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2(
    mut v_argIdx_2377_: *mut LeanObject,
    mut v___x_2378_: *mut LeanObject,
    mut v_inst_2379_: *mut LeanObject,
    mut v_x_2380_: *mut LeanObject,
    mut v_inst_2381_: *mut LeanObject,
    mut v_inst_2382_: *mut LeanObject,
    mut v_toBind_2383_: *mut LeanObject,
    mut v_e_2384_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dummy_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    v_dummy_2385_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0_once
        ),
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2___closed__0,
    );
    v_nargs_2386_ = l_Lean_Expr_getAppNumArgs(v_e_2384_);
    lean_inc(v_nargs_2386_);
    v___x_2387_ = lean_mk_array(v_nargs_2386_, v_dummy_2385_);
    v___x_2388_ = lean_unsigned_to_nat(1);
    v___x_2389_ = lean_nat_sub(v_nargs_2386_, v___x_2388_);
    lean_dec(v_nargs_2386_);
    v_args_2390_ =
        l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_e_2384_, v___x_2387_, v___x_2389_);
    v___f_2391_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__1___boxed
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_2391_, 0, v_args_2390_);
    lean_closure_set(v___f_2391_, 1, v_argIdx_2377_);
    lean_closure_set(v___f_2391_, 2, v___x_2378_);
    lean_closure_set(v___f_2391_, 3, v_inst_2379_);
    lean_closure_set(v___f_2391_, 4, v_x_2380_);
    v___x_2392_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getPos___redArg(v_inst_2381_, v_inst_2382_);
    v___x_2393_ = lean_apply_4(
        v_toBind_2383_,
        lean_box(0),
        lean_box(0),
        v___x_2392_,
        v___f_2391_,
    );
    return v___x_2393_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg(
    mut v_inst_2394_: *mut LeanObject,
    mut v_inst_2395_: *mut LeanObject,
    mut v_inst_2396_: *mut LeanObject,
    mut v_argIdx_2397_: *mut LeanObject,
    mut v_x_2398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toBind_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    v_toBind_2399_ = lean_ctor_get(v_inst_2394_, 1);
    lean_inc_n(v_toBind_2399_, 2);
    v___x_2400_ = l_Lean_instInhabitedExpr;
    lean_inc(v_inst_2395_);
    lean_inc_ref(v_inst_2394_);
    v___f_2401_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg___redArg___lam__2
            as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_2401_, 0, v_argIdx_2397_);
    lean_closure_set(v___f_2401_, 1, v___x_2400_);
    lean_closure_set(v___f_2401_, 2, v_inst_2396_);
    lean_closure_set(v___f_2401_, 3, v_x_2398_);
    lean_closure_set(v___f_2401_, 4, v_inst_2394_);
    lean_closure_set(v___f_2401_, 5, v_inst_2395_);
    lean_closure_set(v___f_2401_, 6, v_toBind_2399_);
    v___x_2402_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_getExpr___redArg(v_inst_2394_, v_inst_2395_);
    v___x_2403_ = lean_apply_4(
        v_toBind_2399_,
        lean_box(0),
        lean_box(0),
        v___x_2402_,
        v___f_2401_,
    );
    return v___x_2403_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_withNaryArg(
    mut v_00_u03b1_2404_: *mut LeanObject,
    mut v_m_2405_: *mut LeanObject,
    mut v_inst_2406_: *mut LeanObject,
    mut v_inst_2407_: *mut LeanObject,
    mut v_inst_2408_: *mut LeanObject,
    mut v_argIdx_2409_: *mut LeanObject,
    mut v_x_2410_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2411_: *mut LeanObject = core::ptr::null_mut();
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
-> *mut LeanObject {
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut LeanObject = core::ptr::null_mut();
    v___x_2412_ = l_Lean_SubExpr_Pos_maxChildren;
    v___x_2413_ = lean_unsigned_to_nat(2);
    v___x_2414_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2414_, 0, v___x_2413_);
    lean_ctor_set(v___x_2414_, 1, v___x_2412_);
    return v___x_2414_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default()
-> *mut LeanObject {
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    v___x_2415_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0), core::ptr::addr_of_mut!(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0_once), _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default___closed__0);
    return v___x_2415_;
}
pub unsafe fn _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator()
-> *mut LeanObject {
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    v___x_2416_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default;
    return v___x_2416_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(
    mut v_iter_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_curr_2418_: *mut LeanObject = core::ptr::null_mut();
    v_curr_2418_ = lean_ctor_get(v_iter_2417_, 0);
    lean_inc(v_curr_2418_);
    return v_curr_2418_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos___boxed(
    mut v_iter_2419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2420_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_toPos(v_iter_2419_);
    lean_dec_ref(v_iter_2419_);
    return v_res_2420_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(
    mut v_iter_2421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_curr_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v_top_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2426_: u8 = 0;
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: u8 = 0;
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2440_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_curr_2422_ = lean_ctor_get(v_iter_2421_, 0);
                v_top_2423_ = lean_ctor_get(v_iter_2421_, 1);
                v_isSharedCheck_2440_ = (!lean_is_exclusive(v_iter_2421_)) as u8;
                if v_isSharedCheck_2440_ == 0 {
                    v___x_2425_ = v_iter_2421_;
                    v_isShared_2426_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_top_2423_);
                    lean_inc(v_curr_2422_);
                    lean_dec(v_iter_2421_);
                    v___x_2425_ = lean_box(0);
                    v_isShared_2426_ = v_isSharedCheck_2440_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2427_ = lean_unsigned_to_nat(1);
                v___x_2428_ = lean_nat_add(v_curr_2422_, v___x_2427_);
                lean_dec(v_curr_2422_);
                v___x_2429_ = lean_nat_dec_eq(v___x_2428_, v_top_2423_);
                if v___x_2429_ == 0 {
                    if v_isShared_2426_ == 0 {
                        lean_ctor_set(v___x_2425_, 0, v___x_2428_);
                        v___x_2431_ = v___x_2425_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2428_);
                        lean_ctor_set(v_reuseFailAlloc_2432_, 1, v_top_2423_);
                        v___x_2431_ = v_reuseFailAlloc_2432_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2428_);
                    v___x_2433_ = lean_unsigned_to_nat(2);
                    v___x_2434_ = lean_nat_mul(v___x_2433_, v_top_2423_);
                    v___x_2435_ = l_Lean_SubExpr_Pos_maxChildren;
                    v___x_2436_ = lean_nat_mul(v___x_2435_, v_top_2423_);
                    lean_dec(v_top_2423_);
                    if v_isShared_2426_ == 0 {
                        lean_ctor_set(v___x_2425_, 1, v___x_2436_);
                        lean_ctor_set(v___x_2425_, 0, v___x_2434_);
                        v___x_2438_ = v___x_2425_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2439_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2439_, 0, v___x_2434_);
                        lean_ctor_set(v_reuseFailAlloc_2439_, 1, v___x_2436_);
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
    mut v_s_2441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    v___x_2442_ = lean_box(0);
    v___x_2443_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_HoleIterator_next(v_s_2441_);
    v___x_2444_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2444_, 0, v___x_2442_);
    lean_ctor_set(v___x_2444_, 1, v___x_2443_);
    return v___x_2444_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1(
    mut v_toPure_2445_: *mut LeanObject,
    mut v_curr_2446_: *mut LeanObject,
    mut v_____r_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    v___x_2448_ = lean_apply_2(v_toPure_2445_, lean_box(0), v_curr_2446_);
    return v___x_2448_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2(
    mut v_toPure_2449_: *mut LeanObject,
    mut v_modifyGet_2450_: *mut LeanObject,
    mut v___f_2451_: *mut LeanObject,
    mut v_toBind_2452_: *mut LeanObject,
    mut v_iter_2453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_curr_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    v_curr_2454_ = lean_ctor_get(v_iter_2453_, 0);
    lean_inc(v_curr_2454_);
    lean_dec_ref(v_iter_2453_);
    v___f_2455_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__1
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2455_, 0, v_toPure_2449_);
    lean_closure_set(v___f_2455_, 1, v_curr_2454_);
    v___x_2456_ = lean_apply_2(v_modifyGet_2450_, lean_box(0), v___f_2451_);
    v___x_2457_ = lean_apply_4(
        v_toBind_2452_,
        lean_box(0),
        lean_box(0),
        v___x_2456_,
        v___f_2455_,
    );
    return v___x_2457_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(
    mut v_inst_2459_: *mut LeanObject,
    mut v_inst_2460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_get_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_modifyGet_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2461_ = lean_ctor_get(v_inst_2459_, 0);
    lean_inc_ref(v_toApplicative_2461_);
    v_toBind_2462_ = lean_ctor_get(v_inst_2459_, 1);
    lean_inc_n(v_toBind_2462_, 2);
    lean_dec_ref(v_inst_2459_);
    v_get_2463_ = lean_ctor_get(v_inst_2460_, 0);
    lean_inc(v_get_2463_);
    v_modifyGet_2464_ = lean_ctor_get(v_inst_2460_, 2);
    lean_inc(v_modifyGet_2464_);
    lean_dec_ref(v_inst_2460_);
    v_toPure_2465_ = lean_ctor_get(v_toApplicative_2461_, 1);
    lean_inc(v_toPure_2465_);
    lean_dec_ref(v_toApplicative_2461_);
    v___f_2466_ = l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___closed__0;
    v___f_2467_ = lean_alloc_closure(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg___lam__2
            as *mut core::ffi::c_void,
        5,
        4,
    );
    lean_closure_set(v___f_2467_, 0, v_toPure_2465_);
    lean_closure_set(v___f_2467_, 1, v_modifyGet_2464_);
    lean_closure_set(v___f_2467_, 2, v___f_2466_);
    lean_closure_set(v___f_2467_, 3, v_toBind_2462_);
    v___x_2468_ = lean_apply_4(
        v_toBind_2462_,
        lean_box(0),
        lean_box(0),
        v_get_2463_,
        v___f_2467_,
    );
    return v___x_2468_;
}
pub unsafe fn l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos(
    mut v_m_2469_: *mut LeanObject,
    mut v_inst_2470_: *mut LeanObject,
    mut v_inst_2471_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    v___x_2472_ =
        l_Lean_PrettyPrinter_Delaborator_SubExpr_nextExtraPos___redArg(v_inst_2470_, v_inst_2471_);
    return v___x_2472_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default =
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default();
    lean_mark_persistent(
        l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator_default,
    );
    l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator =
        _init_l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator();
    lean_mark_persistent(l_Lean_PrettyPrinter_Delaborator_SubExpr_instInhabitedHoleIterator);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_PrettyPrinter_Delaborator_SubExpr(builtin);
}

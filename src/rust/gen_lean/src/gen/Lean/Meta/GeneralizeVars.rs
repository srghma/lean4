// Lean compiler output
// Module: Lean.Meta.GeneralizeVars
// Imports: Lean.Meta.Basic Lean.Util.CollectFVars
use crate::ffi::{
    lean_array_get_size, lean_array_push, lean_array_size, lean_array_to_list,
    lean_array_uget_borrowed, lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l_Lean_BinderInfo_isInstImplicit, l_Lean_Expr_fvarId_x21, l_Lean_Expr_hasFVar,
    l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar, l_Lean_FVarIdSet_insert,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_binderInfo, l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl,
    l_Lean_LocalDecl_isLet, l_Lean_LocalDecl_type, l_Lean_LocalDecl_value_x3f,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_FVarId_getDecl___redArg, l_Lean_Meta_sortFVarIds___redArg,
    runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::MetavarContext::{
    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(
    mut v_e_1478_: *mut crate::leanh::LeanObject,
    mut v___y_1479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1481_: u8 = 0;
    let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1501_: u8 = 0;
    let mut v_unused_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1481_ = l_Lean_Expr_hasMVar(v_e_1478_);
                if v___x_1481_ == 0 {
                    v___x_1482_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1482_, 0, v_e_1478_);
                    return v___x_1482_;
                } else {
                    v___x_1483_ = lean_st_ref_get(v___y_1479_);
                    v_mctx_1484_ = crate::leanh::lean_ctor_get(v___x_1483_, 0);
                    crate::leanh::lean_inc_ref(v_mctx_1484_);
                    crate::leanh::lean_dec(v___x_1483_);
                    v___x_1485_ = l_Lean_instantiateMVarsCore(v_mctx_1484_, v_e_1478_);
                    v_fst_1486_ = crate::leanh::lean_ctor_get(v___x_1485_, 0);
                    crate::leanh::lean_inc(v_fst_1486_);
                    v_snd_1487_ = crate::leanh::lean_ctor_get(v___x_1485_, 1);
                    crate::leanh::lean_inc(v_snd_1487_);
                    crate::leanh::lean_dec_ref(v___x_1485_);
                    v___x_1488_ = lean_st_ref_take(v___y_1479_);
                    v_cache_1489_ = crate::leanh::lean_ctor_get(v___x_1488_, 1);
                    v_zetaDeltaFVarIds_1490_ = crate::leanh::lean_ctor_get(v___x_1488_, 2);
                    v_postponed_1491_ = crate::leanh::lean_ctor_get(v___x_1488_, 3);
                    v_diag_1492_ = crate::leanh::lean_ctor_get(v___x_1488_, 4);
                    v_isSharedCheck_1501_ = (!crate::leanh::lean_is_exclusive(v___x_1488_)) as u8;
                    if v_isSharedCheck_1501_ == 0 {
                        v_unused_1502_ = crate::leanh::lean_ctor_get(v___x_1488_, 0);
                        crate::leanh::lean_dec(v_unused_1502_);
                        v___x_1494_ = v___x_1488_;
                        v_isShared_1495_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_diag_1492_);
                        crate::leanh::lean_inc(v_postponed_1491_);
                        crate::leanh::lean_inc(v_zetaDeltaFVarIds_1490_);
                        crate::leanh::lean_inc(v_cache_1489_);
                        crate::leanh::lean_dec(v___x_1488_);
                        v___x_1494_ = crate::leanh::lean_box(0);
                        v_isShared_1495_ = v_isSharedCheck_1501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1494_, 0, v_snd_1487_);
                    v___x_1497_ = v___x_1494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1500_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 0, v_snd_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 1, v_cache_1489_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1500_,
                        2,
                        v_zetaDeltaFVarIds_1490_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 3, v_postponed_1491_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1500_, 4, v_diag_1492_);
                    v___x_1497_ = v_reuseFailAlloc_1500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1498_ = lean_st_ref_set(v___y_1479_, v___x_1497_);
                v___x_1499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1499_, 0, v_fst_1486_);
                return v___x_1499_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg___boxed(
    mut v_e_1503_: *mut crate::leanh::LeanObject,
    mut v___y_1504_: *mut crate::leanh::LeanObject,
    mut v___y_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_1503_, v___y_1504_);
    crate::leanh::lean_dec(v___y_1504_);
    return v_res_1506_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(
    mut v_e_1507_: *mut crate::leanh::LeanObject,
    mut v___y_1508_: *mut crate::leanh::LeanObject,
    mut v___y_1509_: *mut crate::leanh::LeanObject,
    mut v___y_1510_: *mut crate::leanh::LeanObject,
    mut v___y_1511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1513_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_e_1507_, v___y_1509_);
    return v___x_1513_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___boxed(
    mut v_e_1514_: *mut crate::leanh::LeanObject,
    mut v___y_1515_: *mut crate::leanh::LeanObject,
    mut v___y_1516_: *mut crate::leanh::LeanObject,
    mut v___y_1517_: *mut crate::leanh::LeanObject,
    mut v___y_1518_: *mut crate::leanh::LeanObject,
    mut v___y_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1520_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2(v_e_1514_, v___y_1515_, v___y_1516_, v___y_1517_, v___y_1518_);
    crate::leanh::lean_dec(v___y_1518_);
    crate::leanh::lean_dec_ref(v___y_1517_);
    crate::leanh::lean_dec(v___y_1516_);
    crate::leanh::lean_dec_ref(v___y_1515_);
    return v_res_1520_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(
    mut v_k_1521_: *mut crate::leanh::LeanObject,
    mut v_t_1522_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: u8 = 0;
    let mut v___x_1528_: u8 = 0;
    let mut v___x_1530_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_1522_) == 0 {
                    v_k_1523_ = crate::leanh::lean_ctor_get(v_t_1522_, 1);
                    v_l_1524_ = crate::leanh::lean_ctor_get(v_t_1522_, 3);
                    v_r_1525_ = crate::leanh::lean_ctor_get(v_t_1522_, 4);
                    v___x_1526_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_1521_, v_k_1523_);
                    match v___x_1526_ {
                        0 => {
                            v_t_1522_ = v_l_1524_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_1528_ = 1;
                            return v___x_1528_;
                        }
                        _ => {
                            v_t_1522_ = v_r_1525_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_1530_ = 0;
                    return v___x_1530_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg___boxed(
    mut v_k_1531_: *mut crate::leanh::LeanObject,
    mut v_t_1532_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1533_: u8 = 0;
    let mut v_r_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1533_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_1531_, v_t_1532_);
    crate::leanh::lean_dec(v_t_1532_);
    crate::leanh::lean_dec(v_k_1531_);
    v_r_1534_ = crate::leanh::lean_box((v_res_1533_) as usize);
    return v_r_1534_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(
    mut v_init_1535_: *mut crate::leanh::LeanObject,
    mut v_x_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_1539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1548_: u8 = 0;
    let mut v___x_1549_: u8 = 0;
    let mut v___x_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1560_: u8 = 0;
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1536_) == 0 {
                    v_k_1538_ = crate::leanh::lean_ctor_get(v_x_1536_, 1);
                    crate::leanh::lean_inc(v_k_1538_);
                    v_l_1539_ = crate::leanh::lean_ctor_get(v_x_1536_, 3);
                    crate::leanh::lean_inc(v_l_1539_);
                    v_r_1540_ = crate::leanh::lean_ctor_get(v_x_1536_, 4);
                    crate::leanh::lean_inc(v_r_1540_);
                    crate::leanh::lean_dec_ref_known(v_x_1536_, 5);
                    v___x_1541_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_1535_, v_l_1539_);
                    v_a_1542_ = crate::leanh::lean_ctor_get(v___x_1541_, 0);
                    crate::leanh::lean_inc(v_a_1542_);
                    crate::leanh::lean_dec_ref(v___x_1541_);
                    v_a_1543_ = crate::leanh::lean_ctor_get(v_a_1542_, 0);
                    crate::leanh::lean_inc(v_a_1543_);
                    crate::leanh::lean_dec(v_a_1542_);
                    v_fst_1544_ = crate::leanh::lean_ctor_get(v_a_1543_, 0);
                    v_snd_1545_ = crate::leanh::lean_ctor_get(v_a_1543_, 1);
                    v_isSharedCheck_1560_ = (!crate::leanh::lean_is_exclusive(v_a_1543_)) as u8;
                    if v_isSharedCheck_1560_ == 0 {
                        v___x_1547_ = v_a_1543_;
                        v_isShared_1548_ = v_isSharedCheck_1560_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1545_);
                        crate::leanh::lean_inc(v_fst_1544_);
                        crate::leanh::lean_dec(v_a_1543_);
                        v___x_1547_ = crate::leanh::lean_box(0);
                        v_isShared_1548_ = v_isSharedCheck_1560_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1561_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1561_, 0, v_init_1535_);
                    v___x_1562_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1562_, 0, v___x_1561_);
                    return v___x_1562_;
                }
            }
            1 => {
                v___x_1549_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_1538_, v_snd_1545_);
                if v___x_1549_ == 0 {
                    crate::leanh::lean_inc(v_k_1538_);
                    v___x_1550_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1550_, 0, v_k_1538_);
                    crate::leanh::lean_ctor_set(v___x_1550_, 1, v_fst_1544_);
                    v___x_1551_ = l_Lean_FVarIdSet_insert(v_snd_1545_, v_k_1538_);
                    if v_isShared_1548_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1547_, 1, v___x_1551_);
                        crate::leanh::lean_ctor_set(v___x_1547_, 0, v___x_1550_);
                        v___x_1553_ = v___x_1547_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1555_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1550_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1551_);
                        v___x_1553_ = v_reuseFailAlloc_1555_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_k_1538_);
                    if v_isShared_1548_ == 0 {
                        v___x_1557_ = v___x_1547_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1559_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_fst_1544_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1559_, 1, v_snd_1545_);
                        v___x_1557_ = v_reuseFailAlloc_1559_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v_init_1535_ = v___x_1553_;
                v_x_1536_ = v_r_1540_;
                state = 0;
                continue;
            }
            3 => {
                v_init_1535_ = v___x_1557_;
                v_x_1536_ = v_r_1540_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg___boxed(
    mut v_init_1563_: *mut crate::leanh::LeanObject,
    mut v_x_1564_: *mut crate::leanh::LeanObject,
    mut v___y_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1566_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_1563_, v_x_1564_);
    return v_res_1566_;
}
pub unsafe fn _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1567_ = crate::leanh::lean_box(0);
    v___x_1568_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1569_ = lean_mk_array(v___x_1568_, v___x_1567_);
    return v___x_1569_;
}
pub unsafe fn _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1570_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__0);
    v___x_1571_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1572_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1572_, 0, v___x_1571_);
    crate::leanh::lean_ctor_set(v___x_1572_, 1, v___x_1570_);
    return v___x_1572_;
}
pub unsafe fn _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
    v___x_1576_ = crate::leanh::lean_box(1);
    v___x_1577_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
    v___x_1578_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1578_, 0, v___x_1577_);
    crate::leanh::lean_ctor_set(v___x_1578_, 1, v___x_1576_);
    crate::leanh::lean_ctor_set(v___x_1578_, 2, v___x_1575_);
    return v___x_1578_;
}
pub unsafe fn l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(
    mut v_fvarId_1579_: *mut crate::leanh::LeanObject,
    mut v_todo_1580_: *mut crate::leanh::LeanObject,
    mut v_s_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_s_x27_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: u8 = 0;
    let mut v___x_1618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1626_: u8 = 0;
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1630_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1610_ =
                    l_Lean_FVarId_getDecl___redArg(v_fvarId_1579_, v_a_1582_, v_a_1584_, v_a_1585_);
                if crate::leanh::lean_obj_tag(v___x_1610_) == 0 {
                    v_a_1611_ = crate::leanh::lean_ctor_get(v___x_1610_, 0);
                    crate::leanh::lean_inc(v_a_1611_);
                    crate::leanh::lean_dec_ref_known(v___x_1610_, 1);
                    v___x_1612_ = l_Lean_LocalDecl_type(v_a_1611_);
                    v___x_1613_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v___x_1612_, v_a_1583_);
                    v_a_1614_ = crate::leanh::lean_ctor_get(v___x_1613_, 0);
                    crate::leanh::lean_inc(v_a_1614_);
                    crate::leanh::lean_dec_ref(v___x_1613_);
                    v___x_1615_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__3);
                    v___x_1616_ = l_Lean_collectFVars(v___x_1615_, v_a_1614_);
                    v___x_1617_ = 0;
                    v___x_1618_ = l_Lean_LocalDecl_value_x3f(v_a_1611_, v___x_1617_);
                    crate::leanh::lean_dec(v_a_1611_);
                    if crate::leanh::lean_obj_tag(v___x_1618_) == 1 {
                        v_val_1619_ = crate::leanh::lean_ctor_get(v___x_1618_, 0);
                        crate::leanh::lean_inc(v_val_1619_);
                        crate::leanh::lean_dec_ref_known(v___x_1618_, 1);
                        v___x_1620_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_val_1619_, v_a_1583_);
                        v_a_1621_ = crate::leanh::lean_ctor_get(v___x_1620_, 0);
                        crate::leanh::lean_inc(v_a_1621_);
                        crate::leanh::lean_dec_ref(v___x_1620_);
                        v___x_1622_ = l_Lean_collectFVars(v___x_1616_, v_a_1621_);
                        v_s_x27_1600_ = v___x_1622_;
                        v___y_1601_ = v_a_1582_;
                        v___y_1602_ = v_a_1583_;
                        v___y_1603_ = v_a_1584_;
                        v___y_1604_ = v_a_1585_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1618_);
                        v_s_x27_1600_ = v___x_1616_;
                        v___y_1601_ = v_a_1582_;
                        v___y_1602_ = v_a_1583_;
                        v___y_1603_ = v_a_1584_;
                        v___y_1604_ = v_a_1585_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_s_1581_);
                    crate::leanh::lean_dec(v_todo_1580_);
                    v_a_1623_ = crate::leanh::lean_ctor_get(v___x_1610_, 0);
                    v_isSharedCheck_1630_ = (!crate::leanh::lean_is_exclusive(v___x_1610_)) as u8;
                    if v_isSharedCheck_1630_ == 0 {
                        v___x_1625_ = v___x_1610_;
                        v_isShared_1626_ = v_isSharedCheck_1630_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1623_);
                        crate::leanh::lean_dec(v___x_1610_);
                        v___x_1625_ = crate::leanh::lean_box(0);
                        v_isShared_1626_ = v_isSharedCheck_1630_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_1589_ = crate::leanh::lean_ctor_get(v_a_1588_, 0);
                v_snd_1590_ = crate::leanh::lean_ctor_get(v_a_1588_, 1);
                v_isSharedCheck_1598_ = (!crate::leanh::lean_is_exclusive(v_a_1588_)) as u8;
                if v_isSharedCheck_1598_ == 0 {
                    v___x_1592_ = v_a_1588_;
                    v_isShared_1593_ = v_isSharedCheck_1598_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_1590_);
                    crate::leanh::lean_inc(v_fst_1589_);
                    crate::leanh::lean_dec(v_a_1588_);
                    v___x_1592_ = crate::leanh::lean_box(0);
                    v_isShared_1593_ = v_isSharedCheck_1598_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1593_ == 0 {
                    v___x_1595_ = v___x_1592_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_fst_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 1, v_snd_1590_);
                    v___x_1595_ = v_reuseFailAlloc_1597_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1596_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1596_, 0, v___x_1595_);
                return v___x_1596_;
            }
            4 => {
                v_fvarSet_1605_ = crate::leanh::lean_ctor_get(v_s_x27_1600_, 1);
                crate::leanh::lean_inc(v_fvarSet_1605_);
                crate::leanh::lean_dec_ref(v_s_x27_1600_);
                v___x_1606_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1606_, 0, v_todo_1580_);
                crate::leanh::lean_ctor_set(v___x_1606_, 1, v_s_1581_);
                v___x_1607_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v___x_1606_, v_fvarSet_1605_);
                v_a_1608_ = crate::leanh::lean_ctor_get(v___x_1607_, 0);
                crate::leanh::lean_inc(v_a_1608_);
                crate::leanh::lean_dec_ref(v___x_1607_);
                v_a_1609_ = crate::leanh::lean_ctor_get(v_a_1608_, 0);
                crate::leanh::lean_inc(v_a_1609_);
                crate::leanh::lean_dec(v_a_1608_);
                v_a_1588_ = v_a_1609_;
                state = 1;
                continue;
            }
            5 => {
                if v_isShared_1626_ == 0 {
                    v___x_1628_ = v___x_1625_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_a_1623_);
                    v___x_1628_ = v_reuseFailAlloc_1629_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1628_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___boxed(
    mut v_fvarId_1631_: *mut crate::leanh::LeanObject,
    mut v_todo_1632_: *mut crate::leanh::LeanObject,
    mut v_s_1633_: *mut crate::leanh::LeanObject,
    mut v_a_1634_: *mut crate::leanh::LeanObject,
    mut v_a_1635_: *mut crate::leanh::LeanObject,
    mut v_a_1636_: *mut crate::leanh::LeanObject,
    mut v_a_1637_: *mut crate::leanh::LeanObject,
    mut v_a_1638_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1639_ =
        l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(
            v_fvarId_1631_,
            v_todo_1632_,
            v_s_1633_,
            v_a_1634_,
            v_a_1635_,
            v_a_1636_,
            v_a_1637_,
        );
    crate::leanh::lean_dec(v_a_1637_);
    crate::leanh::lean_dec_ref(v_a_1636_);
    crate::leanh::lean_dec(v_a_1635_);
    crate::leanh::lean_dec_ref(v_a_1634_);
    return v_res_1639_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(
    mut v_00_u03b2_1640_: *mut crate::leanh::LeanObject,
    mut v_k_1641_: *mut crate::leanh::LeanObject,
    mut v_t_1642_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1643_: u8 = 0;
    v___x_1643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_k_1641_, v_t_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___boxed(
    mut v_00_u03b2_1644_: *mut crate::leanh::LeanObject,
    mut v_k_1645_: *mut crate::leanh::LeanObject,
    mut v_t_1646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1647_: u8 = 0;
    let mut v_r_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0(v_00_u03b2_1644_, v_k_1645_, v_t_1646_);
    crate::leanh::lean_dec(v_t_1646_);
    crate::leanh::lean_dec(v_k_1645_);
    v_r_1648_ = crate::leanh::lean_box((v_res_1647_) as usize);
    return v_r_1648_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(
    mut v_init_1649_: *mut crate::leanh::LeanObject,
    mut v_x_1650_: *mut crate::leanh::LeanObject,
    mut v___y_1651_: *mut crate::leanh::LeanObject,
    mut v___y_1652_: *mut crate::leanh::LeanObject,
    mut v___y_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1656_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___redArg(v_init_1649_, v_x_1650_);
    return v___x_1656_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1___boxed(
    mut v_init_1657_: *mut crate::leanh::LeanObject,
    mut v_x_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__1(v_init_1657_, v_x_1658_, v___y_1659_, v___y_1660_, v___y_1661_, v___y_1662_);
    crate::leanh::lean_dec(v___y_1662_);
    crate::leanh::lean_dec_ref(v___y_1661_);
    crate::leanh::lean_dec(v___y_1660_);
    crate::leanh::lean_dec_ref(v___y_1659_);
    return v_res_1664_;
}
pub unsafe fn l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(
    mut v_todo_1665_: *mut crate::leanh::LeanObject,
    mut v_s_1666_: *mut crate::leanh::LeanObject,
    mut v_a_1667_: *mut crate::leanh::LeanObject,
    mut v_a_1668_: *mut crate::leanh::LeanObject,
    mut v_a_1669_: *mut crate::leanh::LeanObject,
    mut v_a_1670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1685_: u8 = 0;
    let mut v___x_1687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1689_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_todo_1665_) == 0 {
                    v___x_1672_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1672_, 0, v_s_1666_);
                    return v___x_1672_;
                } else {
                    v_head_1673_ = crate::leanh::lean_ctor_get(v_todo_1665_, 0);
                    crate::leanh::lean_inc(v_head_1673_);
                    v_tail_1674_ = crate::leanh::lean_ctor_get(v_todo_1665_, 1);
                    crate::leanh::lean_inc(v_tail_1674_);
                    crate::leanh::lean_dec_ref_known(v_todo_1665_, 2);
                    v___x_1675_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_head_1673_, v_s_1666_);
                    if v___x_1675_ == 0 {
                        crate::leanh::lean_inc(v_head_1673_);
                        v___x_1676_ = l_Lean_FVarIdSet_insert(v_s_1666_, v_head_1673_);
                        v___x_1677_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit(v_head_1673_, v_tail_1674_, v___x_1676_, v_a_1667_, v_a_1668_, v_a_1669_, v_a_1670_);
                        if crate::leanh::lean_obj_tag(v___x_1677_) == 0 {
                            v_a_1678_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                            crate::leanh::lean_inc(v_a_1678_);
                            crate::leanh::lean_dec_ref_known(v___x_1677_, 1);
                            v_fst_1679_ = crate::leanh::lean_ctor_get(v_a_1678_, 0);
                            crate::leanh::lean_inc(v_fst_1679_);
                            v_snd_1680_ = crate::leanh::lean_ctor_get(v_a_1678_, 1);
                            crate::leanh::lean_inc(v_snd_1680_);
                            crate::leanh::lean_dec(v_a_1678_);
                            v_todo_1665_ = v_fst_1679_;
                            v_s_1666_ = v_snd_1680_;
                            state = 0;
                            continue;
                        } else {
                            v_a_1682_ = crate::leanh::lean_ctor_get(v___x_1677_, 0);
                            v_isSharedCheck_1689_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1677_)) as u8;
                            if v_isSharedCheck_1689_ == 0 {
                                v___x_1684_ = v___x_1677_;
                                v_isShared_1685_ = v_isSharedCheck_1689_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1682_);
                                crate::leanh::lean_dec(v___x_1677_);
                                v___x_1684_ = crate::leanh::lean_box(0);
                                v_isShared_1685_ = v_isSharedCheck_1689_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_head_1673_);
                        v_todo_1665_ = v_tail_1674_;
                        state = 0;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1685_ == 0 {
                    v___x_1687_ = v___x_1684_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1688_, 0, v_a_1682_);
                    v___x_1687_ = v_reuseFailAlloc_1688_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1687_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop___boxed(
    mut v_todo_1691_: *mut crate::leanh::LeanObject,
    mut v_s_1692_: *mut crate::leanh::LeanObject,
    mut v_a_1693_: *mut crate::leanh::LeanObject,
    mut v_a_1694_: *mut crate::leanh::LeanObject,
    mut v_a_1695_: *mut crate::leanh::LeanObject,
    mut v_a_1696_: *mut crate::leanh::LeanObject,
    mut v_a_1697_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1698_ =
        l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(
            v_todo_1691_,
            v_s_1692_,
            v_a_1693_,
            v_a_1694_,
            v_a_1695_,
            v_a_1696_,
        );
    crate::leanh::lean_dec(v_a_1696_);
    crate::leanh::lean_dec_ref(v_a_1695_);
    crate::leanh::lean_dec(v_a_1694_);
    crate::leanh::lean_dec_ref(v_a_1693_);
    return v_res_1698_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(
    mut v_as_1699_: *mut crate::leanh::LeanObject,
    mut v_sz_1700_: usize,
    mut v_i_1701_: usize,
    mut v_b_1702_: *mut crate::leanh::LeanObject,
    mut v___y_1703_: *mut crate::leanh::LeanObject,
    mut v___y_1704_: *mut crate::leanh::LeanObject,
    mut v___y_1705_: *mut crate::leanh::LeanObject,
    mut v___y_1706_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: usize = 0;
    let mut v___x_1711_: usize = 0;
    let mut v___x_1713_: u8 = 0;
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1719_: u8 = 0;
    let mut v_a_1720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1733_: u8 = 0;
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1737_: u8 = 0;
    let mut v_a_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1741_: u8 = 0;
    let mut v___x_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1745_: u8 = 0;
    let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1751_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1713_ = lean_usize_dec_lt(v_i_1701_, v_sz_1700_);
                if v___x_1713_ == 0 {
                    v___x_1714_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1714_, 0, v_b_1702_);
                    return v___x_1714_;
                } else {
                    v_fst_1715_ = crate::leanh::lean_ctor_get(v_b_1702_, 0);
                    v_snd_1716_ = crate::leanh::lean_ctor_get(v_b_1702_, 1);
                    v_isSharedCheck_1751_ = (!crate::leanh::lean_is_exclusive(v_b_1702_)) as u8;
                    if v_isSharedCheck_1751_ == 0 {
                        v___x_1718_ = v_b_1702_;
                        v_isShared_1719_ = v_isSharedCheck_1751_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1716_);
                        crate::leanh::lean_inc(v_fst_1715_);
                        crate::leanh::lean_dec(v_b_1702_);
                        v___x_1718_ = crate::leanh::lean_box(0);
                        v_isShared_1719_ = v_isSharedCheck_1751_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1710_ = 1usize;
                v___x_1711_ = lean_usize_add(v_i_1701_, v___x_1710_);
                v_i_1701_ = v___x_1711_;
                v_b_1702_ = v_a_1709_;
                state = 0;
                continue;
            }
            2 => {
                v_a_1720_ = lean_array_uget_borrowed(v_as_1699_, v_i_1701_);
                v___x_1721_ = l_Lean_Expr_isFVar(v_a_1720_);
                if v___x_1721_ == 0 {
                    crate::leanh::lean_inc(v___y_1706_);
                    crate::leanh::lean_inc_ref(v___y_1705_);
                    crate::leanh::lean_inc(v___y_1704_);
                    crate::leanh::lean_inc_ref(v___y_1703_);
                    crate::leanh::lean_inc(v_a_1720_);
                    v___x_1722_ = lean_infer_type(
                        v_a_1720_,
                        v___y_1703_,
                        v___y_1704_,
                        v___y_1705_,
                        v___y_1706_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1722_) == 0 {
                        v_a_1723_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                        crate::leanh::lean_inc(v_a_1723_);
                        crate::leanh::lean_dec_ref_known(v___x_1722_, 1);
                        v___x_1724_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__2___redArg(v_a_1723_, v___y_1704_);
                        if crate::leanh::lean_obj_tag(v___x_1724_) == 0 {
                            v_a_1725_ = crate::leanh::lean_ctor_get(v___x_1724_, 0);
                            crate::leanh::lean_inc(v_a_1725_);
                            crate::leanh::lean_dec_ref_known(v___x_1724_, 1);
                            v___x_1726_ = l_Lean_collectFVars(v_fst_1715_, v_a_1725_);
                            if v_isShared_1719_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1718_, 0, v___x_1726_);
                                v___x_1728_ = v___x_1718_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1729_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1726_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_snd_1716_);
                                v___x_1728_ = v_reuseFailAlloc_1729_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_1718_);
                            crate::leanh::lean_dec(v_snd_1716_);
                            crate::leanh::lean_dec(v_fst_1715_);
                            v_a_1730_ = crate::leanh::lean_ctor_get(v___x_1724_, 0);
                            v_isSharedCheck_1737_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1724_)) as u8;
                            if v_isSharedCheck_1737_ == 0 {
                                v___x_1732_ = v___x_1724_;
                                v_isShared_1733_ = v_isSharedCheck_1737_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1730_);
                                crate::leanh::lean_dec(v___x_1724_);
                                v___x_1732_ = crate::leanh::lean_box(0);
                                v_isShared_1733_ = v_isSharedCheck_1737_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_1718_);
                        crate::leanh::lean_dec(v_snd_1716_);
                        crate::leanh::lean_dec(v_fst_1715_);
                        v_a_1738_ = crate::leanh::lean_ctor_get(v___x_1722_, 0);
                        v_isSharedCheck_1745_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1722_)) as u8;
                        if v_isSharedCheck_1745_ == 0 {
                            v___x_1740_ = v___x_1722_;
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1738_);
                            crate::leanh::lean_dec(v___x_1722_);
                            v___x_1740_ = crate::leanh::lean_box(0);
                            v_isShared_1741_ = v_isSharedCheck_1745_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_1746_ = l_Lean_Expr_fvarId_x21(v_a_1720_);
                    v___x_1747_ = lean_array_push(v_snd_1716_, v___x_1746_);
                    if v_isShared_1719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1718_, 1, v___x_1747_);
                        v___x_1749_ = v___x_1718_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1750_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_fst_1715_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1750_, 1, v___x_1747_);
                        v___x_1749_ = v_reuseFailAlloc_1750_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1709_ = v___x_1728_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1733_ == 0 {
                    v___x_1735_ = v___x_1732_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1736_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_a_1730_);
                    v___x_1735_ = v_reuseFailAlloc_1736_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1735_;
            }
            6 => {
                if v_isShared_1741_ == 0 {
                    v___x_1743_ = v___x_1740_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1744_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1744_, 0, v_a_1738_);
                    v___x_1743_ = v_reuseFailAlloc_1744_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1743_;
            }
            8 => {
                v_a_1709_ = v___x_1749_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0___boxed(
    mut v_as_1752_: *mut crate::leanh::LeanObject,
    mut v_sz_1753_: *mut crate::leanh::LeanObject,
    mut v_i_1754_: *mut crate::leanh::LeanObject,
    mut v_b_1755_: *mut crate::leanh::LeanObject,
    mut v___y_1756_: *mut crate::leanh::LeanObject,
    mut v___y_1757_: *mut crate::leanh::LeanObject,
    mut v___y_1758_: *mut crate::leanh::LeanObject,
    mut v___y_1759_: *mut crate::leanh::LeanObject,
    mut v___y_1760_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1761_: usize = 0;
    let mut v_i_boxed_1762_: usize = 0;
    let mut v_res_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1761_ = crate::leanh::lean_unbox_usize(v_sz_1753_);
    crate::leanh::lean_dec(v_sz_1753_);
    v_i_boxed_1762_ = crate::leanh::lean_unbox_usize(v_i_1754_);
    crate::leanh::lean_dec(v_i_1754_);
    v_res_1763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_as_1752_, v_sz_boxed_1761_, v_i_boxed_1762_, v_b_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_);
    crate::leanh::lean_dec(v___y_1759_);
    crate::leanh::lean_dec_ref(v___y_1758_);
    crate::leanh::lean_dec(v___y_1757_);
    crate::leanh::lean_dec_ref(v___y_1756_);
    crate::leanh::lean_dec_ref(v_as_1752_);
    return v_res_1763_;
}
pub unsafe fn l_Lean_Meta_mkGeneralizationForbiddenSet(
    mut v_targets_1764_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1765_: *mut crate::leanh::LeanObject,
    mut v_a_1766_: *mut crate::leanh::LeanObject,
    mut v_a_1767_: *mut crate::leanh::LeanObject,
    mut v_a_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_todo_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1775_: usize = 0;
    let mut v___x_1776_: usize = 0;
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarSet_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1787_: u8 = 0;
    let mut v___x_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1791_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1771_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                v_todo_1772_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__2;
                v_s_1773_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v_s_1773_, 0, v___x_1771_);
                crate::leanh::lean_ctor_set(v_s_1773_, 1, v_forbidden_1765_);
                crate::leanh::lean_ctor_set(v_s_1773_, 2, v_todo_1772_);
                v___x_1774_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1774_, 0, v_s_1773_);
                crate::leanh::lean_ctor_set(v___x_1774_, 1, v_todo_1772_);
                v_sz_1775_ = lean_array_size(v_targets_1764_);
                v___x_1776_ = 0usize;
                v___x_1777_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_mkGeneralizationForbiddenSet_spec__0(v_targets_1764_, v_sz_1775_, v___x_1776_, v___x_1774_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
                if crate::leanh::lean_obj_tag(v___x_1777_) == 0 {
                    v_a_1778_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                    crate::leanh::lean_inc(v_a_1778_);
                    crate::leanh::lean_dec_ref_known(v___x_1777_, 1);
                    v_fst_1779_ = crate::leanh::lean_ctor_get(v_a_1778_, 0);
                    crate::leanh::lean_inc(v_fst_1779_);
                    v_snd_1780_ = crate::leanh::lean_ctor_get(v_a_1778_, 1);
                    crate::leanh::lean_inc(v_snd_1780_);
                    crate::leanh::lean_dec(v_a_1778_);
                    v_fvarSet_1781_ = crate::leanh::lean_ctor_get(v_fst_1779_, 1);
                    crate::leanh::lean_inc(v_fvarSet_1781_);
                    crate::leanh::lean_dec(v_fst_1779_);
                    v___x_1782_ = lean_array_to_list(v_snd_1780_);
                    v___x_1783_ = l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_loop(v___x_1782_, v_fvarSet_1781_, v_a_1766_, v_a_1767_, v_a_1768_, v_a_1769_);
                    return v___x_1783_;
                } else {
                    v_a_1784_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                    v_isSharedCheck_1791_ = (!crate::leanh::lean_is_exclusive(v___x_1777_)) as u8;
                    if v_isSharedCheck_1791_ == 0 {
                        v___x_1786_ = v___x_1777_;
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1784_);
                        crate::leanh::lean_dec(v___x_1777_);
                        v___x_1786_ = crate::leanh::lean_box(0);
                        v_isShared_1787_ = v_isSharedCheck_1791_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1787_ == 0 {
                    v___x_1789_ = v___x_1786_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1790_, 0, v_a_1784_);
                    v___x_1789_ = v_reuseFailAlloc_1790_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1789_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_mkGeneralizationForbiddenSet___boxed(
    mut v_targets_1792_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1793_: *mut crate::leanh::LeanObject,
    mut v_a_1794_: *mut crate::leanh::LeanObject,
    mut v_a_1795_: *mut crate::leanh::LeanObject,
    mut v_a_1796_: *mut crate::leanh::LeanObject,
    mut v_a_1797_: *mut crate::leanh::LeanObject,
    mut v_a_1798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1799_ = l_Lean_Meta_mkGeneralizationForbiddenSet(
        v_targets_1792_,
        v_forbidden_1793_,
        v_a_1794_,
        v_a_1795_,
        v_a_1796_,
        v_a_1797_,
    );
    crate::leanh::lean_dec(v_a_1797_);
    crate::leanh::lean_dec_ref(v_a_1796_);
    crate::leanh::lean_dec(v_a_1795_);
    crate::leanh::lean_dec_ref(v_a_1794_);
    crate::leanh::lean_dec_ref(v_targets_1792_);
    return v_res_1799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(
    mut v___y_1800_: u8,
    mut v_x_1801_: *mut crate::leanh::LeanObject,
) -> u8 {
    return v___y_1800_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed(
    mut v___y_1802_: *mut crate::leanh::LeanObject,
    mut v_x_1803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_9979__boxed_1804_: u8 = 0;
    let mut v_res_1805_: u8 = 0;
    let mut v_r_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___y_9979__boxed_1804_ = (crate::leanh::lean_unbox(v___y_1802_) as u8);
    v_res_1805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1(v___y_9979__boxed_1804_, v_x_1803_);
    crate::leanh::lean_dec(v_x_1803_);
    v_r_1806_ = crate::leanh::lean_box((v_res_1805_) as usize);
    return v_r_1806_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(
    mut v_fst_1807_: *mut crate::leanh::LeanObject,
    mut v_x_1808_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1809_: u8 = 0;
    v___x_1809_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v_x_1808_, v_fst_1807_);
    return v___x_1809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed(
    mut v_fst_1810_: *mut crate::leanh::LeanObject,
    mut v_x_1811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1812_: u8 = 0;
    let mut v_r_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0(v_fst_1810_, v_x_1811_);
    crate::leanh::lean_dec(v_x_1811_);
    crate::leanh::lean_dec(v_fst_1810_);
    v_r_1813_ = crate::leanh::lean_box((v_res_1812_) as usize);
    return v_r_1813_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(
    mut v_ignoreLetDecls_1814_: u8,
    mut v_forbidden_1815_: *mut crate::leanh::LeanObject,
    mut v_as_1816_: *mut crate::leanh::LeanObject,
    mut v_sz_1817_: usize,
    mut v_i_1818_: usize,
    mut v_b_1819_: *mut crate::leanh::LeanObject,
    mut v___y_1820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1827_: u8 = 0;
    let mut v___x_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: usize = 0;
    let mut v___x_1834_: usize = 0;
    let mut v_reuseFailAlloc_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1843_: u8 = 0;
    let mut v___x_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: u8 = 0;
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1856_: u8 = 0;
    let mut v_mctx_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1865_: u8 = 0;
    let mut v___x_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1870_: u8 = 0;
    let mut v_unused_1871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1877_: u8 = 0;
    let mut v_fst_1879_: u8 = 0;
    let mut v_snd_1880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1894_: u8 = 0;
    let mut v_unused_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: u8 = 0;
    let mut v_fst_1902_: u8 = 0;
    let mut v_mctx_1903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1911_: u8 = 0;
    let mut v___x_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1916_: u8 = 0;
    let mut v_unused_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: u8 = 0;
    let mut v___x_1924_: u8 = 0;
    let mut v___f_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1929_: u8 = 0;
    let mut v_snd_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1931_: u8 = 0;
    let mut v___x_1932_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1941_: u8 = 0;
    let mut v___y_1943_: u8 = 0;
    let mut v___x_1944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: u8 = 0;
    let mut v___x_1952_: u8 = 0;
    let mut v___x_1953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1955_: u8 = 0;
    let mut v_type_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: u8 = 0;
    let mut v___x_1964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1971_: u8 = 0;
    let mut v___x_1972_: u8 = 0;
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1976_: u8 = 0;
    let mut v___x_1977_: u8 = 0;
    let mut v___x_1978_: u8 = 0;
    let mut v___x_1979_: u8 = 0;
    let mut v___x_1980_: u8 = 0;
    let mut v___x_1981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1982_: u8 = 0;
    let mut v_isSharedCheck_1983_: u8 = 0;
    let mut v_unused_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1822_ = lean_usize_dec_lt(v_i_1818_, v_sz_1817_);
                if v___x_1822_ == 0 {
                    v___x_1823_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1823_, 0, v_b_1819_);
                    return v___x_1823_;
                } else {
                    v_snd_1824_ = crate::leanh::lean_ctor_get(v_b_1819_, 1);
                    v_isSharedCheck_1983_ = (!crate::leanh::lean_is_exclusive(v_b_1819_)) as u8;
                    if v_isSharedCheck_1983_ == 0 {
                        v_unused_1984_ = crate::leanh::lean_ctor_get(v_b_1819_, 0);
                        crate::leanh::lean_dec(v_unused_1984_);
                        v___x_1826_ = v_b_1819_;
                        v_isShared_1827_ = v_isSharedCheck_1983_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1824_);
                        crate::leanh::lean_dec(v_b_1819_);
                        v___x_1826_ = crate::leanh::lean_box(0);
                        v_isShared_1827_ = v_isSharedCheck_1983_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1828_ = crate::leanh::lean_box(0);
                v_a_1837_ = lean_array_uget_borrowed(v_as_1816_, v_i_1818_);
                if crate::leanh::lean_obj_tag(v_a_1837_) == 0 {
                    v_a_1830_ = v_snd_1824_;
                    state = 2;
                    continue;
                } else {
                    v_val_1838_ = crate::leanh::lean_ctor_get(v_a_1837_, 0);
                    v_fst_1839_ = crate::leanh::lean_ctor_get(v_snd_1824_, 0);
                    v_snd_1840_ = crate::leanh::lean_ctor_get(v_snd_1824_, 1);
                    v_isSharedCheck_1982_ = (!crate::leanh::lean_is_exclusive(v_snd_1824_)) as u8;
                    if v_isSharedCheck_1982_ == 0 {
                        v___x_1842_ = v_snd_1824_;
                        v_isShared_1843_ = v_isSharedCheck_1982_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1840_);
                        crate::leanh::lean_inc(v_fst_1839_);
                        crate::leanh::lean_dec(v_snd_1824_);
                        v___x_1842_ = crate::leanh::lean_box(0);
                        v_isShared_1843_ = v_isSharedCheck_1982_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1827_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1826_, 1, v_a_1830_);
                    crate::leanh::lean_ctor_set(v___x_1826_, 0, v___x_1828_);
                    v___x_1832_ = v___x_1826_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1836_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1828_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1836_, 1, v_a_1830_);
                    v___x_1832_ = v_reuseFailAlloc_1836_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1833_ = 1usize;
                v___x_1834_ = lean_usize_add(v_i_1818_, v___x_1833_);
                v_i_1818_ = v___x_1834_;
                v_b_1819_ = v___x_1832_;
                state = 0;
                continue;
            }
            4 => {
                v___x_1848_ = l_Lean_LocalDecl_fvarId(v_val_1838_);
                v___x_1924_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_1848_, v_forbidden_1815_);
                if v___x_1924_ == 0 {
                    crate::leanh::lean_inc(v_fst_1839_);
                    v___f_1925_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_1925_, 0, v_fst_1839_);
                    v___x_1978_ = l_Lean_LocalDecl_isAuxDecl(v_val_1838_);
                    if v___x_1978_ == 0 {
                        v___x_1979_ = l_Lean_LocalDecl_binderInfo(v_val_1838_);
                        v___x_1980_ = l_Lean_BinderInfo_isInstImplicit(v___x_1979_);
                        v___y_1976_ = v___x_1980_;
                        state = 23;
                        continue;
                    } else {
                        v___y_1976_ = v___x_1978_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1848_);
                    crate::leanh::lean_del_object(v___x_1842_);
                    v___x_1981_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1981_, 0, v_fst_1839_);
                    crate::leanh::lean_ctor_set(v___x_1981_, 1, v_snd_1840_);
                    v_a_1830_ = v___x_1981_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_1843_ == 0 {
                    v___x_1846_ = v___x_1842_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1847_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 0, v_fst_1839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1847_, 1, v_snd_1840_);
                    v___x_1846_ = v_reuseFailAlloc_1847_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_1830_ = v___x_1846_;
                state = 2;
                continue;
            }
            7 => {
                if v_a_1850_ == 0 {
                    crate::leanh::lean_dec(v___x_1848_);
                    v___x_1851_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1851_, 0, v_fst_1839_);
                    crate::leanh::lean_ctor_set(v___x_1851_, 1, v_snd_1840_);
                    v_a_1830_ = v___x_1851_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_1848_);
                    v___x_1852_ = l_Lean_FVarIdSet_insert(v_snd_1840_, v___x_1848_);
                    v___x_1853_ = l_Lean_FVarIdSet_insert(v_fst_1839_, v___x_1848_);
                    v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1854_, 0, v___x_1853_);
                    crate::leanh::lean_ctor_set(v___x_1854_, 1, v___x_1852_);
                    v_a_1830_ = v___x_1854_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_1858_ = lean_st_ref_take(v___y_1820_);
                v_cache_1859_ = crate::leanh::lean_ctor_get(v___x_1858_, 1);
                v_zetaDeltaFVarIds_1860_ = crate::leanh::lean_ctor_get(v___x_1858_, 2);
                v_postponed_1861_ = crate::leanh::lean_ctor_get(v___x_1858_, 3);
                v_diag_1862_ = crate::leanh::lean_ctor_get(v___x_1858_, 4);
                v_isSharedCheck_1870_ = (!crate::leanh::lean_is_exclusive(v___x_1858_)) as u8;
                if v_isSharedCheck_1870_ == 0 {
                    v_unused_1871_ = crate::leanh::lean_ctor_get(v___x_1858_, 0);
                    crate::leanh::lean_dec(v_unused_1871_);
                    v___x_1864_ = v___x_1858_;
                    v_isShared_1865_ = v_isSharedCheck_1870_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1862_);
                    crate::leanh::lean_inc(v_postponed_1861_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1860_);
                    crate::leanh::lean_inc(v_cache_1859_);
                    crate::leanh::lean_dec(v___x_1858_);
                    v___x_1864_ = crate::leanh::lean_box(0);
                    v_isShared_1865_ = v_isSharedCheck_1870_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1865_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1864_, 0, v_mctx_1857_);
                    v___x_1867_ = v___x_1864_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1869_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 0, v_mctx_1857_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 1, v_cache_1859_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1869_,
                        2,
                        v_zetaDeltaFVarIds_1860_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 3, v_postponed_1861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1869_, 4, v_diag_1862_);
                    v___x_1867_ = v_reuseFailAlloc_1869_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_1868_ = lean_st_ref_set(v___y_1820_, v___x_1867_);
                v_a_1850_ = v_fst_1856_;
                state = 7;
                continue;
            }
            11 => {
                v_snd_1874_ = crate::leanh::lean_ctor_get(v___y_1873_, 1);
                crate::leanh::lean_inc(v_snd_1874_);
                v_fst_1875_ = crate::leanh::lean_ctor_get(v___y_1873_, 0);
                crate::leanh::lean_inc(v_fst_1875_);
                crate::leanh::lean_dec_ref(v___y_1873_);
                v_mctx_1876_ = crate::leanh::lean_ctor_get(v_snd_1874_, 1);
                crate::leanh::lean_inc_ref(v_mctx_1876_);
                crate::leanh::lean_dec(v_snd_1874_);
                v___x_1877_ = (crate::leanh::lean_unbox(v_fst_1875_) as u8);
                crate::leanh::lean_dec(v_fst_1875_);
                v_fst_1856_ = v___x_1877_;
                v_mctx_1857_ = v_mctx_1876_;
                state = 8;
                continue;
            }
            12 => {
                v_mctx_1881_ = crate::leanh::lean_ctor_get(v_snd_1880_, 1);
                crate::leanh::lean_inc_ref(v_mctx_1881_);
                crate::leanh::lean_dec_ref(v_snd_1880_);
                v___x_1882_ = lean_st_ref_take(v___y_1820_);
                v_cache_1883_ = crate::leanh::lean_ctor_get(v___x_1882_, 1);
                v_zetaDeltaFVarIds_1884_ = crate::leanh::lean_ctor_get(v___x_1882_, 2);
                v_postponed_1885_ = crate::leanh::lean_ctor_get(v___x_1882_, 3);
                v_diag_1886_ = crate::leanh::lean_ctor_get(v___x_1882_, 4);
                v_isSharedCheck_1894_ = (!crate::leanh::lean_is_exclusive(v___x_1882_)) as u8;
                if v_isSharedCheck_1894_ == 0 {
                    v_unused_1895_ = crate::leanh::lean_ctor_get(v___x_1882_, 0);
                    crate::leanh::lean_dec(v_unused_1895_);
                    v___x_1888_ = v___x_1882_;
                    v_isShared_1889_ = v_isSharedCheck_1894_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1886_);
                    crate::leanh::lean_inc(v_postponed_1885_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1884_);
                    crate::leanh::lean_inc(v_cache_1883_);
                    crate::leanh::lean_dec(v___x_1882_);
                    v___x_1888_ = crate::leanh::lean_box(0);
                    v_isShared_1889_ = v_isSharedCheck_1894_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_1889_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1888_, 0, v_mctx_1881_);
                    v___x_1891_ = v___x_1888_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_1893_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_mctx_1881_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_cache_1883_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1893_,
                        2,
                        v_zetaDeltaFVarIds_1884_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 3, v_postponed_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1893_, 4, v_diag_1886_);
                    v___x_1891_ = v_reuseFailAlloc_1893_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_1892_ = lean_st_ref_set(v___y_1820_, v___x_1891_);
                v_a_1850_ = v_fst_1879_;
                state = 7;
                continue;
            }
            15 => {
                v_fst_1898_ = crate::leanh::lean_ctor_get(v___y_1897_, 0);
                crate::leanh::lean_inc(v_fst_1898_);
                v_snd_1899_ = crate::leanh::lean_ctor_get(v___y_1897_, 1);
                crate::leanh::lean_inc(v_snd_1899_);
                crate::leanh::lean_dec_ref(v___y_1897_);
                v___x_1900_ = (crate::leanh::lean_unbox(v_fst_1898_) as u8);
                crate::leanh::lean_dec(v_fst_1898_);
                v_fst_1879_ = v___x_1900_;
                v_snd_1880_ = v_snd_1899_;
                state = 12;
                continue;
            }
            16 => {
                v___x_1904_ = lean_st_ref_take(v___y_1820_);
                v_cache_1905_ = crate::leanh::lean_ctor_get(v___x_1904_, 1);
                v_zetaDeltaFVarIds_1906_ = crate::leanh::lean_ctor_get(v___x_1904_, 2);
                v_postponed_1907_ = crate::leanh::lean_ctor_get(v___x_1904_, 3);
                v_diag_1908_ = crate::leanh::lean_ctor_get(v___x_1904_, 4);
                v_isSharedCheck_1916_ = (!crate::leanh::lean_is_exclusive(v___x_1904_)) as u8;
                if v_isSharedCheck_1916_ == 0 {
                    v_unused_1917_ = crate::leanh::lean_ctor_get(v___x_1904_, 0);
                    crate::leanh::lean_dec(v_unused_1917_);
                    v___x_1910_ = v___x_1904_;
                    v_isShared_1911_ = v_isSharedCheck_1916_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1908_);
                    crate::leanh::lean_inc(v_postponed_1907_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1906_);
                    crate::leanh::lean_inc(v_cache_1905_);
                    crate::leanh::lean_dec(v___x_1904_);
                    v___x_1910_ = crate::leanh::lean_box(0);
                    v_isShared_1911_ = v_isSharedCheck_1916_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_1911_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1910_, 0, v_mctx_1903_);
                    v___x_1913_ = v___x_1910_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_1915_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_mctx_1903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_cache_1905_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1915_,
                        2,
                        v_zetaDeltaFVarIds_1906_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 3, v_postponed_1907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1915_, 4, v_diag_1908_);
                    v___x_1913_ = v_reuseFailAlloc_1915_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_1914_ = lean_st_ref_set(v___y_1820_, v___x_1913_);
                v_a_1850_ = v_fst_1902_;
                state = 7;
                continue;
            }
            19 => {
                v_snd_1920_ = crate::leanh::lean_ctor_get(v___y_1919_, 1);
                crate::leanh::lean_inc(v_snd_1920_);
                v_fst_1921_ = crate::leanh::lean_ctor_get(v___y_1919_, 0);
                crate::leanh::lean_inc(v_fst_1921_);
                crate::leanh::lean_dec_ref(v___y_1919_);
                v_mctx_1922_ = crate::leanh::lean_ctor_get(v_snd_1920_, 1);
                crate::leanh::lean_inc_ref(v_mctx_1922_);
                crate::leanh::lean_dec(v_snd_1920_);
                v___x_1923_ = (crate::leanh::lean_unbox(v_fst_1921_) as u8);
                crate::leanh::lean_dec(v_fst_1921_);
                v_fst_1902_ = v___x_1923_;
                v_mctx_1903_ = v_mctx_1922_;
                state = 16;
                continue;
            }
            20 => {
                if v_fst_1929_ == 0 {
                    v___x_1931_ = l_Lean_Expr_hasFVar(v___y_1927_);
                    if v___x_1931_ == 0 {
                        v___x_1932_ = l_Lean_Expr_hasMVar(v___y_1927_);
                        if v___x_1932_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_1928_);
                            crate::leanh::lean_dec_ref(v___y_1927_);
                            crate::leanh::lean_dec_ref(v___f_1925_);
                            v_fst_1879_ = v___x_1932_;
                            v_snd_1880_ = v_snd_1930_;
                            state = 12;
                            continue;
                        } else {
                            v___x_1933_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1925_,
                                    v___y_1928_,
                                    v___y_1927_,
                                    v_snd_1930_,
                                );
                            v___y_1897_ = v___x_1933_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_1934_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1925_,
                            v___y_1928_,
                            v___y_1927_,
                            v_snd_1930_,
                        );
                        v___y_1897_ = v___x_1934_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_1928_);
                    crate::leanh::lean_dec_ref(v___y_1927_);
                    crate::leanh::lean_dec_ref(v___f_1925_);
                    v_fst_1879_ = v_fst_1929_;
                    v_snd_1880_ = v_snd_1930_;
                    state = 12;
                    continue;
                }
            }
            21 => {
                v_fst_1939_ = crate::leanh::lean_ctor_get(v___y_1938_, 0);
                crate::leanh::lean_inc(v_fst_1939_);
                v_snd_1940_ = crate::leanh::lean_ctor_get(v___y_1938_, 1);
                crate::leanh::lean_inc(v_snd_1940_);
                crate::leanh::lean_dec_ref(v___y_1938_);
                v___x_1941_ = (crate::leanh::lean_unbox(v_fst_1939_) as u8);
                crate::leanh::lean_dec(v_fst_1939_);
                v___y_1927_ = v___y_1936_;
                v___y_1928_ = v___y_1937_;
                v_fst_1929_ = v___x_1941_;
                v_snd_1930_ = v_snd_1940_;
                state = 20;
                continue;
            }
            22 => {
                v___x_1944_ = crate::leanh::lean_box((v___y_1943_) as usize);
                v___f_1945_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_1945_, 0, v___x_1944_);
                if crate::leanh::lean_obj_tag(v_val_1838_) == 0 {
                    v_type_1946_ = crate::leanh::lean_ctor_get(v_val_1838_, 3);
                    v___x_1947_ = lean_st_ref_get(v___y_1820_);
                    v_mctx_1948_ = crate::leanh::lean_ctor_get(v___x_1947_, 0);
                    crate::leanh::lean_inc_ref_n(v_mctx_1948_, 2);
                    crate::leanh::lean_dec(v___x_1947_);
                    v___x_1949_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                    v___x_1950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1950_, 0, v___x_1949_);
                    crate::leanh::lean_ctor_set(v___x_1950_, 1, v_mctx_1948_);
                    v___x_1951_ = l_Lean_Expr_hasFVar(v_type_1946_);
                    if v___x_1951_ == 0 {
                        v___x_1952_ = l_Lean_Expr_hasMVar(v_type_1946_);
                        if v___x_1952_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1950_, 2);
                            crate::leanh::lean_dec_ref(v___f_1945_);
                            crate::leanh::lean_dec_ref(v___f_1925_);
                            v_fst_1856_ = v___x_1952_;
                            v_mctx_1857_ = v_mctx_1948_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_1948_);
                            crate::leanh::lean_inc_ref(v_type_1946_);
                            v___x_1953_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1925_,
                                    v___f_1945_,
                                    v_type_1946_,
                                    v___x_1950_,
                                );
                            v___y_1873_ = v___x_1953_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_1948_);
                        crate::leanh::lean_inc_ref(v_type_1946_);
                        v___x_1954_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_1925_,
                            v___f_1945_,
                            v_type_1946_,
                            v___x_1950_,
                        );
                        v___y_1873_ = v___x_1954_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_nondep_1955_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_1838_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_1955_ == 0 {
                        v_type_1956_ = crate::leanh::lean_ctor_get(v_val_1838_, 3);
                        v_value_1957_ = crate::leanh::lean_ctor_get(v_val_1838_, 4);
                        v___x_1958_ = lean_st_ref_get(v___y_1820_);
                        v_mctx_1959_ = crate::leanh::lean_ctor_get(v___x_1958_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_1959_);
                        crate::leanh::lean_dec(v___x_1958_);
                        v___x_1960_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_1961_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1961_, 0, v___x_1960_);
                        crate::leanh::lean_ctor_set(v___x_1961_, 1, v_mctx_1959_);
                        v___x_1962_ = l_Lean_Expr_hasFVar(v_type_1956_);
                        if v___x_1962_ == 0 {
                            v___x_1963_ = l_Lean_Expr_hasMVar(v_type_1956_);
                            if v___x_1963_ == 0 {
                                crate::leanh::lean_inc_ref(v_value_1957_);
                                v___y_1927_ = v_value_1957_;
                                v___y_1928_ = v___f_1945_;
                                v_fst_1929_ = v___x_1963_;
                                v_snd_1930_ = v___x_1961_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_type_1956_);
                                crate::leanh::lean_inc_ref(v___f_1945_);
                                crate::leanh::lean_inc_ref(v___f_1925_);
                                v___x_1964_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_1925_,
                                        v___f_1945_,
                                        v_type_1956_,
                                        v___x_1961_,
                                    );
                                crate::leanh::lean_inc_ref(v_value_1957_);
                                v___y_1936_ = v_value_1957_;
                                v___y_1937_ = v___f_1945_;
                                v___y_1938_ = v___x_1964_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_type_1956_);
                            crate::leanh::lean_inc_ref(v___f_1945_);
                            crate::leanh::lean_inc_ref(v___f_1925_);
                            v___x_1965_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1925_,
                                    v___f_1945_,
                                    v_type_1956_,
                                    v___x_1961_,
                                );
                            crate::leanh::lean_inc_ref(v_value_1957_);
                            v___y_1936_ = v_value_1957_;
                            v___y_1937_ = v___f_1945_;
                            v___y_1938_ = v___x_1965_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_type_1966_ = crate::leanh::lean_ctor_get(v_val_1838_, 3);
                        v___x_1967_ = lean_st_ref_get(v___y_1820_);
                        v_mctx_1968_ = crate::leanh::lean_ctor_get(v___x_1967_, 0);
                        crate::leanh::lean_inc_ref_n(v_mctx_1968_, 2);
                        crate::leanh::lean_dec(v___x_1967_);
                        v___x_1969_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_1970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1970_, 0, v___x_1969_);
                        crate::leanh::lean_ctor_set(v___x_1970_, 1, v_mctx_1968_);
                        v___x_1971_ = l_Lean_Expr_hasFVar(v_type_1966_);
                        if v___x_1971_ == 0 {
                            v___x_1972_ = l_Lean_Expr_hasMVar(v_type_1966_);
                            if v___x_1972_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1970_, 2);
                                crate::leanh::lean_dec_ref(v___f_1945_);
                                crate::leanh::lean_dec_ref(v___f_1925_);
                                v_fst_1902_ = v___x_1972_;
                                v_mctx_1903_ = v_mctx_1968_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_mctx_1968_);
                                crate::leanh::lean_inc_ref(v_type_1966_);
                                v___x_1973_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_1925_,
                                        v___f_1945_,
                                        v_type_1966_,
                                        v___x_1970_,
                                    );
                                v___y_1919_ = v___x_1973_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_1968_);
                            crate::leanh::lean_inc_ref(v_type_1966_);
                            v___x_1974_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_1925_,
                                    v___f_1945_,
                                    v_type_1966_,
                                    v___x_1970_,
                                );
                            v___y_1919_ = v___x_1974_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            23 => {
                if v___y_1976_ == 0 {
                    if v_ignoreLetDecls_1814_ == 0 {
                        crate::leanh::lean_del_object(v___x_1842_);
                        v___y_1943_ = v_ignoreLetDecls_1814_;
                        state = 22;
                        continue;
                    } else {
                        v___x_1977_ = l_Lean_LocalDecl_isLet(v_val_1838_, v___y_1976_);
                        if v___x_1977_ == 0 {
                            crate::leanh::lean_del_object(v___x_1842_);
                            v___y_1943_ = v___x_1977_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_1925_);
                            crate::leanh::lean_dec(v___x_1848_);
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_1925_);
                    crate::leanh::lean_dec(v___x_1848_);
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_ignoreLetDecls_1985_: *mut crate::leanh::LeanObject,
    mut v_forbidden_1986_: *mut crate::leanh::LeanObject,
    mut v_as_1987_: *mut crate::leanh::LeanObject,
    mut v_sz_1988_: *mut crate::leanh::LeanObject,
    mut v_i_1989_: *mut crate::leanh::LeanObject,
    mut v_b_1990_: *mut crate::leanh::LeanObject,
    mut v___y_1991_: *mut crate::leanh::LeanObject,
    mut v___y_1992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_1993_: u8 = 0;
    let mut v_sz_boxed_1994_: usize = 0;
    let mut v_i_boxed_1995_: usize = 0;
    let mut v_res_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_1993_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_1985_) as u8);
    v_sz_boxed_1994_ = crate::leanh::lean_unbox_usize(v_sz_1988_);
    crate::leanh::lean_dec(v_sz_1988_);
    v_i_boxed_1995_ = crate::leanh::lean_unbox_usize(v_i_1989_);
    crate::leanh::lean_dec(v_i_1989_);
    v_res_1996_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_boxed_1993_, v_forbidden_1986_, v_as_1987_, v_sz_boxed_1994_, v_i_boxed_1995_, v_b_1990_, v___y_1991_);
    crate::leanh::lean_dec(v___y_1991_);
    crate::leanh::lean_dec_ref(v_as_1987_);
    crate::leanh::lean_dec(v_forbidden_1986_);
    return v_res_1996_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(
    mut v_ignoreLetDecls_1997_: u8,
    mut v_forbidden_1998_: *mut crate::leanh::LeanObject,
    mut v_as_1999_: *mut crate::leanh::LeanObject,
    mut v_sz_2000_: usize,
    mut v_i_2001_: usize,
    mut v_b_2002_: *mut crate::leanh::LeanObject,
    mut v___y_2003_: *mut crate::leanh::LeanObject,
    mut v___y_2004_: *mut crate::leanh::LeanObject,
    mut v___y_2005_: *mut crate::leanh::LeanObject,
    mut v___y_2006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2008_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2013_: u8 = 0;
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2019_: usize = 0;
    let mut v___x_2020_: usize = 0;
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2029_: u8 = 0;
    let mut v___x_2032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2036_: u8 = 0;
    let mut v___x_2037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2042_: u8 = 0;
    let mut v_mctx_2043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2051_: u8 = 0;
    let mut v___x_2053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2056_: u8 = 0;
    let mut v_unused_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: u8 = 0;
    let mut v_fst_2065_: u8 = 0;
    let mut v_snd_2066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2075_: u8 = 0;
    let mut v___x_2077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2080_: u8 = 0;
    let mut v_unused_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: u8 = 0;
    let mut v_fst_2088_: u8 = 0;
    let mut v_mctx_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2102_: u8 = 0;
    let mut v_unused_2103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: u8 = 0;
    let mut v___x_2110_: u8 = 0;
    let mut v___f_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2115_: u8 = 0;
    let mut v_snd_2116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: u8 = 0;
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: u8 = 0;
    let mut v___y_2129_: u8 = 0;
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: u8 = 0;
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2141_: u8 = 0;
    let mut v_type_2142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: u8 = 0;
    let mut v___x_2149_: u8 = 0;
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: u8 = 0;
    let mut v___x_2158_: u8 = 0;
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2162_: u8 = 0;
    let mut v___x_2163_: u8 = 0;
    let mut v___x_2164_: u8 = 0;
    let mut v___x_2165_: u8 = 0;
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2168_: u8 = 0;
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut v_unused_2170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2008_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
                if v___x_2008_ == 0 {
                    v___x_2009_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2009_, 0, v_b_2002_);
                    return v___x_2009_;
                } else {
                    v_snd_2010_ = crate::leanh::lean_ctor_get(v_b_2002_, 1);
                    v_isSharedCheck_2169_ = (!crate::leanh::lean_is_exclusive(v_b_2002_)) as u8;
                    if v_isSharedCheck_2169_ == 0 {
                        v_unused_2170_ = crate::leanh::lean_ctor_get(v_b_2002_, 0);
                        crate::leanh::lean_dec(v_unused_2170_);
                        v___x_2012_ = v_b_2002_;
                        v_isShared_2013_ = v_isSharedCheck_2169_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2010_);
                        crate::leanh::lean_dec(v_b_2002_);
                        v___x_2012_ = crate::leanh::lean_box(0);
                        v_isShared_2013_ = v_isSharedCheck_2169_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2014_ = crate::leanh::lean_box(0);
                v_a_2023_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
                if crate::leanh::lean_obj_tag(v_a_2023_) == 0 {
                    v_a_2016_ = v_snd_2010_;
                    state = 2;
                    continue;
                } else {
                    v_val_2024_ = crate::leanh::lean_ctor_get(v_a_2023_, 0);
                    v_fst_2025_ = crate::leanh::lean_ctor_get(v_snd_2010_, 0);
                    v_snd_2026_ = crate::leanh::lean_ctor_get(v_snd_2010_, 1);
                    v_isSharedCheck_2168_ = (!crate::leanh::lean_is_exclusive(v_snd_2010_)) as u8;
                    if v_isSharedCheck_2168_ == 0 {
                        v___x_2028_ = v_snd_2010_;
                        v_isShared_2029_ = v_isSharedCheck_2168_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2026_);
                        crate::leanh::lean_inc(v_fst_2025_);
                        crate::leanh::lean_dec(v_snd_2010_);
                        v___x_2028_ = crate::leanh::lean_box(0);
                        v_isShared_2029_ = v_isSharedCheck_2168_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2013_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2012_, 1, v_a_2016_);
                    crate::leanh::lean_ctor_set(v___x_2012_, 0, v___x_2014_);
                    v___x_2018_ = v___x_2012_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2022_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 0, v___x_2014_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_a_2016_);
                    v___x_2018_ = v_reuseFailAlloc_2022_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2019_ = 1usize;
                v___x_2020_ = lean_usize_add(v_i_2001_, v___x_2019_);
                v___x_2021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_1997_, v_forbidden_1998_, v_as_1999_, v_sz_2000_, v___x_2020_, v___x_2018_, v___y_2004_);
                return v___x_2021_;
            }
            4 => {
                v___x_2034_ = l_Lean_LocalDecl_fvarId(v_val_2024_);
                v___x_2110_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_2034_, v_forbidden_1998_);
                if v___x_2110_ == 0 {
                    crate::leanh::lean_inc(v_fst_2025_);
                    v___f_2111_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2111_, 0, v_fst_2025_);
                    v___x_2164_ = l_Lean_LocalDecl_isAuxDecl(v_val_2024_);
                    if v___x_2164_ == 0 {
                        v___x_2165_ = l_Lean_LocalDecl_binderInfo(v_val_2024_);
                        v___x_2166_ = l_Lean_BinderInfo_isInstImplicit(v___x_2165_);
                        v___y_2162_ = v___x_2166_;
                        state = 23;
                        continue;
                    } else {
                        v___y_2162_ = v___x_2164_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2034_);
                    crate::leanh::lean_del_object(v___x_2028_);
                    v___x_2167_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2167_, 0, v_fst_2025_);
                    crate::leanh::lean_ctor_set(v___x_2167_, 1, v_snd_2026_);
                    v_a_2016_ = v___x_2167_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2029_ == 0 {
                    v___x_2032_ = v___x_2028_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 0, v_fst_2025_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2033_, 1, v_snd_2026_);
                    v___x_2032_ = v_reuseFailAlloc_2033_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2016_ = v___x_2032_;
                state = 2;
                continue;
            }
            7 => {
                if v_a_2036_ == 0 {
                    crate::leanh::lean_dec(v___x_2034_);
                    v___x_2037_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2037_, 0, v_fst_2025_);
                    crate::leanh::lean_ctor_set(v___x_2037_, 1, v_snd_2026_);
                    v_a_2016_ = v___x_2037_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_2034_);
                    v___x_2038_ = l_Lean_FVarIdSet_insert(v_snd_2026_, v___x_2034_);
                    v___x_2039_ = l_Lean_FVarIdSet_insert(v_fst_2025_, v___x_2034_);
                    v___x_2040_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2040_, 0, v___x_2039_);
                    crate::leanh::lean_ctor_set(v___x_2040_, 1, v___x_2038_);
                    v_a_2016_ = v___x_2040_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_2044_ = lean_st_ref_take(v___y_2004_);
                v_cache_2045_ = crate::leanh::lean_ctor_get(v___x_2044_, 1);
                v_zetaDeltaFVarIds_2046_ = crate::leanh::lean_ctor_get(v___x_2044_, 2);
                v_postponed_2047_ = crate::leanh::lean_ctor_get(v___x_2044_, 3);
                v_diag_2048_ = crate::leanh::lean_ctor_get(v___x_2044_, 4);
                v_isSharedCheck_2056_ = (!crate::leanh::lean_is_exclusive(v___x_2044_)) as u8;
                if v_isSharedCheck_2056_ == 0 {
                    v_unused_2057_ = crate::leanh::lean_ctor_get(v___x_2044_, 0);
                    crate::leanh::lean_dec(v_unused_2057_);
                    v___x_2050_ = v___x_2044_;
                    v_isShared_2051_ = v_isSharedCheck_2056_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2048_);
                    crate::leanh::lean_inc(v_postponed_2047_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2046_);
                    crate::leanh::lean_inc(v_cache_2045_);
                    crate::leanh::lean_dec(v___x_2044_);
                    v___x_2050_ = crate::leanh::lean_box(0);
                    v_isShared_2051_ = v_isSharedCheck_2056_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2051_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2050_, 0, v_mctx_2043_);
                    v___x_2053_ = v___x_2050_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2055_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 0, v_mctx_2043_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_cache_2045_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2055_,
                        2,
                        v_zetaDeltaFVarIds_2046_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 3, v_postponed_2047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2055_, 4, v_diag_2048_);
                    v___x_2053_ = v_reuseFailAlloc_2055_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2054_ = lean_st_ref_set(v___y_2004_, v___x_2053_);
                v_a_2036_ = v_fst_2042_;
                state = 7;
                continue;
            }
            11 => {
                v_snd_2060_ = crate::leanh::lean_ctor_get(v___y_2059_, 1);
                crate::leanh::lean_inc(v_snd_2060_);
                v_fst_2061_ = crate::leanh::lean_ctor_get(v___y_2059_, 0);
                crate::leanh::lean_inc(v_fst_2061_);
                crate::leanh::lean_dec_ref(v___y_2059_);
                v_mctx_2062_ = crate::leanh::lean_ctor_get(v_snd_2060_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2062_);
                crate::leanh::lean_dec(v_snd_2060_);
                v___x_2063_ = (crate::leanh::lean_unbox(v_fst_2061_) as u8);
                crate::leanh::lean_dec(v_fst_2061_);
                v_fst_2042_ = v___x_2063_;
                v_mctx_2043_ = v_mctx_2062_;
                state = 8;
                continue;
            }
            12 => {
                v_mctx_2067_ = crate::leanh::lean_ctor_get(v_snd_2066_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2067_);
                crate::leanh::lean_dec_ref(v_snd_2066_);
                v___x_2068_ = lean_st_ref_take(v___y_2004_);
                v_cache_2069_ = crate::leanh::lean_ctor_get(v___x_2068_, 1);
                v_zetaDeltaFVarIds_2070_ = crate::leanh::lean_ctor_get(v___x_2068_, 2);
                v_postponed_2071_ = crate::leanh::lean_ctor_get(v___x_2068_, 3);
                v_diag_2072_ = crate::leanh::lean_ctor_get(v___x_2068_, 4);
                v_isSharedCheck_2080_ = (!crate::leanh::lean_is_exclusive(v___x_2068_)) as u8;
                if v_isSharedCheck_2080_ == 0 {
                    v_unused_2081_ = crate::leanh::lean_ctor_get(v___x_2068_, 0);
                    crate::leanh::lean_dec(v_unused_2081_);
                    v___x_2074_ = v___x_2068_;
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2072_);
                    crate::leanh::lean_inc(v_postponed_2071_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2070_);
                    crate::leanh::lean_inc(v_cache_2069_);
                    crate::leanh::lean_dec(v___x_2068_);
                    v___x_2074_ = crate::leanh::lean_box(0);
                    v_isShared_2075_ = v_isSharedCheck_2080_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2075_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2074_, 0, v_mctx_2067_);
                    v___x_2077_ = v___x_2074_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2079_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 0, v_mctx_2067_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 1, v_cache_2069_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2079_,
                        2,
                        v_zetaDeltaFVarIds_2070_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 3, v_postponed_2071_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2079_, 4, v_diag_2072_);
                    v___x_2077_ = v_reuseFailAlloc_2079_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2078_ = lean_st_ref_set(v___y_2004_, v___x_2077_);
                v_a_2036_ = v_fst_2065_;
                state = 7;
                continue;
            }
            15 => {
                v_fst_2084_ = crate::leanh::lean_ctor_get(v___y_2083_, 0);
                crate::leanh::lean_inc(v_fst_2084_);
                v_snd_2085_ = crate::leanh::lean_ctor_get(v___y_2083_, 1);
                crate::leanh::lean_inc(v_snd_2085_);
                crate::leanh::lean_dec_ref(v___y_2083_);
                v___x_2086_ = (crate::leanh::lean_unbox(v_fst_2084_) as u8);
                crate::leanh::lean_dec(v_fst_2084_);
                v_fst_2065_ = v___x_2086_;
                v_snd_2066_ = v_snd_2085_;
                state = 12;
                continue;
            }
            16 => {
                v___x_2090_ = lean_st_ref_take(v___y_2004_);
                v_cache_2091_ = crate::leanh::lean_ctor_get(v___x_2090_, 1);
                v_zetaDeltaFVarIds_2092_ = crate::leanh::lean_ctor_get(v___x_2090_, 2);
                v_postponed_2093_ = crate::leanh::lean_ctor_get(v___x_2090_, 3);
                v_diag_2094_ = crate::leanh::lean_ctor_get(v___x_2090_, 4);
                v_isSharedCheck_2102_ = (!crate::leanh::lean_is_exclusive(v___x_2090_)) as u8;
                if v_isSharedCheck_2102_ == 0 {
                    v_unused_2103_ = crate::leanh::lean_ctor_get(v___x_2090_, 0);
                    crate::leanh::lean_dec(v_unused_2103_);
                    v___x_2096_ = v___x_2090_;
                    v_isShared_2097_ = v_isSharedCheck_2102_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2094_);
                    crate::leanh::lean_inc(v_postponed_2093_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2092_);
                    crate::leanh::lean_inc(v_cache_2091_);
                    crate::leanh::lean_dec(v___x_2090_);
                    v___x_2096_ = crate::leanh::lean_box(0);
                    v_isShared_2097_ = v_isSharedCheck_2102_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2097_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2096_, 0, v_mctx_2089_);
                    v___x_2099_ = v___x_2096_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2101_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 0, v_mctx_2089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 1, v_cache_2091_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2101_,
                        2,
                        v_zetaDeltaFVarIds_2092_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 3, v_postponed_2093_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2101_, 4, v_diag_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2101_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2100_ = lean_st_ref_set(v___y_2004_, v___x_2099_);
                v_a_2036_ = v_fst_2088_;
                state = 7;
                continue;
            }
            19 => {
                v_snd_2106_ = crate::leanh::lean_ctor_get(v___y_2105_, 1);
                crate::leanh::lean_inc(v_snd_2106_);
                v_fst_2107_ = crate::leanh::lean_ctor_get(v___y_2105_, 0);
                crate::leanh::lean_inc(v_fst_2107_);
                crate::leanh::lean_dec_ref(v___y_2105_);
                v_mctx_2108_ = crate::leanh::lean_ctor_get(v_snd_2106_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2108_);
                crate::leanh::lean_dec(v_snd_2106_);
                v___x_2109_ = (crate::leanh::lean_unbox(v_fst_2107_) as u8);
                crate::leanh::lean_dec(v_fst_2107_);
                v_fst_2088_ = v___x_2109_;
                v_mctx_2089_ = v_mctx_2108_;
                state = 16;
                continue;
            }
            20 => {
                if v_fst_2115_ == 0 {
                    v___x_2117_ = l_Lean_Expr_hasFVar(v___y_2114_);
                    if v___x_2117_ == 0 {
                        v___x_2118_ = l_Lean_Expr_hasMVar(v___y_2114_);
                        if v___x_2118_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2114_);
                            crate::leanh::lean_dec_ref(v___y_2113_);
                            crate::leanh::lean_dec_ref(v___f_2111_);
                            v_fst_2065_ = v___x_2118_;
                            v_snd_2066_ = v_snd_2116_;
                            state = 12;
                            continue;
                        } else {
                            v___x_2119_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2111_,
                                    v___y_2113_,
                                    v___y_2114_,
                                    v_snd_2116_,
                                );
                            v___y_2083_ = v___x_2119_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_2120_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2111_,
                            v___y_2113_,
                            v___y_2114_,
                            v_snd_2116_,
                        );
                        v___y_2083_ = v___x_2120_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2114_);
                    crate::leanh::lean_dec_ref(v___y_2113_);
                    crate::leanh::lean_dec_ref(v___f_2111_);
                    v_fst_2065_ = v_fst_2115_;
                    v_snd_2066_ = v_snd_2116_;
                    state = 12;
                    continue;
                }
            }
            21 => {
                v_fst_2125_ = crate::leanh::lean_ctor_get(v___y_2124_, 0);
                crate::leanh::lean_inc(v_fst_2125_);
                v_snd_2126_ = crate::leanh::lean_ctor_get(v___y_2124_, 1);
                crate::leanh::lean_inc(v_snd_2126_);
                crate::leanh::lean_dec_ref(v___y_2124_);
                v___x_2127_ = (crate::leanh::lean_unbox(v_fst_2125_) as u8);
                crate::leanh::lean_dec(v_fst_2125_);
                v___y_2113_ = v___y_2122_;
                v___y_2114_ = v___y_2123_;
                v_fst_2115_ = v___x_2127_;
                v_snd_2116_ = v_snd_2126_;
                state = 20;
                continue;
            }
            22 => {
                v___x_2130_ = crate::leanh::lean_box((v___y_2129_) as usize);
                v___f_2131_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2131_, 0, v___x_2130_);
                if crate::leanh::lean_obj_tag(v_val_2024_) == 0 {
                    v_type_2132_ = crate::leanh::lean_ctor_get(v_val_2024_, 3);
                    v___x_2133_ = lean_st_ref_get(v___y_2004_);
                    v_mctx_2134_ = crate::leanh::lean_ctor_get(v___x_2133_, 0);
                    crate::leanh::lean_inc_ref_n(v_mctx_2134_, 2);
                    crate::leanh::lean_dec(v___x_2133_);
                    v___x_2135_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                    v___x_2136_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2136_, 0, v___x_2135_);
                    crate::leanh::lean_ctor_set(v___x_2136_, 1, v_mctx_2134_);
                    v___x_2137_ = l_Lean_Expr_hasFVar(v_type_2132_);
                    if v___x_2137_ == 0 {
                        v___x_2138_ = l_Lean_Expr_hasMVar(v_type_2132_);
                        if v___x_2138_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2136_, 2);
                            crate::leanh::lean_dec_ref(v___f_2131_);
                            crate::leanh::lean_dec_ref(v___f_2111_);
                            v_fst_2042_ = v___x_2138_;
                            v_mctx_2043_ = v_mctx_2134_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2134_);
                            crate::leanh::lean_inc_ref(v_type_2132_);
                            v___x_2139_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2111_,
                                    v___f_2131_,
                                    v_type_2132_,
                                    v___x_2136_,
                                );
                            v___y_2059_ = v___x_2139_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_2134_);
                        crate::leanh::lean_inc_ref(v_type_2132_);
                        v___x_2140_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2111_,
                            v___f_2131_,
                            v_type_2132_,
                            v___x_2136_,
                        );
                        v___y_2059_ = v___x_2140_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_nondep_2141_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2024_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_2141_ == 0 {
                        v_type_2142_ = crate::leanh::lean_ctor_get(v_val_2024_, 3);
                        v_value_2143_ = crate::leanh::lean_ctor_get(v_val_2024_, 4);
                        v___x_2144_ = lean_st_ref_get(v___y_2004_);
                        v_mctx_2145_ = crate::leanh::lean_ctor_get(v___x_2144_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_2145_);
                        crate::leanh::lean_dec(v___x_2144_);
                        v___x_2146_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2147_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2147_, 0, v___x_2146_);
                        crate::leanh::lean_ctor_set(v___x_2147_, 1, v_mctx_2145_);
                        v___x_2148_ = l_Lean_Expr_hasFVar(v_type_2142_);
                        if v___x_2148_ == 0 {
                            v___x_2149_ = l_Lean_Expr_hasMVar(v_type_2142_);
                            if v___x_2149_ == 0 {
                                crate::leanh::lean_inc_ref(v_value_2143_);
                                v___y_2113_ = v___f_2131_;
                                v___y_2114_ = v_value_2143_;
                                v_fst_2115_ = v___x_2149_;
                                v_snd_2116_ = v___x_2147_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_type_2142_);
                                crate::leanh::lean_inc_ref(v___f_2131_);
                                crate::leanh::lean_inc_ref(v___f_2111_);
                                v___x_2150_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2111_,
                                        v___f_2131_,
                                        v_type_2142_,
                                        v___x_2147_,
                                    );
                                crate::leanh::lean_inc_ref(v_value_2143_);
                                v___y_2122_ = v___f_2131_;
                                v___y_2123_ = v_value_2143_;
                                v___y_2124_ = v___x_2150_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_type_2142_);
                            crate::leanh::lean_inc_ref(v___f_2131_);
                            crate::leanh::lean_inc_ref(v___f_2111_);
                            v___x_2151_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2111_,
                                    v___f_2131_,
                                    v_type_2142_,
                                    v___x_2147_,
                                );
                            crate::leanh::lean_inc_ref(v_value_2143_);
                            v___y_2122_ = v___f_2131_;
                            v___y_2123_ = v_value_2143_;
                            v___y_2124_ = v___x_2151_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_type_2152_ = crate::leanh::lean_ctor_get(v_val_2024_, 3);
                        v___x_2153_ = lean_st_ref_get(v___y_2004_);
                        v_mctx_2154_ = crate::leanh::lean_ctor_get(v___x_2153_, 0);
                        crate::leanh::lean_inc_ref_n(v_mctx_2154_, 2);
                        crate::leanh::lean_dec(v___x_2153_);
                        v___x_2155_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2156_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2156_, 0, v___x_2155_);
                        crate::leanh::lean_ctor_set(v___x_2156_, 1, v_mctx_2154_);
                        v___x_2157_ = l_Lean_Expr_hasFVar(v_type_2152_);
                        if v___x_2157_ == 0 {
                            v___x_2158_ = l_Lean_Expr_hasMVar(v_type_2152_);
                            if v___x_2158_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2156_, 2);
                                crate::leanh::lean_dec_ref(v___f_2131_);
                                crate::leanh::lean_dec_ref(v___f_2111_);
                                v_fst_2088_ = v___x_2158_;
                                v_mctx_2089_ = v_mctx_2154_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_mctx_2154_);
                                crate::leanh::lean_inc_ref(v_type_2152_);
                                v___x_2159_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2111_,
                                        v___f_2131_,
                                        v_type_2152_,
                                        v___x_2156_,
                                    );
                                v___y_2105_ = v___x_2159_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2154_);
                            crate::leanh::lean_inc_ref(v_type_2152_);
                            v___x_2160_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2111_,
                                    v___f_2131_,
                                    v_type_2152_,
                                    v___x_2156_,
                                );
                            v___y_2105_ = v___x_2160_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            23 => {
                if v___y_2162_ == 0 {
                    if v_ignoreLetDecls_1997_ == 0 {
                        crate::leanh::lean_del_object(v___x_2028_);
                        v___y_2129_ = v_ignoreLetDecls_1997_;
                        state = 22;
                        continue;
                    } else {
                        v___x_2163_ = l_Lean_LocalDecl_isLet(v_val_2024_, v___y_2162_);
                        if v___x_2163_ == 0 {
                            crate::leanh::lean_del_object(v___x_2028_);
                            v___y_2129_ = v___x_2163_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_2111_);
                            crate::leanh::lean_dec(v___x_2034_);
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2111_);
                    crate::leanh::lean_dec(v___x_2034_);
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___boxed(
    mut v_ignoreLetDecls_2171_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2172_: *mut crate::leanh::LeanObject,
    mut v_as_2173_: *mut crate::leanh::LeanObject,
    mut v_sz_2174_: *mut crate::leanh::LeanObject,
    mut v_i_2175_: *mut crate::leanh::LeanObject,
    mut v_b_2176_: *mut crate::leanh::LeanObject,
    mut v___y_2177_: *mut crate::leanh::LeanObject,
    mut v___y_2178_: *mut crate::leanh::LeanObject,
    mut v___y_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2182_: u8 = 0;
    let mut v_sz_boxed_2183_: usize = 0;
    let mut v_i_boxed_2184_: usize = 0;
    let mut v_res_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2182_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2171_) as u8);
    v_sz_boxed_2183_ = crate::leanh::lean_unbox_usize(v_sz_2174_);
    crate::leanh::lean_dec(v_sz_2174_);
    v_i_boxed_2184_ = crate::leanh::lean_unbox_usize(v_i_2175_);
    crate::leanh::lean_dec(v_i_2175_);
    v_res_2185_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_boxed_2182_, v_forbidden_2172_, v_as_2173_, v_sz_boxed_2183_, v_i_boxed_2184_, v_b_2176_, v___y_2177_, v___y_2178_, v___y_2179_, v___y_2180_);
    crate::leanh::lean_dec(v___y_2180_);
    crate::leanh::lean_dec_ref(v___y_2179_);
    crate::leanh::lean_dec(v___y_2178_);
    crate::leanh::lean_dec_ref(v___y_2177_);
    crate::leanh::lean_dec_ref(v_as_2173_);
    crate::leanh::lean_dec(v_forbidden_2172_);
    return v_res_2185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_ignoreLetDecls_2186_: u8,
    mut v_forbidden_2187_: *mut crate::leanh::LeanObject,
    mut v_as_2188_: *mut crate::leanh::LeanObject,
    mut v_sz_2189_: usize,
    mut v_i_2190_: usize,
    mut v_b_2191_: *mut crate::leanh::LeanObject,
    mut v___y_2192_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2194_: u8 = 0;
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2199_: u8 = 0;
    let mut v___x_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: usize = 0;
    let mut v___x_2206_: usize = 0;
    let mut v_reuseFailAlloc_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2228_: u8 = 0;
    let mut v_mctx_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2237_: u8 = 0;
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v_unused_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v_fst_2251_: u8 = 0;
    let mut v_snd_2252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2261_: u8 = 0;
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2266_: u8 = 0;
    let mut v_unused_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: u8 = 0;
    let mut v_fst_2274_: u8 = 0;
    let mut v_mctx_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2283_: u8 = 0;
    let mut v___x_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2288_: u8 = 0;
    let mut v_unused_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: u8 = 0;
    let mut v___x_2296_: u8 = 0;
    let mut v___f_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2301_: u8 = 0;
    let mut v_snd_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2303_: u8 = 0;
    let mut v___x_2304_: u8 = 0;
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: u8 = 0;
    let mut v___y_2315_: u8 = 0;
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v___x_2324_: u8 = 0;
    let mut v___x_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2327_: u8 = 0;
    let mut v_type_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: u8 = 0;
    let mut v___x_2335_: u8 = 0;
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: u8 = 0;
    let mut v___x_2344_: u8 = 0;
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2348_: u8 = 0;
    let mut v___x_2349_: u8 = 0;
    let mut v___x_2350_: u8 = 0;
    let mut v___x_2351_: u8 = 0;
    let mut v___x_2352_: u8 = 0;
    let mut v___x_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2354_: u8 = 0;
    let mut v_isSharedCheck_2355_: u8 = 0;
    let mut v_unused_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2194_ = lean_usize_dec_lt(v_i_2190_, v_sz_2189_);
                if v___x_2194_ == 0 {
                    v___x_2195_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2195_, 0, v_b_2191_);
                    return v___x_2195_;
                } else {
                    v_snd_2196_ = crate::leanh::lean_ctor_get(v_b_2191_, 1);
                    v_isSharedCheck_2355_ = (!crate::leanh::lean_is_exclusive(v_b_2191_)) as u8;
                    if v_isSharedCheck_2355_ == 0 {
                        v_unused_2356_ = crate::leanh::lean_ctor_get(v_b_2191_, 0);
                        crate::leanh::lean_dec(v_unused_2356_);
                        v___x_2198_ = v_b_2191_;
                        v_isShared_2199_ = v_isSharedCheck_2355_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2196_);
                        crate::leanh::lean_dec(v_b_2191_);
                        v___x_2198_ = crate::leanh::lean_box(0);
                        v_isShared_2199_ = v_isSharedCheck_2355_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2200_ = crate::leanh::lean_box(0);
                v_a_2209_ = lean_array_uget_borrowed(v_as_2188_, v_i_2190_);
                if crate::leanh::lean_obj_tag(v_a_2209_) == 0 {
                    v_a_2202_ = v_snd_2196_;
                    state = 2;
                    continue;
                } else {
                    v_val_2210_ = crate::leanh::lean_ctor_get(v_a_2209_, 0);
                    v_fst_2211_ = crate::leanh::lean_ctor_get(v_snd_2196_, 0);
                    v_snd_2212_ = crate::leanh::lean_ctor_get(v_snd_2196_, 1);
                    v_isSharedCheck_2354_ = (!crate::leanh::lean_is_exclusive(v_snd_2196_)) as u8;
                    if v_isSharedCheck_2354_ == 0 {
                        v___x_2214_ = v_snd_2196_;
                        v_isShared_2215_ = v_isSharedCheck_2354_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2212_);
                        crate::leanh::lean_inc(v_fst_2211_);
                        crate::leanh::lean_dec(v_snd_2196_);
                        v___x_2214_ = crate::leanh::lean_box(0);
                        v_isShared_2215_ = v_isSharedCheck_2354_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2199_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2198_, 1, v_a_2202_);
                    crate::leanh::lean_ctor_set(v___x_2198_, 0, v___x_2200_);
                    v___x_2204_ = v___x_2198_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2208_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 0, v___x_2200_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2208_, 1, v_a_2202_);
                    v___x_2204_ = v_reuseFailAlloc_2208_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2205_ = 1usize;
                v___x_2206_ = lean_usize_add(v_i_2190_, v___x_2205_);
                v_i_2190_ = v___x_2206_;
                v_b_2191_ = v___x_2204_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2220_ = l_Lean_LocalDecl_fvarId(v_val_2210_);
                v___x_2296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_2220_, v_forbidden_2187_);
                if v___x_2296_ == 0 {
                    crate::leanh::lean_inc(v_fst_2211_);
                    v___f_2297_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2297_, 0, v_fst_2211_);
                    v___x_2350_ = l_Lean_LocalDecl_isAuxDecl(v_val_2210_);
                    if v___x_2350_ == 0 {
                        v___x_2351_ = l_Lean_LocalDecl_binderInfo(v_val_2210_);
                        v___x_2352_ = l_Lean_BinderInfo_isInstImplicit(v___x_2351_);
                        v___y_2348_ = v___x_2352_;
                        state = 23;
                        continue;
                    } else {
                        v___y_2348_ = v___x_2350_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2220_);
                    crate::leanh::lean_del_object(v___x_2214_);
                    v___x_2353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2353_, 0, v_fst_2211_);
                    crate::leanh::lean_ctor_set(v___x_2353_, 1, v_snd_2212_);
                    v_a_2202_ = v___x_2353_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2215_ == 0 {
                    v___x_2218_ = v___x_2214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2219_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 0, v_fst_2211_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2219_, 1, v_snd_2212_);
                    v___x_2218_ = v_reuseFailAlloc_2219_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2202_ = v___x_2218_;
                state = 2;
                continue;
            }
            7 => {
                if v_a_2222_ == 0 {
                    crate::leanh::lean_dec(v___x_2220_);
                    v___x_2223_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2223_, 0, v_fst_2211_);
                    crate::leanh::lean_ctor_set(v___x_2223_, 1, v_snd_2212_);
                    v_a_2202_ = v___x_2223_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_2220_);
                    v___x_2224_ = l_Lean_FVarIdSet_insert(v_snd_2212_, v___x_2220_);
                    v___x_2225_ = l_Lean_FVarIdSet_insert(v_fst_2211_, v___x_2220_);
                    v___x_2226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2226_, 0, v___x_2225_);
                    crate::leanh::lean_ctor_set(v___x_2226_, 1, v___x_2224_);
                    v_a_2202_ = v___x_2226_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_2230_ = lean_st_ref_take(v___y_2192_);
                v_cache_2231_ = crate::leanh::lean_ctor_get(v___x_2230_, 1);
                v_zetaDeltaFVarIds_2232_ = crate::leanh::lean_ctor_get(v___x_2230_, 2);
                v_postponed_2233_ = crate::leanh::lean_ctor_get(v___x_2230_, 3);
                v_diag_2234_ = crate::leanh::lean_ctor_get(v___x_2230_, 4);
                v_isSharedCheck_2242_ = (!crate::leanh::lean_is_exclusive(v___x_2230_)) as u8;
                if v_isSharedCheck_2242_ == 0 {
                    v_unused_2243_ = crate::leanh::lean_ctor_get(v___x_2230_, 0);
                    crate::leanh::lean_dec(v_unused_2243_);
                    v___x_2236_ = v___x_2230_;
                    v_isShared_2237_ = v_isSharedCheck_2242_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2234_);
                    crate::leanh::lean_inc(v_postponed_2233_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2232_);
                    crate::leanh::lean_inc(v_cache_2231_);
                    crate::leanh::lean_dec(v___x_2230_);
                    v___x_2236_ = crate::leanh::lean_box(0);
                    v_isShared_2237_ = v_isSharedCheck_2242_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2237_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2236_, 0, v_mctx_2229_);
                    v___x_2239_ = v___x_2236_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_mctx_2229_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_cache_2231_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2241_,
                        2,
                        v_zetaDeltaFVarIds_2232_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 3, v_postponed_2233_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 4, v_diag_2234_);
                    v___x_2239_ = v_reuseFailAlloc_2241_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2240_ = lean_st_ref_set(v___y_2192_, v___x_2239_);
                v_a_2222_ = v_fst_2228_;
                state = 7;
                continue;
            }
            11 => {
                v_snd_2246_ = crate::leanh::lean_ctor_get(v___y_2245_, 1);
                crate::leanh::lean_inc(v_snd_2246_);
                v_fst_2247_ = crate::leanh::lean_ctor_get(v___y_2245_, 0);
                crate::leanh::lean_inc(v_fst_2247_);
                crate::leanh::lean_dec_ref(v___y_2245_);
                v_mctx_2248_ = crate::leanh::lean_ctor_get(v_snd_2246_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2248_);
                crate::leanh::lean_dec(v_snd_2246_);
                v___x_2249_ = (crate::leanh::lean_unbox(v_fst_2247_) as u8);
                crate::leanh::lean_dec(v_fst_2247_);
                v_fst_2228_ = v___x_2249_;
                v_mctx_2229_ = v_mctx_2248_;
                state = 8;
                continue;
            }
            12 => {
                v_mctx_2253_ = crate::leanh::lean_ctor_get(v_snd_2252_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2253_);
                crate::leanh::lean_dec_ref(v_snd_2252_);
                v___x_2254_ = lean_st_ref_take(v___y_2192_);
                v_cache_2255_ = crate::leanh::lean_ctor_get(v___x_2254_, 1);
                v_zetaDeltaFVarIds_2256_ = crate::leanh::lean_ctor_get(v___x_2254_, 2);
                v_postponed_2257_ = crate::leanh::lean_ctor_get(v___x_2254_, 3);
                v_diag_2258_ = crate::leanh::lean_ctor_get(v___x_2254_, 4);
                v_isSharedCheck_2266_ = (!crate::leanh::lean_is_exclusive(v___x_2254_)) as u8;
                if v_isSharedCheck_2266_ == 0 {
                    v_unused_2267_ = crate::leanh::lean_ctor_get(v___x_2254_, 0);
                    crate::leanh::lean_dec(v_unused_2267_);
                    v___x_2260_ = v___x_2254_;
                    v_isShared_2261_ = v_isSharedCheck_2266_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2258_);
                    crate::leanh::lean_inc(v_postponed_2257_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2256_);
                    crate::leanh::lean_inc(v_cache_2255_);
                    crate::leanh::lean_dec(v___x_2254_);
                    v___x_2260_ = crate::leanh::lean_box(0);
                    v_isShared_2261_ = v_isSharedCheck_2266_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2261_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2260_, 0, v_mctx_2253_);
                    v___x_2263_ = v___x_2260_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2265_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_mctx_2253_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 1, v_cache_2255_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2265_,
                        2,
                        v_zetaDeltaFVarIds_2256_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 3, v_postponed_2257_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2265_, 4, v_diag_2258_);
                    v___x_2263_ = v_reuseFailAlloc_2265_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2264_ = lean_st_ref_set(v___y_2192_, v___x_2263_);
                v_a_2222_ = v_fst_2251_;
                state = 7;
                continue;
            }
            15 => {
                v_fst_2270_ = crate::leanh::lean_ctor_get(v___y_2269_, 0);
                crate::leanh::lean_inc(v_fst_2270_);
                v_snd_2271_ = crate::leanh::lean_ctor_get(v___y_2269_, 1);
                crate::leanh::lean_inc(v_snd_2271_);
                crate::leanh::lean_dec_ref(v___y_2269_);
                v___x_2272_ = (crate::leanh::lean_unbox(v_fst_2270_) as u8);
                crate::leanh::lean_dec(v_fst_2270_);
                v_fst_2251_ = v___x_2272_;
                v_snd_2252_ = v_snd_2271_;
                state = 12;
                continue;
            }
            16 => {
                v___x_2276_ = lean_st_ref_take(v___y_2192_);
                v_cache_2277_ = crate::leanh::lean_ctor_get(v___x_2276_, 1);
                v_zetaDeltaFVarIds_2278_ = crate::leanh::lean_ctor_get(v___x_2276_, 2);
                v_postponed_2279_ = crate::leanh::lean_ctor_get(v___x_2276_, 3);
                v_diag_2280_ = crate::leanh::lean_ctor_get(v___x_2276_, 4);
                v_isSharedCheck_2288_ = (!crate::leanh::lean_is_exclusive(v___x_2276_)) as u8;
                if v_isSharedCheck_2288_ == 0 {
                    v_unused_2289_ = crate::leanh::lean_ctor_get(v___x_2276_, 0);
                    crate::leanh::lean_dec(v_unused_2289_);
                    v___x_2282_ = v___x_2276_;
                    v_isShared_2283_ = v_isSharedCheck_2288_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2280_);
                    crate::leanh::lean_inc(v_postponed_2279_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2278_);
                    crate::leanh::lean_inc(v_cache_2277_);
                    crate::leanh::lean_dec(v___x_2276_);
                    v___x_2282_ = crate::leanh::lean_box(0);
                    v_isShared_2283_ = v_isSharedCheck_2288_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2283_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2282_, 0, v_mctx_2275_);
                    v___x_2285_ = v___x_2282_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2287_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 0, v_mctx_2275_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 1, v_cache_2277_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2287_,
                        2,
                        v_zetaDeltaFVarIds_2278_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 3, v_postponed_2279_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2287_, 4, v_diag_2280_);
                    v___x_2285_ = v_reuseFailAlloc_2287_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2286_ = lean_st_ref_set(v___y_2192_, v___x_2285_);
                v_a_2222_ = v_fst_2274_;
                state = 7;
                continue;
            }
            19 => {
                v_snd_2292_ = crate::leanh::lean_ctor_get(v___y_2291_, 1);
                crate::leanh::lean_inc(v_snd_2292_);
                v_fst_2293_ = crate::leanh::lean_ctor_get(v___y_2291_, 0);
                crate::leanh::lean_inc(v_fst_2293_);
                crate::leanh::lean_dec_ref(v___y_2291_);
                v_mctx_2294_ = crate::leanh::lean_ctor_get(v_snd_2292_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2294_);
                crate::leanh::lean_dec(v_snd_2292_);
                v___x_2295_ = (crate::leanh::lean_unbox(v_fst_2293_) as u8);
                crate::leanh::lean_dec(v_fst_2293_);
                v_fst_2274_ = v___x_2295_;
                v_mctx_2275_ = v_mctx_2294_;
                state = 16;
                continue;
            }
            20 => {
                if v_fst_2301_ == 0 {
                    v___x_2303_ = l_Lean_Expr_hasFVar(v___y_2300_);
                    if v___x_2303_ == 0 {
                        v___x_2304_ = l_Lean_Expr_hasMVar(v___y_2300_);
                        if v___x_2304_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2300_);
                            crate::leanh::lean_dec_ref(v___y_2299_);
                            crate::leanh::lean_dec_ref(v___f_2297_);
                            v_fst_2251_ = v___x_2304_;
                            v_snd_2252_ = v_snd_2302_;
                            state = 12;
                            continue;
                        } else {
                            v___x_2305_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2297_,
                                    v___y_2299_,
                                    v___y_2300_,
                                    v_snd_2302_,
                                );
                            v___y_2269_ = v___x_2305_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_2306_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2297_,
                            v___y_2299_,
                            v___y_2300_,
                            v_snd_2302_,
                        );
                        v___y_2269_ = v___x_2306_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2300_);
                    crate::leanh::lean_dec_ref(v___y_2299_);
                    crate::leanh::lean_dec_ref(v___f_2297_);
                    v_fst_2251_ = v_fst_2301_;
                    v_snd_2252_ = v_snd_2302_;
                    state = 12;
                    continue;
                }
            }
            21 => {
                v_fst_2311_ = crate::leanh::lean_ctor_get(v___y_2310_, 0);
                crate::leanh::lean_inc(v_fst_2311_);
                v_snd_2312_ = crate::leanh::lean_ctor_get(v___y_2310_, 1);
                crate::leanh::lean_inc(v_snd_2312_);
                crate::leanh::lean_dec_ref(v___y_2310_);
                v___x_2313_ = (crate::leanh::lean_unbox(v_fst_2311_) as u8);
                crate::leanh::lean_dec(v_fst_2311_);
                v___y_2299_ = v___y_2308_;
                v___y_2300_ = v___y_2309_;
                v_fst_2301_ = v___x_2313_;
                v_snd_2302_ = v_snd_2312_;
                state = 20;
                continue;
            }
            22 => {
                v___x_2316_ = crate::leanh::lean_box((v___y_2315_) as usize);
                v___f_2317_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2317_, 0, v___x_2316_);
                if crate::leanh::lean_obj_tag(v_val_2210_) == 0 {
                    v_type_2318_ = crate::leanh::lean_ctor_get(v_val_2210_, 3);
                    v___x_2319_ = lean_st_ref_get(v___y_2192_);
                    v_mctx_2320_ = crate::leanh::lean_ctor_get(v___x_2319_, 0);
                    crate::leanh::lean_inc_ref_n(v_mctx_2320_, 2);
                    crate::leanh::lean_dec(v___x_2319_);
                    v___x_2321_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                    v___x_2322_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2322_, 0, v___x_2321_);
                    crate::leanh::lean_ctor_set(v___x_2322_, 1, v_mctx_2320_);
                    v___x_2323_ = l_Lean_Expr_hasFVar(v_type_2318_);
                    if v___x_2323_ == 0 {
                        v___x_2324_ = l_Lean_Expr_hasMVar(v_type_2318_);
                        if v___x_2324_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2322_, 2);
                            crate::leanh::lean_dec_ref(v___f_2317_);
                            crate::leanh::lean_dec_ref(v___f_2297_);
                            v_fst_2228_ = v___x_2324_;
                            v_mctx_2229_ = v_mctx_2320_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2320_);
                            crate::leanh::lean_inc_ref(v_type_2318_);
                            v___x_2325_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2297_,
                                    v___f_2317_,
                                    v_type_2318_,
                                    v___x_2322_,
                                );
                            v___y_2245_ = v___x_2325_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_2320_);
                        crate::leanh::lean_inc_ref(v_type_2318_);
                        v___x_2326_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2297_,
                            v___f_2317_,
                            v_type_2318_,
                            v___x_2322_,
                        );
                        v___y_2245_ = v___x_2326_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_nondep_2327_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2210_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_2327_ == 0 {
                        v_type_2328_ = crate::leanh::lean_ctor_get(v_val_2210_, 3);
                        v_value_2329_ = crate::leanh::lean_ctor_get(v_val_2210_, 4);
                        v___x_2330_ = lean_st_ref_get(v___y_2192_);
                        v_mctx_2331_ = crate::leanh::lean_ctor_get(v___x_2330_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_2331_);
                        crate::leanh::lean_dec(v___x_2330_);
                        v___x_2332_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2333_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2333_, 0, v___x_2332_);
                        crate::leanh::lean_ctor_set(v___x_2333_, 1, v_mctx_2331_);
                        v___x_2334_ = l_Lean_Expr_hasFVar(v_type_2328_);
                        if v___x_2334_ == 0 {
                            v___x_2335_ = l_Lean_Expr_hasMVar(v_type_2328_);
                            if v___x_2335_ == 0 {
                                crate::leanh::lean_inc_ref(v_value_2329_);
                                v___y_2299_ = v___f_2317_;
                                v___y_2300_ = v_value_2329_;
                                v_fst_2301_ = v___x_2335_;
                                v_snd_2302_ = v___x_2333_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_type_2328_);
                                crate::leanh::lean_inc_ref(v___f_2317_);
                                crate::leanh::lean_inc_ref(v___f_2297_);
                                v___x_2336_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2297_,
                                        v___f_2317_,
                                        v_type_2328_,
                                        v___x_2333_,
                                    );
                                crate::leanh::lean_inc_ref(v_value_2329_);
                                v___y_2308_ = v___f_2317_;
                                v___y_2309_ = v_value_2329_;
                                v___y_2310_ = v___x_2336_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_type_2328_);
                            crate::leanh::lean_inc_ref(v___f_2317_);
                            crate::leanh::lean_inc_ref(v___f_2297_);
                            v___x_2337_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2297_,
                                    v___f_2317_,
                                    v_type_2328_,
                                    v___x_2333_,
                                );
                            crate::leanh::lean_inc_ref(v_value_2329_);
                            v___y_2308_ = v___f_2317_;
                            v___y_2309_ = v_value_2329_;
                            v___y_2310_ = v___x_2337_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_type_2338_ = crate::leanh::lean_ctor_get(v_val_2210_, 3);
                        v___x_2339_ = lean_st_ref_get(v___y_2192_);
                        v_mctx_2340_ = crate::leanh::lean_ctor_get(v___x_2339_, 0);
                        crate::leanh::lean_inc_ref_n(v_mctx_2340_, 2);
                        crate::leanh::lean_dec(v___x_2339_);
                        v___x_2341_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2342_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2342_, 0, v___x_2341_);
                        crate::leanh::lean_ctor_set(v___x_2342_, 1, v_mctx_2340_);
                        v___x_2343_ = l_Lean_Expr_hasFVar(v_type_2338_);
                        if v___x_2343_ == 0 {
                            v___x_2344_ = l_Lean_Expr_hasMVar(v_type_2338_);
                            if v___x_2344_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2342_, 2);
                                crate::leanh::lean_dec_ref(v___f_2317_);
                                crate::leanh::lean_dec_ref(v___f_2297_);
                                v_fst_2274_ = v___x_2344_;
                                v_mctx_2275_ = v_mctx_2340_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_mctx_2340_);
                                crate::leanh::lean_inc_ref(v_type_2338_);
                                v___x_2345_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2297_,
                                        v___f_2317_,
                                        v_type_2338_,
                                        v___x_2342_,
                                    );
                                v___y_2291_ = v___x_2345_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2340_);
                            crate::leanh::lean_inc_ref(v_type_2338_);
                            v___x_2346_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2297_,
                                    v___f_2317_,
                                    v_type_2338_,
                                    v___x_2342_,
                                );
                            v___y_2291_ = v___x_2346_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            23 => {
                if v___y_2348_ == 0 {
                    if v_ignoreLetDecls_2186_ == 0 {
                        crate::leanh::lean_del_object(v___x_2214_);
                        v___y_2315_ = v_ignoreLetDecls_2186_;
                        state = 22;
                        continue;
                    } else {
                        v___x_2349_ = l_Lean_LocalDecl_isLet(v_val_2210_, v___y_2348_);
                        if v___x_2349_ == 0 {
                            crate::leanh::lean_del_object(v___x_2214_);
                            v___y_2315_ = v___x_2349_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_2297_);
                            crate::leanh::lean_dec(v___x_2220_);
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2297_);
                    crate::leanh::lean_dec(v___x_2220_);
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_ignoreLetDecls_2357_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2358_: *mut crate::leanh::LeanObject,
    mut v_as_2359_: *mut crate::leanh::LeanObject,
    mut v_sz_2360_: *mut crate::leanh::LeanObject,
    mut v_i_2361_: *mut crate::leanh::LeanObject,
    mut v_b_2362_: *mut crate::leanh::LeanObject,
    mut v___y_2363_: *mut crate::leanh::LeanObject,
    mut v___y_2364_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2365_: u8 = 0;
    let mut v_sz_boxed_2366_: usize = 0;
    let mut v_i_boxed_2367_: usize = 0;
    let mut v_res_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2365_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2357_) as u8);
    v_sz_boxed_2366_ = crate::leanh::lean_unbox_usize(v_sz_2360_);
    crate::leanh::lean_dec(v_sz_2360_);
    v_i_boxed_2367_ = crate::leanh::lean_unbox_usize(v_i_2361_);
    crate::leanh::lean_dec(v_i_2361_);
    v_res_2368_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_boxed_2365_, v_forbidden_2358_, v_as_2359_, v_sz_boxed_2366_, v_i_boxed_2367_, v_b_2362_, v___y_2363_);
    crate::leanh::lean_dec(v___y_2363_);
    crate::leanh::lean_dec_ref(v_as_2359_);
    crate::leanh::lean_dec(v_forbidden_2358_);
    return v_res_2368_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(
    mut v_ignoreLetDecls_2369_: u8,
    mut v_forbidden_2370_: *mut crate::leanh::LeanObject,
    mut v_as_2371_: *mut crate::leanh::LeanObject,
    mut v_sz_2372_: usize,
    mut v_i_2373_: usize,
    mut v_b_2374_: *mut crate::leanh::LeanObject,
    mut v___y_2375_: *mut crate::leanh::LeanObject,
    mut v___y_2376_: *mut crate::leanh::LeanObject,
    mut v___y_2377_: *mut crate::leanh::LeanObject,
    mut v___y_2378_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2385_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: usize = 0;
    let mut v___x_2392_: usize = 0;
    let mut v___x_2393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2401_: u8 = 0;
    let mut v___x_2404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2408_: u8 = 0;
    let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2414_: u8 = 0;
    let mut v_mctx_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2423_: u8 = 0;
    let mut v___x_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_unused_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u8 = 0;
    let mut v_fst_2437_: u8 = 0;
    let mut v_snd_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2447_: u8 = 0;
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_unused_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: u8 = 0;
    let mut v_fst_2460_: u8 = 0;
    let mut v_mctx_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_2464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2469_: u8 = 0;
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2474_: u8 = 0;
    let mut v_unused_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2481_: u8 = 0;
    let mut v___x_2482_: u8 = 0;
    let mut v___f_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2487_: u8 = 0;
    let mut v_snd_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: u8 = 0;
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: u8 = 0;
    let mut v___y_2501_: u8 = 0;
    let mut v___x_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: u8 = 0;
    let mut v___x_2510_: u8 = 0;
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_2513_: u8 = 0;
    let mut v_type_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: u8 = 0;
    let mut v___x_2521_: u8 = 0;
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2534_: u8 = 0;
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: u8 = 0;
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2540_: u8 = 0;
    let mut v_isSharedCheck_2541_: u8 = 0;
    let mut v_unused_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2380_ = lean_usize_dec_lt(v_i_2373_, v_sz_2372_);
                if v___x_2380_ == 0 {
                    v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2381_, 0, v_b_2374_);
                    return v___x_2381_;
                } else {
                    v_snd_2382_ = crate::leanh::lean_ctor_get(v_b_2374_, 1);
                    v_isSharedCheck_2541_ = (!crate::leanh::lean_is_exclusive(v_b_2374_)) as u8;
                    if v_isSharedCheck_2541_ == 0 {
                        v_unused_2542_ = crate::leanh::lean_ctor_get(v_b_2374_, 0);
                        crate::leanh::lean_dec(v_unused_2542_);
                        v___x_2384_ = v_b_2374_;
                        v_isShared_2385_ = v_isSharedCheck_2541_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2382_);
                        crate::leanh::lean_dec(v_b_2374_);
                        v___x_2384_ = crate::leanh::lean_box(0);
                        v_isShared_2385_ = v_isSharedCheck_2541_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2386_ = crate::leanh::lean_box(0);
                v_a_2395_ = lean_array_uget_borrowed(v_as_2371_, v_i_2373_);
                if crate::leanh::lean_obj_tag(v_a_2395_) == 0 {
                    v_a_2388_ = v_snd_2382_;
                    state = 2;
                    continue;
                } else {
                    v_val_2396_ = crate::leanh::lean_ctor_get(v_a_2395_, 0);
                    v_fst_2397_ = crate::leanh::lean_ctor_get(v_snd_2382_, 0);
                    v_snd_2398_ = crate::leanh::lean_ctor_get(v_snd_2382_, 1);
                    v_isSharedCheck_2540_ = (!crate::leanh::lean_is_exclusive(v_snd_2382_)) as u8;
                    if v_isSharedCheck_2540_ == 0 {
                        v___x_2400_ = v_snd_2382_;
                        v_isShared_2401_ = v_isSharedCheck_2540_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2398_);
                        crate::leanh::lean_inc(v_fst_2397_);
                        crate::leanh::lean_dec(v_snd_2382_);
                        v___x_2400_ = crate::leanh::lean_box(0);
                        v_isShared_2401_ = v_isSharedCheck_2540_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2385_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2384_, 1, v_a_2388_);
                    crate::leanh::lean_ctor_set(v___x_2384_, 0, v___x_2386_);
                    v___x_2390_ = v___x_2384_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2394_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 0, v___x_2386_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2394_, 1, v_a_2388_);
                    v___x_2390_ = v_reuseFailAlloc_2394_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2391_ = 1usize;
                v___x_2392_ = lean_usize_add(v_i_2373_, v___x_2391_);
                v___x_2393_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_2369_, v_forbidden_2370_, v_as_2371_, v_sz_2372_, v___x_2392_, v___x_2390_, v___y_2376_);
                return v___x_2393_;
            }
            4 => {
                v___x_2406_ = l_Lean_LocalDecl_fvarId(v_val_2396_);
                v___x_2482_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit_spec__0___redArg(v___x_2406_, v_forbidden_2370_);
                if v___x_2482_ == 0 {
                    crate::leanh::lean_inc(v_fst_2397_);
                    v___f_2483_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
                    crate::leanh::lean_closure_set(v___f_2483_, 0, v_fst_2397_);
                    v___x_2536_ = l_Lean_LocalDecl_isAuxDecl(v_val_2396_);
                    if v___x_2536_ == 0 {
                        v___x_2537_ = l_Lean_LocalDecl_binderInfo(v_val_2396_);
                        v___x_2538_ = l_Lean_BinderInfo_isInstImplicit(v___x_2537_);
                        v___y_2534_ = v___x_2538_;
                        state = 23;
                        continue;
                    } else {
                        v___y_2534_ = v___x_2536_;
                        state = 23;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2406_);
                    crate::leanh::lean_del_object(v___x_2400_);
                    v___x_2539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2539_, 0, v_fst_2397_);
                    crate::leanh::lean_ctor_set(v___x_2539_, 1, v_snd_2398_);
                    v_a_2388_ = v___x_2539_;
                    state = 2;
                    continue;
                }
            }
            5 => {
                if v_isShared_2401_ == 0 {
                    v___x_2404_ = v___x_2400_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2405_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_fst_2397_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2405_, 1, v_snd_2398_);
                    v___x_2404_ = v_reuseFailAlloc_2405_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_2388_ = v___x_2404_;
                state = 2;
                continue;
            }
            7 => {
                if v_a_2408_ == 0 {
                    crate::leanh::lean_dec(v___x_2406_);
                    v___x_2409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2409_, 0, v_fst_2397_);
                    crate::leanh::lean_ctor_set(v___x_2409_, 1, v_snd_2398_);
                    v_a_2388_ = v___x_2409_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v___x_2406_);
                    v___x_2410_ = l_Lean_FVarIdSet_insert(v_snd_2398_, v___x_2406_);
                    v___x_2411_ = l_Lean_FVarIdSet_insert(v_fst_2397_, v___x_2406_);
                    v___x_2412_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2412_, 0, v___x_2411_);
                    crate::leanh::lean_ctor_set(v___x_2412_, 1, v___x_2410_);
                    v_a_2388_ = v___x_2412_;
                    state = 2;
                    continue;
                }
            }
            8 => {
                v___x_2416_ = lean_st_ref_take(v___y_2376_);
                v_cache_2417_ = crate::leanh::lean_ctor_get(v___x_2416_, 1);
                v_zetaDeltaFVarIds_2418_ = crate::leanh::lean_ctor_get(v___x_2416_, 2);
                v_postponed_2419_ = crate::leanh::lean_ctor_get(v___x_2416_, 3);
                v_diag_2420_ = crate::leanh::lean_ctor_get(v___x_2416_, 4);
                v_isSharedCheck_2428_ = (!crate::leanh::lean_is_exclusive(v___x_2416_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v_unused_2429_ = crate::leanh::lean_ctor_get(v___x_2416_, 0);
                    crate::leanh::lean_dec(v_unused_2429_);
                    v___x_2422_ = v___x_2416_;
                    v_isShared_2423_ = v_isSharedCheck_2428_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2420_);
                    crate::leanh::lean_inc(v_postponed_2419_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2418_);
                    crate::leanh::lean_inc(v_cache_2417_);
                    crate::leanh::lean_dec(v___x_2416_);
                    v___x_2422_ = crate::leanh::lean_box(0);
                    v_isShared_2423_ = v_isSharedCheck_2428_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2423_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2422_, 0, v_mctx_2415_);
                    v___x_2425_ = v___x_2422_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_mctx_2415_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 1, v_cache_2417_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2427_,
                        2,
                        v_zetaDeltaFVarIds_2418_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 3, v_postponed_2419_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 4, v_diag_2420_);
                    v___x_2425_ = v_reuseFailAlloc_2427_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2426_ = lean_st_ref_set(v___y_2376_, v___x_2425_);
                v_a_2408_ = v_fst_2414_;
                state = 7;
                continue;
            }
            11 => {
                v_snd_2432_ = crate::leanh::lean_ctor_get(v___y_2431_, 1);
                crate::leanh::lean_inc(v_snd_2432_);
                v_fst_2433_ = crate::leanh::lean_ctor_get(v___y_2431_, 0);
                crate::leanh::lean_inc(v_fst_2433_);
                crate::leanh::lean_dec_ref(v___y_2431_);
                v_mctx_2434_ = crate::leanh::lean_ctor_get(v_snd_2432_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2434_);
                crate::leanh::lean_dec(v_snd_2432_);
                v___x_2435_ = (crate::leanh::lean_unbox(v_fst_2433_) as u8);
                crate::leanh::lean_dec(v_fst_2433_);
                v_fst_2414_ = v___x_2435_;
                v_mctx_2415_ = v_mctx_2434_;
                state = 8;
                continue;
            }
            12 => {
                v_mctx_2439_ = crate::leanh::lean_ctor_get(v_snd_2438_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2439_);
                crate::leanh::lean_dec_ref(v_snd_2438_);
                v___x_2440_ = lean_st_ref_take(v___y_2376_);
                v_cache_2441_ = crate::leanh::lean_ctor_get(v___x_2440_, 1);
                v_zetaDeltaFVarIds_2442_ = crate::leanh::lean_ctor_get(v___x_2440_, 2);
                v_postponed_2443_ = crate::leanh::lean_ctor_get(v___x_2440_, 3);
                v_diag_2444_ = crate::leanh::lean_ctor_get(v___x_2440_, 4);
                v_isSharedCheck_2452_ = (!crate::leanh::lean_is_exclusive(v___x_2440_)) as u8;
                if v_isSharedCheck_2452_ == 0 {
                    v_unused_2453_ = crate::leanh::lean_ctor_get(v___x_2440_, 0);
                    crate::leanh::lean_dec(v_unused_2453_);
                    v___x_2446_ = v___x_2440_;
                    v_isShared_2447_ = v_isSharedCheck_2452_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2444_);
                    crate::leanh::lean_inc(v_postponed_2443_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2442_);
                    crate::leanh::lean_inc(v_cache_2441_);
                    crate::leanh::lean_dec(v___x_2440_);
                    v___x_2446_ = crate::leanh::lean_box(0);
                    v_isShared_2447_ = v_isSharedCheck_2452_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2447_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2446_, 0, v_mctx_2439_);
                    v___x_2449_ = v___x_2446_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2451_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_mctx_2439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 1, v_cache_2441_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2451_,
                        2,
                        v_zetaDeltaFVarIds_2442_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 3, v_postponed_2443_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2451_, 4, v_diag_2444_);
                    v___x_2449_ = v_reuseFailAlloc_2451_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_2450_ = lean_st_ref_set(v___y_2376_, v___x_2449_);
                v_a_2408_ = v_fst_2437_;
                state = 7;
                continue;
            }
            15 => {
                v_fst_2456_ = crate::leanh::lean_ctor_get(v___y_2455_, 0);
                crate::leanh::lean_inc(v_fst_2456_);
                v_snd_2457_ = crate::leanh::lean_ctor_get(v___y_2455_, 1);
                crate::leanh::lean_inc(v_snd_2457_);
                crate::leanh::lean_dec_ref(v___y_2455_);
                v___x_2458_ = (crate::leanh::lean_unbox(v_fst_2456_) as u8);
                crate::leanh::lean_dec(v_fst_2456_);
                v_fst_2437_ = v___x_2458_;
                v_snd_2438_ = v_snd_2457_;
                state = 12;
                continue;
            }
            16 => {
                v___x_2462_ = lean_st_ref_take(v___y_2376_);
                v_cache_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 1);
                v_zetaDeltaFVarIds_2464_ = crate::leanh::lean_ctor_get(v___x_2462_, 2);
                v_postponed_2465_ = crate::leanh::lean_ctor_get(v___x_2462_, 3);
                v_diag_2466_ = crate::leanh::lean_ctor_get(v___x_2462_, 4);
                v_isSharedCheck_2474_ = (!crate::leanh::lean_is_exclusive(v___x_2462_)) as u8;
                if v_isSharedCheck_2474_ == 0 {
                    v_unused_2475_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                    crate::leanh::lean_dec(v_unused_2475_);
                    v___x_2468_ = v___x_2462_;
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 17;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_2466_);
                    crate::leanh::lean_inc(v_postponed_2465_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_2464_);
                    crate::leanh::lean_inc(v_cache_2463_);
                    crate::leanh::lean_dec(v___x_2462_);
                    v___x_2468_ = crate::leanh::lean_box(0);
                    v_isShared_2469_ = v_isSharedCheck_2474_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_2469_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2468_, 0, v_mctx_2461_);
                    v___x_2471_ = v___x_2468_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_2473_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_mctx_2461_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_cache_2463_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2473_,
                        2,
                        v_zetaDeltaFVarIds_2464_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 3, v_postponed_2465_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2473_, 4, v_diag_2466_);
                    v___x_2471_ = v_reuseFailAlloc_2473_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_2472_ = lean_st_ref_set(v___y_2376_, v___x_2471_);
                v_a_2408_ = v_fst_2460_;
                state = 7;
                continue;
            }
            19 => {
                v_snd_2478_ = crate::leanh::lean_ctor_get(v___y_2477_, 1);
                crate::leanh::lean_inc(v_snd_2478_);
                v_fst_2479_ = crate::leanh::lean_ctor_get(v___y_2477_, 0);
                crate::leanh::lean_inc(v_fst_2479_);
                crate::leanh::lean_dec_ref(v___y_2477_);
                v_mctx_2480_ = crate::leanh::lean_ctor_get(v_snd_2478_, 1);
                crate::leanh::lean_inc_ref(v_mctx_2480_);
                crate::leanh::lean_dec(v_snd_2478_);
                v___x_2481_ = (crate::leanh::lean_unbox(v_fst_2479_) as u8);
                crate::leanh::lean_dec(v_fst_2479_);
                v_fst_2460_ = v___x_2481_;
                v_mctx_2461_ = v_mctx_2480_;
                state = 16;
                continue;
            }
            20 => {
                if v_fst_2487_ == 0 {
                    v___x_2489_ = l_Lean_Expr_hasFVar(v___y_2486_);
                    if v___x_2489_ == 0 {
                        v___x_2490_ = l_Lean_Expr_hasMVar(v___y_2486_);
                        if v___x_2490_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_2486_);
                            crate::leanh::lean_dec_ref(v___y_2485_);
                            crate::leanh::lean_dec_ref(v___f_2483_);
                            v_fst_2437_ = v___x_2490_;
                            v_snd_2438_ = v_snd_2488_;
                            state = 12;
                            continue;
                        } else {
                            v___x_2491_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2483_,
                                    v___y_2485_,
                                    v___y_2486_,
                                    v_snd_2488_,
                                );
                            v___y_2455_ = v___x_2491_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_2492_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2483_,
                            v___y_2485_,
                            v___y_2486_,
                            v_snd_2488_,
                        );
                        v___y_2455_ = v___x_2492_;
                        state = 15;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_2486_);
                    crate::leanh::lean_dec_ref(v___y_2485_);
                    crate::leanh::lean_dec_ref(v___f_2483_);
                    v_fst_2437_ = v_fst_2487_;
                    v_snd_2438_ = v_snd_2488_;
                    state = 12;
                    continue;
                }
            }
            21 => {
                v_fst_2497_ = crate::leanh::lean_ctor_get(v___y_2496_, 0);
                crate::leanh::lean_inc(v_fst_2497_);
                v_snd_2498_ = crate::leanh::lean_ctor_get(v___y_2496_, 1);
                crate::leanh::lean_inc(v_snd_2498_);
                crate::leanh::lean_dec_ref(v___y_2496_);
                v___x_2499_ = (crate::leanh::lean_unbox(v_fst_2497_) as u8);
                crate::leanh::lean_dec(v_fst_2497_);
                v___y_2485_ = v___y_2494_;
                v___y_2486_ = v___y_2495_;
                v_fst_2487_ = v___x_2499_;
                v_snd_2488_ = v_snd_2498_;
                state = 20;
                continue;
            }
            22 => {
                v___x_2502_ = crate::leanh::lean_box((v___y_2501_) as usize);
                v___f_2503_ = crate::leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                crate::leanh::lean_closure_set(v___f_2503_, 0, v___x_2502_);
                if crate::leanh::lean_obj_tag(v_val_2396_) == 0 {
                    v_type_2504_ = crate::leanh::lean_ctor_get(v_val_2396_, 3);
                    v___x_2505_ = lean_st_ref_get(v___y_2376_);
                    v_mctx_2506_ = crate::leanh::lean_ctor_get(v___x_2505_, 0);
                    crate::leanh::lean_inc_ref_n(v_mctx_2506_, 2);
                    crate::leanh::lean_dec(v___x_2505_);
                    v___x_2507_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                    v___x_2508_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2508_, 0, v___x_2507_);
                    crate::leanh::lean_ctor_set(v___x_2508_, 1, v_mctx_2506_);
                    v___x_2509_ = l_Lean_Expr_hasFVar(v_type_2504_);
                    if v___x_2509_ == 0 {
                        v___x_2510_ = l_Lean_Expr_hasMVar(v_type_2504_);
                        if v___x_2510_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2508_, 2);
                            crate::leanh::lean_dec_ref(v___f_2503_);
                            crate::leanh::lean_dec_ref(v___f_2483_);
                            v_fst_2414_ = v___x_2510_;
                            v_mctx_2415_ = v_mctx_2506_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2506_);
                            crate::leanh::lean_inc_ref(v_type_2504_);
                            v___x_2511_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2483_,
                                    v___f_2503_,
                                    v_type_2504_,
                                    v___x_2508_,
                                );
                            v___y_2431_ = v___x_2511_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_mctx_2506_);
                        crate::leanh::lean_inc_ref(v_type_2504_);
                        v___x_2512_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_2483_,
                            v___f_2503_,
                            v_type_2504_,
                            v___x_2508_,
                        );
                        v___y_2431_ = v___x_2512_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_nondep_2513_ = crate::leanh::lean_ctor_get_uint8(
                        v_val_2396_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5) as u32,
                    );
                    if v_nondep_2513_ == 0 {
                        v_type_2514_ = crate::leanh::lean_ctor_get(v_val_2396_, 3);
                        v_value_2515_ = crate::leanh::lean_ctor_get(v_val_2396_, 4);
                        v___x_2516_ = lean_st_ref_get(v___y_2376_);
                        v_mctx_2517_ = crate::leanh::lean_ctor_get(v___x_2516_, 0);
                        crate::leanh::lean_inc_ref(v_mctx_2517_);
                        crate::leanh::lean_dec(v___x_2516_);
                        v___x_2518_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2519_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2519_, 0, v___x_2518_);
                        crate::leanh::lean_ctor_set(v___x_2519_, 1, v_mctx_2517_);
                        v___x_2520_ = l_Lean_Expr_hasFVar(v_type_2514_);
                        if v___x_2520_ == 0 {
                            v___x_2521_ = l_Lean_Expr_hasMVar(v_type_2514_);
                            if v___x_2521_ == 0 {
                                crate::leanh::lean_inc_ref(v_value_2515_);
                                v___y_2485_ = v___f_2503_;
                                v___y_2486_ = v_value_2515_;
                                v_fst_2487_ = v___x_2521_;
                                v_snd_2488_ = v___x_2519_;
                                state = 20;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_type_2514_);
                                crate::leanh::lean_inc_ref(v___f_2503_);
                                crate::leanh::lean_inc_ref(v___f_2483_);
                                v___x_2522_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2483_,
                                        v___f_2503_,
                                        v_type_2514_,
                                        v___x_2519_,
                                    );
                                crate::leanh::lean_inc_ref(v_value_2515_);
                                v___y_2494_ = v___f_2503_;
                                v___y_2495_ = v_value_2515_;
                                v___y_2496_ = v___x_2522_;
                                state = 21;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_type_2514_);
                            crate::leanh::lean_inc_ref(v___f_2503_);
                            crate::leanh::lean_inc_ref(v___f_2483_);
                            v___x_2523_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2483_,
                                    v___f_2503_,
                                    v_type_2514_,
                                    v___x_2519_,
                                );
                            crate::leanh::lean_inc_ref(v_value_2515_);
                            v___y_2494_ = v___f_2503_;
                            v___y_2495_ = v_value_2515_;
                            v___y_2496_ = v___x_2523_;
                            state = 21;
                            continue;
                        }
                    } else {
                        v_type_2524_ = crate::leanh::lean_ctor_get(v_val_2396_, 3);
                        v___x_2525_ = lean_st_ref_get(v___y_2376_);
                        v_mctx_2526_ = crate::leanh::lean_ctor_get(v___x_2525_, 0);
                        crate::leanh::lean_inc_ref_n(v_mctx_2526_, 2);
                        crate::leanh::lean_dec(v___x_2525_);
                        v___x_2527_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1_once), _init_l___private_Lean_Meta_GeneralizeVars_0__Lean_Meta_mkGeneralizationForbiddenSet_visit___closed__1);
                        v___x_2528_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2528_, 0, v___x_2527_);
                        crate::leanh::lean_ctor_set(v___x_2528_, 1, v_mctx_2526_);
                        v___x_2529_ = l_Lean_Expr_hasFVar(v_type_2524_);
                        if v___x_2529_ == 0 {
                            v___x_2530_ = l_Lean_Expr_hasMVar(v_type_2524_);
                            if v___x_2530_ == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_2528_, 2);
                                crate::leanh::lean_dec_ref(v___f_2503_);
                                crate::leanh::lean_dec_ref(v___f_2483_);
                                v_fst_2460_ = v___x_2530_;
                                v_mctx_2461_ = v_mctx_2526_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v_mctx_2526_);
                                crate::leanh::lean_inc_ref(v_type_2524_);
                                v___x_2531_ =
                                    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                        v___f_2483_,
                                        v___f_2503_,
                                        v_type_2524_,
                                        v___x_2528_,
                                    );
                                v___y_2477_ = v___x_2531_;
                                state = 19;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_mctx_2526_);
                            crate::leanh::lean_inc_ref(v_type_2524_);
                            v___x_2532_ =
                                l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                                    v___f_2483_,
                                    v___f_2503_,
                                    v_type_2524_,
                                    v___x_2528_,
                                );
                            v___y_2477_ = v___x_2532_;
                            state = 19;
                            continue;
                        }
                    }
                }
            }
            23 => {
                if v___y_2534_ == 0 {
                    if v_ignoreLetDecls_2369_ == 0 {
                        crate::leanh::lean_del_object(v___x_2400_);
                        v___y_2501_ = v_ignoreLetDecls_2369_;
                        state = 22;
                        continue;
                    } else {
                        v___x_2535_ = l_Lean_LocalDecl_isLet(v_val_2396_, v___y_2534_);
                        if v___x_2535_ == 0 {
                            crate::leanh::lean_del_object(v___x_2400_);
                            v___y_2501_ = v___x_2535_;
                            state = 22;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___f_2483_);
                            crate::leanh::lean_dec(v___x_2406_);
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___f_2483_);
                    crate::leanh::lean_dec(v___x_2406_);
                    state = 5;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2___boxed(
    mut v_ignoreLetDecls_2543_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2544_: *mut crate::leanh::LeanObject,
    mut v_as_2545_: *mut crate::leanh::LeanObject,
    mut v_sz_2546_: *mut crate::leanh::LeanObject,
    mut v_i_2547_: *mut crate::leanh::LeanObject,
    mut v_b_2548_: *mut crate::leanh::LeanObject,
    mut v___y_2549_: *mut crate::leanh::LeanObject,
    mut v___y_2550_: *mut crate::leanh::LeanObject,
    mut v___y_2551_: *mut crate::leanh::LeanObject,
    mut v___y_2552_: *mut crate::leanh::LeanObject,
    mut v___y_2553_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2554_: u8 = 0;
    let mut v_sz_boxed_2555_: usize = 0;
    let mut v_i_boxed_2556_: usize = 0;
    let mut v_res_2557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2554_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2543_) as u8);
    v_sz_boxed_2555_ = crate::leanh::lean_unbox_usize(v_sz_2546_);
    crate::leanh::lean_dec(v_sz_2546_);
    v_i_boxed_2556_ = crate::leanh::lean_unbox_usize(v_i_2547_);
    crate::leanh::lean_dec(v_i_2547_);
    v_res_2557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_boxed_2554_, v_forbidden_2544_, v_as_2545_, v_sz_boxed_2555_, v_i_boxed_2556_, v_b_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
    crate::leanh::lean_dec(v___y_2552_);
    crate::leanh::lean_dec_ref(v___y_2551_);
    crate::leanh::lean_dec(v___y_2550_);
    crate::leanh::lean_dec_ref(v___y_2549_);
    crate::leanh::lean_dec_ref(v_as_2545_);
    crate::leanh::lean_dec(v_forbidden_2544_);
    return v_res_2557_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(
    mut v_init_2558_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2559_: u8,
    mut v_forbidden_2560_: *mut crate::leanh::LeanObject,
    mut v_n_2561_: *mut crate::leanh::LeanObject,
    mut v_b_2562_: *mut crate::leanh::LeanObject,
    mut v___y_2563_: *mut crate::leanh::LeanObject,
    mut v___y_2564_: *mut crate::leanh::LeanObject,
    mut v___y_2565_: *mut crate::leanh::LeanObject,
    mut v___y_2566_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2571_: usize = 0;
    let mut v___x_2572_: usize = 0;
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2577_: u8 = 0;
    let mut v_fst_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_a_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2592_: u8 = 0;
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2596_: u8 = 0;
    let mut v_vs_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2600_: usize = 0;
    let mut v___x_2601_: usize = 0;
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2606_: u8 = 0;
    let mut v_fst_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut v_a_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2621_: u8 = 0;
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2625_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2561_) == 0 {
                    v_cs_2568_ = crate::leanh::lean_ctor_get(v_n_2561_, 0);
                    v___x_2569_ = crate::leanh::lean_box(0);
                    v___x_2570_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2570_, 0, v___x_2569_);
                    crate::leanh::lean_ctor_set(v___x_2570_, 1, v_b_2562_);
                    v_sz_2571_ = lean_array_size(v_cs_2568_);
                    v___x_2572_ = 0usize;
                    v___x_2573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_2558_, v_ignoreLetDecls_2559_, v_forbidden_2560_, v_cs_2568_, v_sz_2571_, v___x_2572_, v___x_2570_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
                    if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                        v_a_2574_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2588_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2588_ == 0 {
                            v___x_2576_ = v___x_2573_;
                            v_isShared_2577_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2574_);
                            crate::leanh::lean_dec(v___x_2573_);
                            v___x_2576_ = crate::leanh::lean_box(0);
                            v_isShared_2577_ = v_isSharedCheck_2588_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2589_ = crate::leanh::lean_ctor_get(v___x_2573_, 0);
                        v_isSharedCheck_2596_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2573_)) as u8;
                        if v_isSharedCheck_2596_ == 0 {
                            v___x_2591_ = v___x_2573_;
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2589_);
                            crate::leanh::lean_dec(v___x_2573_);
                            v___x_2591_ = crate::leanh::lean_box(0);
                            v_isShared_2592_ = v_isSharedCheck_2596_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2597_ = crate::leanh::lean_ctor_get(v_n_2561_, 0);
                    v___x_2598_ = crate::leanh::lean_box(0);
                    v___x_2599_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2599_, 0, v___x_2598_);
                    crate::leanh::lean_ctor_set(v___x_2599_, 1, v_b_2562_);
                    v_sz_2600_ = lean_array_size(v_vs_2597_);
                    v___x_2601_ = 0usize;
                    v___x_2602_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2(v_ignoreLetDecls_2559_, v_forbidden_2560_, v_vs_2597_, v_sz_2600_, v___x_2601_, v___x_2599_, v___y_2563_, v___y_2564_, v___y_2565_, v___y_2566_);
                    if crate::leanh::lean_obj_tag(v___x_2602_) == 0 {
                        v_a_2603_ = crate::leanh::lean_ctor_get(v___x_2602_, 0);
                        v_isSharedCheck_2617_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2602_)) as u8;
                        if v_isSharedCheck_2617_ == 0 {
                            v___x_2605_ = v___x_2602_;
                            v_isShared_2606_ = v_isSharedCheck_2617_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2603_);
                            crate::leanh::lean_dec(v___x_2602_);
                            v___x_2605_ = crate::leanh::lean_box(0);
                            v_isShared_2606_ = v_isSharedCheck_2617_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2618_ = crate::leanh::lean_ctor_get(v___x_2602_, 0);
                        v_isSharedCheck_2625_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2602_)) as u8;
                        if v_isSharedCheck_2625_ == 0 {
                            v___x_2620_ = v___x_2602_;
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2618_);
                            crate::leanh::lean_dec(v___x_2602_);
                            v___x_2620_ = crate::leanh::lean_box(0);
                            v_isShared_2621_ = v_isSharedCheck_2625_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2578_ = crate::leanh::lean_ctor_get(v_a_2574_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2578_) == 0 {
                    v_snd_2579_ = crate::leanh::lean_ctor_get(v_a_2574_, 1);
                    crate::leanh::lean_inc(v_snd_2579_);
                    crate::leanh::lean_dec(v_a_2574_);
                    v___x_2580_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2580_, 0, v_snd_2579_);
                    if v_isShared_2577_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2576_, 0, v___x_2580_);
                        v___x_2582_ = v___x_2576_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v___x_2580_);
                        v___x_2582_ = v_reuseFailAlloc_2583_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2578_);
                    crate::leanh::lean_dec(v_a_2574_);
                    v_val_2584_ = crate::leanh::lean_ctor_get(v_fst_2578_, 0);
                    crate::leanh::lean_inc(v_val_2584_);
                    crate::leanh::lean_dec_ref_known(v_fst_2578_, 1);
                    if v_isShared_2577_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2576_, 0, v_val_2584_);
                        v___x_2586_ = v___x_2576_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2587_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_val_2584_);
                        v___x_2586_ = v_reuseFailAlloc_2587_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2582_;
            }
            3 => {
                return v___x_2586_;
            }
            4 => {
                if v_isShared_2592_ == 0 {
                    v___x_2594_ = v___x_2591_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2595_, 0, v_a_2589_);
                    v___x_2594_ = v_reuseFailAlloc_2595_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2594_;
            }
            6 => {
                v_fst_2607_ = crate::leanh::lean_ctor_get(v_a_2603_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2607_) == 0 {
                    v_snd_2608_ = crate::leanh::lean_ctor_get(v_a_2603_, 1);
                    crate::leanh::lean_inc(v_snd_2608_);
                    crate::leanh::lean_dec(v_a_2603_);
                    v___x_2609_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2609_, 0, v_snd_2608_);
                    if v_isShared_2606_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2605_, 0, v___x_2609_);
                        v___x_2611_ = v___x_2605_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2612_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
                        v___x_2611_ = v_reuseFailAlloc_2612_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2607_);
                    crate::leanh::lean_dec(v_a_2603_);
                    v_val_2613_ = crate::leanh::lean_ctor_get(v_fst_2607_, 0);
                    crate::leanh::lean_inc(v_val_2613_);
                    crate::leanh::lean_dec_ref_known(v_fst_2607_, 1);
                    if v_isShared_2606_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2605_, 0, v_val_2613_);
                        v___x_2615_ = v___x_2605_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_val_2613_);
                        v___x_2615_ = v_reuseFailAlloc_2616_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2611_;
            }
            8 => {
                return v___x_2615_;
            }
            9 => {
                if v_isShared_2621_ == 0 {
                    v___x_2623_ = v___x_2620_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2624_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_a_2618_);
                    v___x_2623_ = v_reuseFailAlloc_2624_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2623_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(
    mut v_init_2626_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2627_: u8,
    mut v_forbidden_2628_: *mut crate::leanh::LeanObject,
    mut v_as_2629_: *mut crate::leanh::LeanObject,
    mut v_sz_2630_: usize,
    mut v_i_2631_: usize,
    mut v_b_2632_: *mut crate::leanh::LeanObject,
    mut v___y_2633_: *mut crate::leanh::LeanObject,
    mut v___y_2634_: *mut crate::leanh::LeanObject,
    mut v___y_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2643_: u8 = 0;
    let mut v_a_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2649_: u8 = 0;
    let mut v___x_2650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: usize = 0;
    let mut v___x_2662_: usize = 0;
    let mut v_reuseFailAlloc_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2665_: u8 = 0;
    let mut v_a_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2669_: u8 = 0;
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2673_: u8 = 0;
    let mut v_isSharedCheck_2674_: u8 = 0;
    let mut v_unused_2675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2638_ = lean_usize_dec_lt(v_i_2631_, v_sz_2630_);
                if v___x_2638_ == 0 {
                    v___x_2639_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2639_, 0, v_b_2632_);
                    return v___x_2639_;
                } else {
                    v_snd_2640_ = crate::leanh::lean_ctor_get(v_b_2632_, 1);
                    v_isSharedCheck_2674_ = (!crate::leanh::lean_is_exclusive(v_b_2632_)) as u8;
                    if v_isSharedCheck_2674_ == 0 {
                        v_unused_2675_ = crate::leanh::lean_ctor_get(v_b_2632_, 0);
                        crate::leanh::lean_dec(v_unused_2675_);
                        v___x_2642_ = v_b_2632_;
                        v_isShared_2643_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2640_);
                        crate::leanh::lean_dec(v_b_2632_);
                        v___x_2642_ = crate::leanh::lean_box(0);
                        v_isShared_2643_ = v_isSharedCheck_2674_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2644_ = lean_array_uget_borrowed(v_as_2629_, v_i_2631_);
                crate::leanh::lean_inc(v_snd_2640_);
                v___x_2645_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_2626_, v_ignoreLetDecls_2627_, v_forbidden_2628_, v_a_2644_, v_snd_2640_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_);
                if crate::leanh::lean_obj_tag(v___x_2645_) == 0 {
                    v_a_2646_ = crate::leanh::lean_ctor_get(v___x_2645_, 0);
                    v_isSharedCheck_2665_ = (!crate::leanh::lean_is_exclusive(v___x_2645_)) as u8;
                    if v_isSharedCheck_2665_ == 0 {
                        v___x_2648_ = v___x_2645_;
                        v_isShared_2649_ = v_isSharedCheck_2665_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2646_);
                        crate::leanh::lean_dec(v___x_2645_);
                        v___x_2648_ = crate::leanh::lean_box(0);
                        v_isShared_2649_ = v_isSharedCheck_2665_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2642_);
                    crate::leanh::lean_dec(v_snd_2640_);
                    v_a_2666_ = crate::leanh::lean_ctor_get(v___x_2645_, 0);
                    v_isSharedCheck_2673_ = (!crate::leanh::lean_is_exclusive(v___x_2645_)) as u8;
                    if v_isSharedCheck_2673_ == 0 {
                        v___x_2668_ = v___x_2645_;
                        v_isShared_2669_ = v_isSharedCheck_2673_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2666_);
                        crate::leanh::lean_dec(v___x_2645_);
                        v___x_2668_ = crate::leanh::lean_box(0);
                        v_isShared_2669_ = v_isSharedCheck_2673_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2646_) == 0 {
                    v___x_2650_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2650_, 0, v_a_2646_);
                    if v_isShared_2643_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2650_);
                        v___x_2652_ = v___x_2642_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2656_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v___x_2650_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_snd_2640_);
                        v___x_2652_ = v_reuseFailAlloc_2656_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2648_);
                    crate::leanh::lean_dec(v_snd_2640_);
                    v_a_2657_ = crate::leanh::lean_ctor_get(v_a_2646_, 0);
                    crate::leanh::lean_inc(v_a_2657_);
                    crate::leanh::lean_dec_ref_known(v_a_2646_, 1);
                    v___x_2658_ = crate::leanh::lean_box(0);
                    if v_isShared_2643_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2642_, 1, v_a_2657_);
                        crate::leanh::lean_ctor_set(v___x_2642_, 0, v___x_2658_);
                        v___x_2660_ = v___x_2642_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2664_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 0, v___x_2658_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2664_, 1, v_a_2657_);
                        v___x_2660_ = v_reuseFailAlloc_2664_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2649_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2648_, 0, v___x_2652_);
                    v___x_2654_ = v___x_2648_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2655_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2655_, 0, v___x_2652_);
                    v___x_2654_ = v_reuseFailAlloc_2655_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2654_;
            }
            5 => {
                v___x_2661_ = 1usize;
                v___x_2662_ = lean_usize_add(v_i_2631_, v___x_2661_);
                v_i_2631_ = v___x_2662_;
                v_b_2632_ = v___x_2660_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2669_ == 0 {
                    v___x_2671_ = v___x_2668_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2672_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_a_2666_);
                    v___x_2671_ = v_reuseFailAlloc_2672_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1___boxed(
    mut v_init_2676_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2677_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2678_: *mut crate::leanh::LeanObject,
    mut v_as_2679_: *mut crate::leanh::LeanObject,
    mut v_sz_2680_: *mut crate::leanh::LeanObject,
    mut v_i_2681_: *mut crate::leanh::LeanObject,
    mut v_b_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2688_: u8 = 0;
    let mut v_sz_boxed_2689_: usize = 0;
    let mut v_i_boxed_2690_: usize = 0;
    let mut v_res_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2688_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2677_) as u8);
    v_sz_boxed_2689_ = crate::leanh::lean_unbox_usize(v_sz_2680_);
    crate::leanh::lean_dec(v_sz_2680_);
    v_i_boxed_2690_ = crate::leanh::lean_unbox_usize(v_i_2681_);
    crate::leanh::lean_dec(v_i_2681_);
    v_res_2691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__1(v_init_2676_, v_ignoreLetDecls_boxed_2688_, v_forbidden_2678_, v_as_2679_, v_sz_boxed_2689_, v_i_boxed_2690_, v_b_2682_, v___y_2683_, v___y_2684_, v___y_2685_, v___y_2686_);
    crate::leanh::lean_dec(v___y_2686_);
    crate::leanh::lean_dec_ref(v___y_2685_);
    crate::leanh::lean_dec(v___y_2684_);
    crate::leanh::lean_dec_ref(v___y_2683_);
    crate::leanh::lean_dec_ref(v_as_2679_);
    crate::leanh::lean_dec(v_forbidden_2678_);
    crate::leanh::lean_dec_ref(v_init_2676_);
    return v_res_2691_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0___boxed(
    mut v_init_2692_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2693_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2694_: *mut crate::leanh::LeanObject,
    mut v_n_2695_: *mut crate::leanh::LeanObject,
    mut v_b_2696_: *mut crate::leanh::LeanObject,
    mut v___y_2697_: *mut crate::leanh::LeanObject,
    mut v___y_2698_: *mut crate::leanh::LeanObject,
    mut v___y_2699_: *mut crate::leanh::LeanObject,
    mut v___y_2700_: *mut crate::leanh::LeanObject,
    mut v___y_2701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2702_: u8 = 0;
    let mut v_res_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2702_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2693_) as u8);
    v_res_2703_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_2692_, v_ignoreLetDecls_boxed_2702_, v_forbidden_2694_, v_n_2695_, v_b_2696_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_);
    crate::leanh::lean_dec(v___y_2700_);
    crate::leanh::lean_dec_ref(v___y_2699_);
    crate::leanh::lean_dec(v___y_2698_);
    crate::leanh::lean_dec_ref(v___y_2697_);
    crate::leanh::lean_dec_ref(v_n_2695_);
    crate::leanh::lean_dec(v_forbidden_2694_);
    crate::leanh::lean_dec_ref(v_init_2692_);
    return v_res_2703_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(
    mut v_ignoreLetDecls_2704_: u8,
    mut v_forbidden_2705_: *mut crate::leanh::LeanObject,
    mut v_t_2706_: *mut crate::leanh::LeanObject,
    mut v_init_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
    mut v___y_2709_: *mut crate::leanh::LeanObject,
    mut v___y_2710_: *mut crate::leanh::LeanObject,
    mut v___y_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v_a_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2727_: usize = 0;
    let mut v___x_2728_: usize = 0;
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2733_: u8 = 0;
    let mut v_fst_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2743_: u8 = 0;
    let mut v_a_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2747_: u8 = 0;
    let mut v___x_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2751_: u8 = 0;
    let mut v_isSharedCheck_2752_: u8 = 0;
    let mut v_a_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2713_ = crate::leanh::lean_ctor_get(v_t_2706_, 0);
                v_tail_2714_ = crate::leanh::lean_ctor_get(v_t_2706_, 1);
                crate::leanh::lean_inc_ref(v_init_2707_);
                v___x_2715_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0(v_init_2707_, v_ignoreLetDecls_2704_, v_forbidden_2705_, v_root_2713_, v_init_2707_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
                crate::leanh::lean_dec_ref(v_init_2707_);
                if crate::leanh::lean_obj_tag(v___x_2715_) == 0 {
                    v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2715_, 0);
                    v_isSharedCheck_2752_ = (!crate::leanh::lean_is_exclusive(v___x_2715_)) as u8;
                    if v_isSharedCheck_2752_ == 0 {
                        v___x_2718_ = v___x_2715_;
                        v_isShared_2719_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2716_);
                        crate::leanh::lean_dec(v___x_2715_);
                        v___x_2718_ = crate::leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2752_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2753_ = crate::leanh::lean_ctor_get(v___x_2715_, 0);
                    v_isSharedCheck_2760_ = (!crate::leanh::lean_is_exclusive(v___x_2715_)) as u8;
                    if v_isSharedCheck_2760_ == 0 {
                        v___x_2755_ = v___x_2715_;
                        v_isShared_2756_ = v_isSharedCheck_2760_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2753_);
                        crate::leanh::lean_dec(v___x_2715_);
                        v___x_2755_ = crate::leanh::lean_box(0);
                        v_isShared_2756_ = v_isSharedCheck_2760_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2716_) == 0 {
                    v_a_2720_ = crate::leanh::lean_ctor_get(v_a_2716_, 0);
                    crate::leanh::lean_inc(v_a_2720_);
                    crate::leanh::lean_dec_ref_known(v_a_2716_, 1);
                    if v_isShared_2719_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2718_, 0, v_a_2720_);
                        v___x_2722_ = v___x_2718_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2723_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2720_);
                        v___x_2722_ = v_reuseFailAlloc_2723_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2718_);
                    v_a_2724_ = crate::leanh::lean_ctor_get(v_a_2716_, 0);
                    crate::leanh::lean_inc(v_a_2724_);
                    crate::leanh::lean_dec_ref_known(v_a_2716_, 1);
                    v___x_2725_ = crate::leanh::lean_box(0);
                    v___x_2726_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2726_, 0, v___x_2725_);
                    crate::leanh::lean_ctor_set(v___x_2726_, 1, v_a_2724_);
                    v_sz_2727_ = lean_array_size(v_tail_2714_);
                    v___x_2728_ = 0usize;
                    v___x_2729_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1(v_ignoreLetDecls_2704_, v_forbidden_2705_, v_tail_2714_, v_sz_2727_, v___x_2728_, v___x_2726_, v___y_2708_, v___y_2709_, v___y_2710_, v___y_2711_);
                    if crate::leanh::lean_obj_tag(v___x_2729_) == 0 {
                        v_a_2730_ = crate::leanh::lean_ctor_get(v___x_2729_, 0);
                        v_isSharedCheck_2743_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2729_)) as u8;
                        if v_isSharedCheck_2743_ == 0 {
                            v___x_2732_ = v___x_2729_;
                            v_isShared_2733_ = v_isSharedCheck_2743_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2730_);
                            crate::leanh::lean_dec(v___x_2729_);
                            v___x_2732_ = crate::leanh::lean_box(0);
                            v_isShared_2733_ = v_isSharedCheck_2743_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2744_ = crate::leanh::lean_ctor_get(v___x_2729_, 0);
                        v_isSharedCheck_2751_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2729_)) as u8;
                        if v_isSharedCheck_2751_ == 0 {
                            v___x_2746_ = v___x_2729_;
                            v_isShared_2747_ = v_isSharedCheck_2751_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2744_);
                            crate::leanh::lean_dec(v___x_2729_);
                            v___x_2746_ = crate::leanh::lean_box(0);
                            v_isShared_2747_ = v_isSharedCheck_2751_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2722_;
            }
            3 => {
                v_fst_2734_ = crate::leanh::lean_ctor_get(v_a_2730_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2734_) == 0 {
                    v_snd_2735_ = crate::leanh::lean_ctor_get(v_a_2730_, 1);
                    crate::leanh::lean_inc(v_snd_2735_);
                    crate::leanh::lean_dec(v_a_2730_);
                    if v_isShared_2733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2732_, 0, v_snd_2735_);
                        v___x_2737_ = v___x_2732_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_snd_2735_);
                        v___x_2737_ = v_reuseFailAlloc_2738_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2734_);
                    crate::leanh::lean_dec(v_a_2730_);
                    v_val_2739_ = crate::leanh::lean_ctor_get(v_fst_2734_, 0);
                    crate::leanh::lean_inc(v_val_2739_);
                    crate::leanh::lean_dec_ref_known(v_fst_2734_, 1);
                    if v_isShared_2733_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2732_, 0, v_val_2739_);
                        v___x_2741_ = v___x_2732_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2742_, 0, v_val_2739_);
                        v___x_2741_ = v_reuseFailAlloc_2742_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2737_;
            }
            5 => {
                return v___x_2741_;
            }
            6 => {
                if v_isShared_2747_ == 0 {
                    v___x_2749_ = v___x_2746_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2750_, 0, v_a_2744_);
                    v___x_2749_ = v_reuseFailAlloc_2750_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2749_;
            }
            8 => {
                if v_isShared_2756_ == 0 {
                    v___x_2758_ = v___x_2755_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_a_2753_);
                    v___x_2758_ = v_reuseFailAlloc_2759_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0___boxed(
    mut v_ignoreLetDecls_2761_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2762_: *mut crate::leanh::LeanObject,
    mut v_t_2763_: *mut crate::leanh::LeanObject,
    mut v_init_2764_: *mut crate::leanh::LeanObject,
    mut v___y_2765_: *mut crate::leanh::LeanObject,
    mut v___y_2766_: *mut crate::leanh::LeanObject,
    mut v___y_2767_: *mut crate::leanh::LeanObject,
    mut v___y_2768_: *mut crate::leanh::LeanObject,
    mut v___y_2769_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2770_: u8 = 0;
    let mut v_res_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2770_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2761_) as u8);
    v_res_2771_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(
        v_ignoreLetDecls_boxed_2770_,
        v_forbidden_2762_,
        v_t_2763_,
        v_init_2764_,
        v___y_2765_,
        v___y_2766_,
        v___y_2767_,
        v___y_2768_,
    );
    crate::leanh::lean_dec(v___y_2768_);
    crate::leanh::lean_dec_ref(v___y_2767_);
    crate::leanh::lean_dec(v___y_2766_);
    crate::leanh::lean_dec_ref(v___y_2765_);
    crate::leanh::lean_dec_ref(v_t_2763_);
    crate::leanh::lean_dec(v_forbidden_2762_);
    return v_res_2771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(
    mut v_as_2772_: *mut crate::leanh::LeanObject,
    mut v_i_2773_: usize,
    mut v_stop_2774_: usize,
    mut v_b_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: usize = 0;
    let mut v___x_2779_: usize = 0;
    let mut v___x_2781_: u8 = 0;
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: u8 = 0;
    let mut v___x_2784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2781_ = lean_usize_dec_eq(v_i_2773_, v_stop_2774_);
                if v___x_2781_ == 0 {
                    v___x_2782_ = lean_array_uget_borrowed(v_as_2772_, v_i_2773_);
                    v___x_2783_ = l_Lean_Expr_isFVar(v___x_2782_);
                    if v___x_2783_ == 0 {
                        v___y_2777_ = v_b_2775_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2784_ = l_Lean_Expr_fvarId_x21(v___x_2782_);
                        v___x_2785_ = l_Lean_FVarIdSet_insert(v_b_2775_, v___x_2784_);
                        v___y_2777_ = v___x_2785_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_2775_;
                }
            }
            1 => {
                v___x_2778_ = 1usize;
                v___x_2779_ = lean_usize_add(v_i_2773_, v___x_2778_);
                v_i_2773_ = v___x_2779_;
                v_b_2775_ = v___y_2777_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1___boxed(
    mut v_as_2786_: *mut crate::leanh::LeanObject,
    mut v_i_2787_: *mut crate::leanh::LeanObject,
    mut v_stop_2788_: *mut crate::leanh::LeanObject,
    mut v_b_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2790_: usize = 0;
    let mut v_stop_boxed_2791_: usize = 0;
    let mut v_res_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2790_ = crate::leanh::lean_unbox_usize(v_i_2787_);
    crate::leanh::lean_dec(v_i_2787_);
    v_stop_boxed_2791_ = crate::leanh::lean_unbox_usize(v_stop_2788_);
    crate::leanh::lean_dec(v_stop_2788_);
    v_res_2792_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_as_2786_, v_i_boxed_2790_, v_stop_boxed_2791_, v_b_2789_);
    crate::leanh::lean_dec_ref(v_as_2786_);
    return v_res_2792_;
}
pub unsafe fn l_Lean_Meta_getFVarSetToGeneralize(
    mut v_targets_2793_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2794_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2795_: u8,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
    mut v_a_2798_: *mut crate::leanh::LeanObject,
    mut v_a_2799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_r_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v_snd_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut v_a_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2820_: u8 = 0;
    let mut v___x_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2824_: u8 = 0;
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: u8 = 0;
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: usize = 0;
    let mut v___x_2830_: usize = 0;
    let mut v___x_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2832_: usize = 0;
    let mut v___x_2833_: usize = 0;
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_r_2801_ = crate::leanh::lean_box(1);
                v___x_2825_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2826_ = lean_array_get_size(v_targets_2793_);
                v___x_2827_ = lean_nat_dec_lt(v___x_2825_, v___x_2826_);
                if v___x_2827_ == 0 {
                    v___y_2803_ = v_r_2801_;
                    state = 1;
                    continue;
                } else {
                    v___x_2828_ = lean_nat_dec_le(v___x_2826_, v___x_2826_);
                    if v___x_2828_ == 0 {
                        if v___x_2827_ == 0 {
                            v___y_2803_ = v_r_2801_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2829_ = 0usize;
                            v___x_2830_ = lean_usize_of_nat(v___x_2826_);
                            v___x_2831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_2793_, v___x_2829_, v___x_2830_, v_r_2801_);
                            v___y_2803_ = v___x_2831_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2832_ = 0usize;
                        v___x_2833_ = lean_usize_of_nat(v___x_2826_);
                        v___x_2834_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Meta_getFVarSetToGeneralize_spec__1(v_targets_2793_, v___x_2832_, v___x_2833_, v_r_2801_);
                        v___y_2803_ = v___x_2834_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_lctx_2804_ = crate::leanh::lean_ctor_get(v_a_2796_, 2);
                v_decls_2805_ = crate::leanh::lean_ctor_get(v_lctx_2804_, 1);
                v___x_2806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2806_, 0, v___y_2803_);
                crate::leanh::lean_ctor_set(v___x_2806_, 1, v_r_2801_);
                v___x_2807_ =
                    l_Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0(
                        v_ignoreLetDecls_2795_,
                        v_forbidden_2794_,
                        v_decls_2805_,
                        v___x_2806_,
                        v_a_2796_,
                        v_a_2797_,
                        v_a_2798_,
                        v_a_2799_,
                    );
                if crate::leanh::lean_obj_tag(v___x_2807_) == 0 {
                    v_a_2808_ = crate::leanh::lean_ctor_get(v___x_2807_, 0);
                    v_isSharedCheck_2816_ = (!crate::leanh::lean_is_exclusive(v___x_2807_)) as u8;
                    if v_isSharedCheck_2816_ == 0 {
                        v___x_2810_ = v___x_2807_;
                        v_isShared_2811_ = v_isSharedCheck_2816_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2808_);
                        crate::leanh::lean_dec(v___x_2807_);
                        v___x_2810_ = crate::leanh::lean_box(0);
                        v_isShared_2811_ = v_isSharedCheck_2816_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2817_ = crate::leanh::lean_ctor_get(v___x_2807_, 0);
                    v_isSharedCheck_2824_ = (!crate::leanh::lean_is_exclusive(v___x_2807_)) as u8;
                    if v_isSharedCheck_2824_ == 0 {
                        v___x_2819_ = v___x_2807_;
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2817_);
                        crate::leanh::lean_dec(v___x_2807_);
                        v___x_2819_ = crate::leanh::lean_box(0);
                        v_isShared_2820_ = v_isSharedCheck_2824_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_2812_ = crate::leanh::lean_ctor_get(v_a_2808_, 1);
                crate::leanh::lean_inc(v_snd_2812_);
                crate::leanh::lean_dec(v_a_2808_);
                if v_isShared_2811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2810_, 0, v_snd_2812_);
                    v___x_2814_ = v___x_2810_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_snd_2812_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2814_;
            }
            4 => {
                if v_isShared_2820_ == 0 {
                    v___x_2822_ = v___x_2819_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2823_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2823_, 0, v_a_2817_);
                    v___x_2822_ = v_reuseFailAlloc_2823_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFVarSetToGeneralize___boxed(
    mut v_targets_2835_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2836_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2837_: *mut crate::leanh::LeanObject,
    mut v_a_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
    mut v_a_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2843_: u8 = 0;
    let mut v_res_2844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2843_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2837_) as u8);
    v_res_2844_ = l_Lean_Meta_getFVarSetToGeneralize(
        v_targets_2835_,
        v_forbidden_2836_,
        v_ignoreLetDecls_boxed_2843_,
        v_a_2838_,
        v_a_2839_,
        v_a_2840_,
        v_a_2841_,
    );
    crate::leanh::lean_dec(v_a_2841_);
    crate::leanh::lean_dec_ref(v_a_2840_);
    crate::leanh::lean_dec(v_a_2839_);
    crate::leanh::lean_dec_ref(v_a_2838_);
    crate::leanh::lean_dec(v_forbidden_2836_);
    crate::leanh::lean_dec_ref(v_targets_2835_);
    return v_res_2844_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(
    mut v_ignoreLetDecls_2845_: u8,
    mut v_forbidden_2846_: *mut crate::leanh::LeanObject,
    mut v_as_2847_: *mut crate::leanh::LeanObject,
    mut v_sz_2848_: usize,
    mut v_i_2849_: usize,
    mut v_b_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___redArg(v_ignoreLetDecls_2845_, v_forbidden_2846_, v_as_2847_, v_sz_2848_, v_i_2849_, v_b_2850_, v___y_2852_);
    return v___x_2856_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4___boxed(
    mut v_ignoreLetDecls_2857_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2858_: *mut crate::leanh::LeanObject,
    mut v_as_2859_: *mut crate::leanh::LeanObject,
    mut v_sz_2860_: *mut crate::leanh::LeanObject,
    mut v_i_2861_: *mut crate::leanh::LeanObject,
    mut v_b_2862_: *mut crate::leanh::LeanObject,
    mut v___y_2863_: *mut crate::leanh::LeanObject,
    mut v___y_2864_: *mut crate::leanh::LeanObject,
    mut v___y_2865_: *mut crate::leanh::LeanObject,
    mut v___y_2866_: *mut crate::leanh::LeanObject,
    mut v___y_2867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2868_: u8 = 0;
    let mut v_sz_boxed_2869_: usize = 0;
    let mut v_i_boxed_2870_: usize = 0;
    let mut v_res_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2868_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2857_) as u8);
    v_sz_boxed_2869_ = crate::leanh::lean_unbox_usize(v_sz_2860_);
    crate::leanh::lean_dec(v_sz_2860_);
    v_i_boxed_2870_ = crate::leanh::lean_unbox_usize(v_i_2861_);
    crate::leanh::lean_dec(v_i_2861_);
    v_res_2871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__1_spec__4(v_ignoreLetDecls_boxed_2868_, v_forbidden_2858_, v_as_2859_, v_sz_boxed_2869_, v_i_boxed_2870_, v_b_2862_, v___y_2863_, v___y_2864_, v___y_2865_, v___y_2866_);
    crate::leanh::lean_dec(v___y_2866_);
    crate::leanh::lean_dec_ref(v___y_2865_);
    crate::leanh::lean_dec(v___y_2864_);
    crate::leanh::lean_dec_ref(v___y_2863_);
    crate::leanh::lean_dec_ref(v_as_2859_);
    crate::leanh::lean_dec(v_forbidden_2858_);
    return v_res_2871_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(
    mut v_ignoreLetDecls_2872_: u8,
    mut v_forbidden_2873_: *mut crate::leanh::LeanObject,
    mut v_as_2874_: *mut crate::leanh::LeanObject,
    mut v_sz_2875_: usize,
    mut v_i_2876_: usize,
    mut v_b_2877_: *mut crate::leanh::LeanObject,
    mut v___y_2878_: *mut crate::leanh::LeanObject,
    mut v___y_2879_: *mut crate::leanh::LeanObject,
    mut v___y_2880_: *mut crate::leanh::LeanObject,
    mut v___y_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___redArg(v_ignoreLetDecls_2872_, v_forbidden_2873_, v_as_2874_, v_sz_2875_, v_i_2876_, v_b_2877_, v___y_2879_);
    return v___x_2883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_ignoreLetDecls_2884_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2885_: *mut crate::leanh::LeanObject,
    mut v_as_2886_: *mut crate::leanh::LeanObject,
    mut v_sz_2887_: *mut crate::leanh::LeanObject,
    mut v_i_2888_: *mut crate::leanh::LeanObject,
    mut v_b_2889_: *mut crate::leanh::LeanObject,
    mut v___y_2890_: *mut crate::leanh::LeanObject,
    mut v___y_2891_: *mut crate::leanh::LeanObject,
    mut v___y_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2895_: u8 = 0;
    let mut v_sz_boxed_2896_: usize = 0;
    let mut v_i_boxed_2897_: usize = 0;
    let mut v_res_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2895_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2884_) as u8);
    v_sz_boxed_2896_ = crate::leanh::lean_unbox_usize(v_sz_2887_);
    crate::leanh::lean_dec(v_sz_2887_);
    v_i_boxed_2897_ = crate::leanh::lean_unbox_usize(v_i_2888_);
    crate::leanh::lean_dec(v_i_2888_);
    v_res_2898_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_getFVarSetToGeneralize_spec__0_spec__0_spec__2_spec__4(v_ignoreLetDecls_boxed_2895_, v_forbidden_2885_, v_as_2886_, v_sz_boxed_2896_, v_i_boxed_2897_, v_b_2889_, v___y_2890_, v___y_2891_, v___y_2892_, v___y_2893_);
    crate::leanh::lean_dec(v___y_2893_);
    crate::leanh::lean_dec_ref(v___y_2892_);
    crate::leanh::lean_dec(v___y_2891_);
    crate::leanh::lean_dec_ref(v___y_2890_);
    crate::leanh::lean_dec_ref(v_as_2886_);
    crate::leanh::lean_dec(v_forbidden_2885_);
    return v_res_2898_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(
    mut v_init_2899_: *mut crate::leanh::LeanObject,
    mut v_x_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_k_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2900_) == 0 {
                    v_k_2901_ = crate::leanh::lean_ctor_get(v_x_2900_, 1);
                    crate::leanh::lean_inc(v_k_2901_);
                    v_l_2902_ = crate::leanh::lean_ctor_get(v_x_2900_, 3);
                    crate::leanh::lean_inc(v_l_2902_);
                    v_r_2903_ = crate::leanh::lean_ctor_get(v_x_2900_, 4);
                    crate::leanh::lean_inc(v_r_2903_);
                    crate::leanh::lean_dec_ref_known(v_x_2900_, 5);
                    v___x_2904_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_2899_, v_l_2902_);
                    v___x_2905_ = lean_array_push(v___x_2904_, v_k_2901_);
                    v_init_2899_ = v___x_2905_;
                    v_x_2900_ = v_r_2903_;
                    state = 0;
                    continue;
                } else {
                    return v_init_2899_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFVarsToGeneralize(
    mut v_targets_2907_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2908_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2909_: u8,
    mut v_a_2910_: *mut crate::leanh::LeanObject,
    mut v_a_2911_: *mut crate::leanh::LeanObject,
    mut v_a_2912_: *mut crate::leanh::LeanObject,
    mut v_a_2913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2929_: u8 = 0;
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2933_: u8 = 0;
    let mut v_a_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2941_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2915_ = l_Lean_Meta_mkGeneralizationForbiddenSet(
                    v_targets_2907_,
                    v_forbidden_2908_,
                    v_a_2910_,
                    v_a_2911_,
                    v_a_2912_,
                    v_a_2913_,
                );
                if crate::leanh::lean_obj_tag(v___x_2915_) == 0 {
                    v_a_2916_ = crate::leanh::lean_ctor_get(v___x_2915_, 0);
                    crate::leanh::lean_inc(v_a_2916_);
                    crate::leanh::lean_dec_ref_known(v___x_2915_, 1);
                    v___x_2917_ = l_Lean_Meta_getFVarSetToGeneralize(
                        v_targets_2907_,
                        v_a_2916_,
                        v_ignoreLetDecls_2909_,
                        v_a_2910_,
                        v_a_2911_,
                        v_a_2912_,
                        v_a_2913_,
                    );
                    crate::leanh::lean_dec(v_a_2916_);
                    if crate::leanh::lean_obj_tag(v___x_2917_) == 0 {
                        v_a_2918_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                        crate::leanh::lean_inc(v_a_2918_);
                        crate::leanh::lean_dec_ref_known(v___x_2917_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2918_) == 0 {
                            v_size_2924_ = crate::leanh::lean_ctor_get(v_a_2918_, 0);
                            crate::leanh::lean_inc(v_size_2924_);
                            v___y_2920_ = v_size_2924_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2925_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___y_2920_ = v___x_2925_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2926_ = crate::leanh::lean_ctor_get(v___x_2917_, 0);
                        v_isSharedCheck_2933_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2917_)) as u8;
                        if v_isSharedCheck_2933_ == 0 {
                            v___x_2928_ = v___x_2917_;
                            v_isShared_2929_ = v_isSharedCheck_2933_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2926_);
                            crate::leanh::lean_dec(v___x_2917_);
                            v___x_2928_ = crate::leanh::lean_box(0);
                            v_isShared_2929_ = v_isSharedCheck_2933_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v_a_2934_ = crate::leanh::lean_ctor_get(v___x_2915_, 0);
                    v_isSharedCheck_2941_ = (!crate::leanh::lean_is_exclusive(v___x_2915_)) as u8;
                    if v_isSharedCheck_2941_ == 0 {
                        v___x_2936_ = v___x_2915_;
                        v_isShared_2937_ = v_isSharedCheck_2941_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2934_);
                        crate::leanh::lean_dec(v___x_2915_);
                        v___x_2936_ = crate::leanh::lean_box(0);
                        v_isShared_2937_ = v_isSharedCheck_2941_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2921_ = lean_mk_empty_array_with_capacity(v___y_2920_);
                crate::leanh::lean_dec(v___y_2920_);
                v___x_2922_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v___x_2921_, v_a_2918_);
                v___x_2923_ = l_Lean_Meta_sortFVarIds___redArg(v___x_2922_, v_a_2910_);
                return v___x_2923_;
            }
            2 => {
                if v_isShared_2929_ == 0 {
                    v___x_2931_ = v___x_2928_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2932_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_a_2926_);
                    v___x_2931_ = v_reuseFailAlloc_2932_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2931_;
            }
            4 => {
                if v_isShared_2937_ == 0 {
                    v___x_2939_ = v___x_2936_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2940_, 0, v_a_2934_);
                    v___x_2939_ = v_reuseFailAlloc_2940_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2939_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_getFVarsToGeneralize___boxed(
    mut v_targets_2942_: *mut crate::leanh::LeanObject,
    mut v_forbidden_2943_: *mut crate::leanh::LeanObject,
    mut v_ignoreLetDecls_2944_: *mut crate::leanh::LeanObject,
    mut v_a_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_a_2947_: *mut crate::leanh::LeanObject,
    mut v_a_2948_: *mut crate::leanh::LeanObject,
    mut v_a_2949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ignoreLetDecls_boxed_2950_: u8 = 0;
    let mut v_res_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_ignoreLetDecls_boxed_2950_ = (crate::leanh::lean_unbox(v_ignoreLetDecls_2944_) as u8);
    v_res_2951_ = l_Lean_Meta_getFVarsToGeneralize(
        v_targets_2942_,
        v_forbidden_2943_,
        v_ignoreLetDecls_boxed_2950_,
        v_a_2945_,
        v_a_2946_,
        v_a_2947_,
        v_a_2948_,
    );
    crate::leanh::lean_dec(v_a_2948_);
    crate::leanh::lean_dec_ref(v_a_2947_);
    crate::leanh::lean_dec(v_a_2946_);
    crate::leanh::lean_dec_ref(v_a_2945_);
    crate::leanh::lean_dec_ref(v_targets_2942_);
    return v_res_2951_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0(
    mut v_init_2952_: *mut crate::leanh::LeanObject,
    mut v_t_2953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2954_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Meta_getFVarsToGeneralize_spec__0_spec__0(v_init_2952_, v_t_2953_);
    return v___x_2954_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_GeneralizeVars(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_GeneralizeVars(
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
pub unsafe fn initialize_Lean_Meta_GeneralizeVars(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_GeneralizeVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_GeneralizeVars(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_GeneralizeVars(builtin);
}

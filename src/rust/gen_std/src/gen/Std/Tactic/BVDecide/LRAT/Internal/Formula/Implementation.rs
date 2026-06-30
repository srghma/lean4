// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Internal.Formula.Implementation
// Imports: Std.Tactic.BVDecide.LRAT.Internal.Formula.Class
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_mk_array, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_range;
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Assignment::{
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment,
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment,
    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment,
    l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Clause::{
    l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg,
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce,
};
use crate::r#gen::Std::Tactic::BVDecide::LRAT::Internal::Formula::Class::{
    initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
    runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class,
};
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited(
    mut v_n_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1468_: u8 = 0;
    let mut v___x_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1467_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instInhabited___closed__0;
    v___x_1468_ = 3;
    v___x_1469_ = leanh::lean_box((v___x_1468_) as usize);
    v___x_1470_ = lean_mk_array(v_n_1466_, v___x_1469_);
    v___x_1471_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1471_, 0, v___x_1467_);
    leanh::lean_ctor_set(v___x_1471_, 1, v___x_1467_);
    leanh::lean_ctor_set(v___x_1471_, 2, v___x_1467_);
    leanh::lean_ctor_set(v___x_1471_, 3, v___x_1470_);
    return v___x_1471_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(
    mut v_a_1472_: *mut leanh::LeanObject,
    mut v_a_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1479_: u8 = 0;
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1486_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1472_) == 0 {
                    v___x_1474_ = l_List_reverse___redArg(v_a_1473_);
                    return v___x_1474_;
                } else {
                    v_head_1475_ = leanh::lean_ctor_get(v_a_1472_, 0);
                    v_tail_1476_ = leanh::lean_ctor_get(v_a_1472_, 1);
                    v_isSharedCheck_1486_ = (!leanh::lean_is_exclusive(v_a_1472_)) as u8;
                    if v_isSharedCheck_1486_ == 0 {
                        v___x_1478_ = v_a_1472_;
                        v_isShared_1479_ = v_isSharedCheck_1486_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1476_);
                        leanh::lean_inc(v_head_1475_);
                        leanh::lean_dec(v_a_1472_);
                        v___x_1478_ = leanh::lean_box(0);
                        v_isShared_1479_ = v_isSharedCheck_1486_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1480_ = leanh::lean_box(0);
                if v_isShared_1479_ == 0 {
                    leanh::lean_ctor_set(v___x_1478_, 1, v___x_1480_);
                    v___x_1482_ = v___x_1478_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1485_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 0, v_head_1475_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1485_, 1, v___x_1480_);
                    v___x_1482_ = v_reuseFailAlloc_1485_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1483_, 0, v___x_1482_);
                leanh::lean_ctor_set(v___x_1483_, 1, v_a_1473_);
                v_a_1472_ = v_tail_1476_;
                v_a_1473_ = v___x_1483_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_filterMapTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(
    mut v_a_1487_: *mut leanh::LeanObject,
    mut v_a_1488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1487_) == 0 {
                    v___x_1489_ = lean_array_to_list(v_a_1488_);
                    return v___x_1489_;
                } else {
                    v_head_1490_ = leanh::lean_ctor_get(v_a_1487_, 0);
                    if leanh::lean_obj_tag(v_head_1490_) == 0 {
                        v_tail_1491_ = leanh::lean_ctor_get(v_a_1487_, 1);
                        leanh::lean_inc(v_tail_1491_);
                        leanh::lean_dec_ref_known(v_a_1487_, 2);
                        v_a_1487_ = v_tail_1491_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc_ref(v_head_1490_);
                        v_tail_1493_ = leanh::lean_ctor_get(v_a_1487_, 1);
                        leanh::lean_inc(v_tail_1493_);
                        leanh::lean_dec_ref_known(v_a_1487_, 2);
                        v_val_1494_ = leanh::lean_ctor_get(v_head_1490_, 0);
                        leanh::lean_inc(v_val_1494_);
                        leanh::lean_dec_ref_known(v_head_1490_, 1);
                        v___x_1495_ = lean_array_push(v_a_1488_, v_val_1494_);
                        v_a_1487_ = v_tail_1493_;
                        v_a_1488_ = v___x_1495_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(
    mut v_n_1499_: *mut leanh::LeanObject,
    mut v_f_1500_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_1501_ = leanh::lean_ctor_get(v_f_1500_, 0);
    leanh::lean_inc_ref(v_clauses_1501_);
    v_rupUnits_1502_ = leanh::lean_ctor_get(v_f_1500_, 1);
    leanh::lean_inc_ref(v_rupUnits_1502_);
    v_ratUnits_1503_ = leanh::lean_ctor_get(v_f_1500_, 2);
    leanh::lean_inc_ref(v_ratUnits_1503_);
    leanh::lean_dec_ref(v_f_1500_);
    v___x_1504_ = lean_array_to_list(v_clauses_1501_);
    v___x_1505_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___closed__0;
    v___x_1506_ = l_List_filterMapTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__0(v___x_1504_, v___x_1505_);
    v___x_1507_ = lean_array_to_list(v_rupUnits_1502_);
    v___x_1508_ = leanh::lean_box(0);
    v___x_1509_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v___x_1507_, v___x_1508_);
    v___x_1510_ = l_List_appendTR___redArg(v___x_1506_, v___x_1509_);
    v___x_1511_ = lean_array_to_list(v_ratUnits_1503_);
    v___x_1512_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v___x_1511_, v___x_1508_);
    v___x_1513_ = l_List_appendTR___redArg(v___x_1510_, v___x_1512_);
    return v___x_1513_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList___boxed(
    mut v_n_1514_: *mut leanh::LeanObject,
    mut v_f_1515_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1516_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList(v_n_1514_, v_f_1515_);
    leanh::lean_dec(v_n_1514_);
    return v_res_1516_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(
    mut v_n_1517_: *mut leanh::LeanObject,
    mut v_a_1518_: *mut leanh::LeanObject,
    mut v_a_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___redArg(v_a_1518_, v_a_1519_);
    return v___x_1520_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1___boxed(
    mut v_n_1521_: *mut leanh::LeanObject,
    mut v_a_1522_: *mut leanh::LeanObject,
    mut v_a_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ =
        l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_toList_spec__1(
            v_n_1521_, v_a_1522_, v_a_1523_,
        );
    leanh::lean_dec(v_n_1521_);
    return v_res_1524_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(
    mut v_assignments_1525_: *mut leanh::LeanObject,
    mut v_cOpt_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_cOpt_1526_) == 0 {
        return v_assignments_1525_;
    } else {
        let mut v_val_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_1527_ = leanh::lean_ctor_get(v_cOpt_1526_, 0);
        if leanh::lean_obj_tag(v_val_1527_) == 1 {
            let mut v_tail_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_tail_1528_ = leanh::lean_ctor_get(v_val_1527_, 1);
            if leanh::lean_obj_tag(v_tail_1528_) == 0 {
                let mut v_head_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_snd_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1531_: u8 = 0;
                v_head_1529_ = leanh::lean_ctor_get(v_val_1527_, 0);
                v_snd_1530_ = leanh::lean_ctor_get(v_head_1529_, 1);
                v___x_1531_ = (leanh::lean_unbox(v_snd_1530_) as u8);
                if v___x_1531_ == 0 {
                    let mut v_fst_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1534_: u8 = 0;
                    v_fst_1532_ = leanh::lean_ctor_get(v_head_1529_, 0);
                    v___x_1533_ = lean_array_get_size(v_assignments_1525_);
                    v___x_1534_ = lean_nat_dec_lt(v_fst_1532_, v___x_1533_);
                    if v___x_1534_ == 0 {
                        return v_assignments_1525_;
                    } else {
                        let mut v_v_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_xs_x27_1537_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_1538_: u8 = 0;
                        v_v_1535_ = lean_array_fget(v_assignments_1525_, v_fst_1532_);
                        v___x_1536_ = leanh::lean_box(0);
                        v_xs_x27_1537_ =
                            lean_array_fset(v_assignments_1525_, v_fst_1532_, v___x_1536_);
                        v___x_1538_ = (leanh::lean_unbox(v_v_1535_) as u8);
                        match v___x_1538_ {
                            0 => {
                                let mut v___x_1539_: u8 = 0;
                                let mut v___x_1540_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1541_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v_v_1535_);
                                v___x_1539_ = 2;
                                v___x_1540_ = leanh::lean_box((v___x_1539_) as usize);
                                v___x_1541_ =
                                    lean_array_fset(v_xs_x27_1537_, v_fst_1532_, v___x_1540_);
                                return v___x_1541_;
                            }
                            3 => {
                                let mut v___x_1542_: u8 = 0;
                                let mut v___x_1543_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1544_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v_v_1535_);
                                v___x_1542_ = 1;
                                v___x_1543_ = leanh::lean_box((v___x_1542_) as usize);
                                v___x_1544_ =
                                    lean_array_fset(v_xs_x27_1537_, v_fst_1532_, v___x_1543_);
                                return v___x_1544_;
                            }
                            _ => {
                                let mut v___x_1545_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_1545_ =
                                    lean_array_fset(v_xs_x27_1537_, v_fst_1532_, v_v_1535_);
                                return v___x_1545_;
                            }
                        }
                    }
                } else {
                    let mut v_fst_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1548_: u8 = 0;
                    v_fst_1546_ = leanh::lean_ctor_get(v_head_1529_, 0);
                    v___x_1547_ = lean_array_get_size(v_assignments_1525_);
                    v___x_1548_ = lean_nat_dec_lt(v_fst_1546_, v___x_1547_);
                    if v___x_1548_ == 0 {
                        return v_assignments_1525_;
                    } else {
                        let mut v_v_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
                        let mut v_xs_x27_1551_: *mut leanh::LeanObject =
                            core::ptr::null_mut();
                        let mut v___x_1552_: u8 = 0;
                        v_v_1549_ = lean_array_fget(v_assignments_1525_, v_fst_1546_);
                        v___x_1550_ = leanh::lean_box(0);
                        v_xs_x27_1551_ =
                            lean_array_fset(v_assignments_1525_, v_fst_1546_, v___x_1550_);
                        v___x_1552_ = (leanh::lean_unbox(v_v_1549_) as u8);
                        match v___x_1552_ {
                            1 => {
                                let mut v___x_1553_: u8 = 0;
                                let mut v___x_1554_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1555_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v_v_1549_);
                                v___x_1553_ = 2;
                                v___x_1554_ = leanh::lean_box((v___x_1553_) as usize);
                                v___x_1555_ =
                                    lean_array_fset(v_xs_x27_1551_, v_fst_1546_, v___x_1554_);
                                return v___x_1555_;
                            }
                            3 => {
                                let mut v___x_1556_: u8 = 0;
                                let mut v___x_1557_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                let mut v___x_1558_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                leanh::lean_dec(v_v_1549_);
                                v___x_1556_ = 0;
                                v___x_1557_ = leanh::lean_box((v___x_1556_) as usize);
                                v___x_1558_ =
                                    lean_array_fset(v_xs_x27_1551_, v_fst_1546_, v___x_1557_);
                                return v___x_1558_;
                            }
                            _ => {
                                let mut v___x_1559_: *mut leanh::LeanObject =
                                    core::ptr::null_mut();
                                v___x_1559_ =
                                    lean_array_fset(v_xs_x27_1551_, v_fst_1546_, v_v_1549_);
                                return v___x_1559_;
                            }
                        }
                    }
                }
            } else {
                return v_assignments_1525_;
            }
        } else {
            return v_assignments_1525_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg___boxed(
    mut v_assignments_1560_: *mut leanh::LeanObject,
    mut v_cOpt_1561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1562_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(
        v_assignments_1560_,
        v_cOpt_1561_,
    );
    leanh::lean_dec(v_cOpt_1561_);
    return v_res_1562_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(
    mut v_n_1563_: *mut leanh::LeanObject,
    mut v_assignments_1564_: *mut leanh::LeanObject,
    mut v_cOpt_1565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1566_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(
        v_assignments_1564_,
        v_cOpt_1565_,
    );
    return v___x_1566_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___boxed(
    mut v_n_1567_: *mut leanh::LeanObject,
    mut v_assignments_1568_: *mut leanh::LeanObject,
    mut v_cOpt_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1570_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn(
        v_n_1567_,
        v_assignments_1568_,
        v_cOpt_1569_,
    );
    leanh::lean_dec(v_cOpt_1569_);
    leanh::lean_dec(v_n_1567_);
    return v_res_1570_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(
    mut v_as_1571_: *mut leanh::LeanObject,
    mut v_i_1572_: usize,
    mut v_stop_1573_: usize,
    mut v_b_1574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1575_: u8 = 0;
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: usize = 0;
    let mut v___x_1579_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1575_ = lean_usize_dec_eq(v_i_1572_, v_stop_1573_);
                if v___x_1575_ == 0 {
                    v___x_1576_ = lean_array_uget_borrowed(v_as_1571_, v_i_1572_);
                    v___x_1577_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray__fold__fn___redArg(v_b_1574_, v___x_1576_);
                    v___x_1578_ = 1usize;
                    v___x_1579_ = lean_usize_add(v_i_1572_, v___x_1578_);
                    v_i_1572_ = v___x_1579_;
                    v_b_1574_ = v___x_1577_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1574_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg___boxed(
    mut v_as_1581_: *mut leanh::LeanObject,
    mut v_i_1582_: *mut leanh::LeanObject,
    mut v_stop_1583_: *mut leanh::LeanObject,
    mut v_b_1584_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1585_: usize = 0;
    let mut v_stop_boxed_1586_: usize = 0;
    let mut v_res_1587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1585_ = leanh::lean_unbox_usize(v_i_1582_);
    leanh::lean_dec(v_i_1582_);
    v_stop_boxed_1586_ = leanh::lean_unbox_usize(v_stop_1583_);
    leanh::lean_dec(v_stop_1583_);
    v_res_1587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_as_1581_, v_i_boxed_1585_, v_stop_boxed_1586_, v_b_1584_);
    leanh::lean_dec_ref(v_as_1581_);
    return v_res_1587_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray(
    mut v_n_1590_: *mut leanh::LeanObject,
    mut v_clauses_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: u8 = 0;
    let mut v___x_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: u8 = 0;
    let mut v___x_1602_: u8 = 0;
    let mut v___x_1603_: usize = 0;
    let mut v___x_1604_: usize = 0;
    let mut v___x_1605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: usize = 0;
    let mut v___x_1607_: usize = 0;
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1596_ = 3;
                v___x_1597_ = leanh::lean_box((v___x_1596_) as usize);
                v___x_1598_ = lean_mk_array(v_n_1590_, v___x_1597_);
                v___x_1599_ = leanh::lean_unsigned_to_nat(0);
                v___x_1600_ = lean_array_get_size(v_clauses_1591_);
                v___x_1601_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
                if v___x_1601_ == 0 {
                    v___y_1593_ = v___x_1598_;
                    state = 1;
                    continue;
                } else {
                    v___x_1602_ = lean_nat_dec_le(v___x_1600_, v___x_1600_);
                    if v___x_1602_ == 0 {
                        if v___x_1601_ == 0 {
                            v___y_1593_ = v___x_1598_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1603_ = 0usize;
                            v___x_1604_ = lean_usize_of_nat(v___x_1600_);
                            v___x_1605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_clauses_1591_, v___x_1603_, v___x_1604_, v___x_1598_);
                            v___y_1593_ = v___x_1605_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1606_ = 0usize;
                        v___x_1607_ = lean_usize_of_nat(v___x_1600_);
                        v___x_1608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_clauses_1591_, v___x_1606_, v___x_1607_, v___x_1598_);
                        v___y_1593_ = v___x_1608_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1594_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
                v___x_1595_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1595_, 0, v_clauses_1591_);
                leanh::lean_ctor_set(v___x_1595_, 1, v___x_1594_);
                leanh::lean_ctor_set(v___x_1595_, 2, v___x_1594_);
                leanh::lean_ctor_set(v___x_1595_, 3, v___y_1593_);
                return v___x_1595_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(
    mut v_n_1609_: *mut leanh::LeanObject,
    mut v_as_1610_: *mut leanh::LeanObject,
    mut v_i_1611_: usize,
    mut v_stop_1612_: usize,
    mut v_b_1613_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___redArg(v_as_1610_, v_i_1611_, v_stop_1612_, v_b_1613_);
    return v___x_1614_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0___boxed(
    mut v_n_1615_: *mut leanh::LeanObject,
    mut v_as_1616_: *mut leanh::LeanObject,
    mut v_i_1617_: *mut leanh::LeanObject,
    mut v_stop_1618_: *mut leanh::LeanObject,
    mut v_b_1619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1620_: usize = 0;
    let mut v_stop_boxed_1621_: usize = 0;
    let mut v_res_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1620_ = leanh::lean_unbox_usize(v_i_1617_);
    leanh::lean_dec(v_i_1617_);
    v_stop_boxed_1621_ = leanh::lean_unbox_usize(v_stop_1618_);
    leanh::lean_dec(v_stop_1618_);
    v_res_1622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray_spec__0(v_n_1615_, v_as_1616_, v_i_boxed_1620_, v_stop_boxed_1621_, v_b_1619_);
    leanh::lean_dec_ref(v_as_1616_);
    leanh::lean_dec(v_n_1615_);
    return v_res_1622_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(
    mut v_f_1623_: *mut leanh::LeanObject,
    mut v_c_1624_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1631_: u8 = 0;
    let mut v___x_1633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: u8 = 0;
    let mut v_fst_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: u8 = 0;
    let mut v___x_1647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1652_: u8 = 0;
    let mut v___x_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: u8 = 0;
    let mut v___x_1658_: u8 = 0;
    let mut v___x_1659_: u8 = 0;
    let mut v_fst_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    let mut v___x_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1670_: u8 = 0;
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: u8 = 0;
    let mut v___x_1675_: u8 = 0;
    let mut v___x_1676_: u8 = 0;
    let mut v___x_1677_: u8 = 0;
    let mut v_isSharedCheck_1678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_1625_ = leanh::lean_ctor_get(v_f_1623_, 0);
                v_rupUnits_1626_ = leanh::lean_ctor_get(v_f_1623_, 1);
                v_ratUnits_1627_ = leanh::lean_ctor_get(v_f_1623_, 2);
                v_assignments_1628_ = leanh::lean_ctor_get(v_f_1623_, 3);
                v_isSharedCheck_1678_ = (!leanh::lean_is_exclusive(v_f_1623_)) as u8;
                if v_isSharedCheck_1678_ == 0 {
                    v___x_1630_ = v_f_1623_;
                    v_isShared_1631_ = v_isSharedCheck_1678_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_1628_);
                    leanh::lean_inc(v_ratUnits_1627_);
                    leanh::lean_inc(v_rupUnits_1626_);
                    leanh::lean_inc(v_clauses_1625_);
                    leanh::lean_dec(v_f_1623_);
                    v___x_1630_ = leanh::lean_box(0);
                    v_isShared_1631_ = v_isSharedCheck_1678_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_c_1624_) == 1 {
                    v_tail_1638_ = leanh::lean_ctor_get(v_c_1624_, 1);
                    if leanh::lean_obj_tag(v_tail_1638_) == 0 {
                        leanh::lean_del_object(v___x_1630_);
                        v_head_1639_ = leanh::lean_ctor_get(v_c_1624_, 0);
                        v_snd_1640_ = leanh::lean_ctor_get(v_head_1639_, 1);
                        v___x_1641_ = (leanh::lean_unbox(v_snd_1640_) as u8);
                        if v___x_1641_ == 0 {
                            v_fst_1642_ = leanh::lean_ctor_get(v_head_1639_, 0);
                            leanh::lean_inc(v_fst_1642_);
                            v___x_1643_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1643_, 0, v_c_1624_);
                            v___x_1644_ = lean_array_push(v_clauses_1625_, v___x_1643_);
                            v___x_1645_ = lean_array_get_size(v_assignments_1628_);
                            v___x_1646_ = lean_nat_dec_lt(v_fst_1642_, v___x_1645_);
                            if v___x_1646_ == 0 {
                                leanh::lean_dec(v_fst_1642_);
                                v___x_1647_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_1647_, 0, v___x_1644_);
                                leanh::lean_ctor_set(v___x_1647_, 1, v_rupUnits_1626_);
                                leanh::lean_ctor_set(v___x_1647_, 2, v_ratUnits_1627_);
                                leanh::lean_ctor_set(v___x_1647_, 3, v_assignments_1628_);
                                return v___x_1647_;
                            } else {
                                v_v_1648_ = lean_array_fget(v_assignments_1628_, v_fst_1642_);
                                v___x_1649_ = leanh::lean_box(0);
                                v_xs_x27_1650_ =
                                    lean_array_fset(v_assignments_1628_, v_fst_1642_, v___x_1649_);
                                v___x_1656_ = (leanh::lean_unbox(v_v_1648_) as u8);
                                match v___x_1656_ {
                                    0 => {
                                        leanh::lean_dec(v_v_1648_);
                                        v___x_1657_ = 2;
                                        v___y_1652_ = v___x_1657_;
                                        state = 4;
                                        continue;
                                    }
                                    3 => {
                                        leanh::lean_dec(v_v_1648_);
                                        v___x_1658_ = 1;
                                        v___y_1652_ = v___x_1658_;
                                        state = 4;
                                        continue;
                                    }
                                    _ => {
                                        v___x_1659_ = (leanh::lean_unbox(v_v_1648_) as u8);
                                        leanh::lean_dec(v_v_1648_);
                                        v___y_1652_ = v___x_1659_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            v_fst_1660_ = leanh::lean_ctor_get(v_head_1639_, 0);
                            leanh::lean_inc(v_fst_1660_);
                            v___x_1661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1661_, 0, v_c_1624_);
                            v___x_1662_ = lean_array_push(v_clauses_1625_, v___x_1661_);
                            v___x_1663_ = lean_array_get_size(v_assignments_1628_);
                            v___x_1664_ = lean_nat_dec_lt(v_fst_1660_, v___x_1663_);
                            if v___x_1664_ == 0 {
                                leanh::lean_dec(v_fst_1660_);
                                v___x_1665_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_1665_, 0, v___x_1662_);
                                leanh::lean_ctor_set(v___x_1665_, 1, v_rupUnits_1626_);
                                leanh::lean_ctor_set(v___x_1665_, 2, v_ratUnits_1627_);
                                leanh::lean_ctor_set(v___x_1665_, 3, v_assignments_1628_);
                                return v___x_1665_;
                            } else {
                                v_v_1666_ = lean_array_fget(v_assignments_1628_, v_fst_1660_);
                                v___x_1667_ = leanh::lean_box(0);
                                v_xs_x27_1668_ =
                                    lean_array_fset(v_assignments_1628_, v_fst_1660_, v___x_1667_);
                                v___x_1674_ = (leanh::lean_unbox(v_v_1666_) as u8);
                                match v___x_1674_ {
                                    1 => {
                                        leanh::lean_dec(v_v_1666_);
                                        v___x_1675_ = 2;
                                        v___y_1670_ = v___x_1675_;
                                        state = 5;
                                        continue;
                                    }
                                    3 => {
                                        leanh::lean_dec(v_v_1666_);
                                        v___x_1676_ = 0;
                                        v___y_1670_ = v___x_1676_;
                                        state = 5;
                                        continue;
                                    }
                                    _ => {
                                        v___x_1677_ = (leanh::lean_unbox(v_v_1666_) as u8);
                                        leanh::lean_dec(v_v_1666_);
                                        v___y_1670_ = v___x_1677_;
                                        state = 5;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                } else {
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1633_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1633_, 0, v_c_1624_);
                v___x_1634_ = lean_array_push(v_clauses_1625_, v___x_1633_);
                if v_isShared_1631_ == 0 {
                    leanh::lean_ctor_set(v___x_1630_, 0, v___x_1634_);
                    v___x_1636_ = v___x_1630_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1637_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 0, v___x_1634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 1, v_rupUnits_1626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 2, v_ratUnits_1627_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1637_, 3, v_assignments_1628_);
                    v___x_1636_ = v_reuseFailAlloc_1637_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1636_;
            }
            4 => {
                v___x_1653_ = leanh::lean_box((v___y_1652_) as usize);
                v___x_1654_ = lean_array_fset(v_xs_x27_1650_, v_fst_1642_, v___x_1653_);
                leanh::lean_dec(v_fst_1642_);
                v___x_1655_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1655_, 0, v___x_1644_);
                leanh::lean_ctor_set(v___x_1655_, 1, v_rupUnits_1626_);
                leanh::lean_ctor_set(v___x_1655_, 2, v_ratUnits_1627_);
                leanh::lean_ctor_set(v___x_1655_, 3, v___x_1654_);
                return v___x_1655_;
            }
            5 => {
                v___x_1671_ = leanh::lean_box((v___y_1670_) as usize);
                v___x_1672_ = lean_array_fset(v_xs_x27_1668_, v_fst_1660_, v___x_1671_);
                leanh::lean_dec(v_fst_1660_);
                v___x_1673_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                leanh::lean_ctor_set(v___x_1673_, 0, v___x_1662_);
                leanh::lean_ctor_set(v___x_1673_, 1, v_rupUnits_1626_);
                leanh::lean_ctor_set(v___x_1673_, 2, v_ratUnits_1627_);
                leanh::lean_ctor_set(v___x_1673_, 3, v___x_1672_);
                return v___x_1673_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(
    mut v_n_1679_: *mut leanh::LeanObject,
    mut v_f_1680_: *mut leanh::LeanObject,
    mut v_c_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1682_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(v_f_1680_, v_c_1681_);
    return v___x_1682_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___boxed(
    mut v_n_1683_: *mut leanh::LeanObject,
    mut v_f_1684_: *mut leanh::LeanObject,
    mut v_c_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1686_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert(v_n_1683_, v_f_1684_, v_c_1685_);
    leanh::lean_dec(v_n_1683_);
    return v_res_1686_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(
    mut v_f_1687_: *mut leanh::LeanObject,
    mut v_id_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_1692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1695_: u8 = 0;
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: u8 = 0;
    let mut v___x_1718_: u8 = 0;
    let mut v___x_1719_: u8 = 0;
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_1689_ = leanh::lean_ctor_get(v_f_1687_, 0);
                v_rupUnits_1690_ = leanh::lean_ctor_get(v_f_1687_, 1);
                v_ratUnits_1691_ = leanh::lean_ctor_get(v_f_1687_, 2);
                v_assignments_1692_ = leanh::lean_ctor_get(v_f_1687_, 3);
                v_isSharedCheck_1723_ = (!leanh::lean_is_exclusive(v_f_1687_)) as u8;
                if v_isSharedCheck_1723_ == 0 {
                    v___x_1694_ = v_f_1687_;
                    v_isShared_1695_ = v_isSharedCheck_1723_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_1692_);
                    leanh::lean_inc(v_ratUnits_1691_);
                    leanh::lean_inc(v_rupUnits_1690_);
                    leanh::lean_inc(v_clauses_1689_);
                    leanh::lean_dec(v_f_1687_);
                    v___x_1694_ = leanh::lean_box(0);
                    v_isShared_1695_ = v_isSharedCheck_1723_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1702_ = leanh::lean_box(0);
                v___x_1703_ = lean_array_get_borrowed(v___x_1702_, v_clauses_1689_, v_id_1688_);
                if leanh::lean_obj_tag(v___x_1703_) == 0 {
                    leanh::lean_del_object(v___x_1694_);
                    v___x_1704_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v___x_1704_, 0, v_clauses_1689_);
                    leanh::lean_ctor_set(v___x_1704_, 1, v_rupUnits_1690_);
                    leanh::lean_ctor_set(v___x_1704_, 2, v_ratUnits_1691_);
                    leanh::lean_ctor_set(v___x_1704_, 3, v_assignments_1692_);
                    return v___x_1704_;
                } else {
                    v_val_1705_ = leanh::lean_ctor_get(v___x_1703_, 0);
                    if leanh::lean_obj_tag(v_val_1705_) == 1 {
                        v_tail_1706_ = leanh::lean_ctor_get(v_val_1705_, 1);
                        if leanh::lean_obj_tag(v_tail_1706_) == 0 {
                            leanh::lean_del_object(v___x_1694_);
                            v_head_1707_ = leanh::lean_ctor_get(v_val_1705_, 0);
                            v_fst_1708_ = leanh::lean_ctor_get(v_head_1707_, 0);
                            leanh::lean_inc(v_fst_1708_);
                            v_snd_1709_ = leanh::lean_ctor_get(v_head_1707_, 1);
                            leanh::lean_inc(v_snd_1709_);
                            v___x_1710_ = lean_array_set(v_clauses_1689_, v_id_1688_, v___x_1702_);
                            v___x_1711_ = lean_array_get_size(v_assignments_1692_);
                            v___x_1712_ = lean_nat_dec_lt(v_fst_1708_, v___x_1711_);
                            if v___x_1712_ == 0 {
                                leanh::lean_dec(v_snd_1709_);
                                leanh::lean_dec(v_fst_1708_);
                                v___x_1713_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_1713_, 0, v___x_1710_);
                                leanh::lean_ctor_set(v___x_1713_, 1, v_rupUnits_1690_);
                                leanh::lean_ctor_set(v___x_1713_, 2, v_ratUnits_1691_);
                                leanh::lean_ctor_set(v___x_1713_, 3, v_assignments_1692_);
                                return v___x_1713_;
                            } else {
                                v_v_1714_ = lean_array_fget(v_assignments_1692_, v_fst_1708_);
                                v___x_1715_ = leanh::lean_box(0);
                                v_xs_x27_1716_ =
                                    lean_array_fset(v_assignments_1692_, v_fst_1708_, v___x_1715_);
                                v___x_1717_ = (leanh::lean_unbox(v_snd_1709_) as u8);
                                leanh::lean_dec(v_snd_1709_);
                                v___x_1718_ = (leanh::lean_unbox(v_v_1714_) as u8);
                                leanh::lean_dec(v_v_1714_);
                                v___x_1719_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(
                                        v___x_1717_,
                                        v___x_1718_,
                                    );
                                v___x_1720_ = leanh::lean_box((v___x_1719_) as usize);
                                v___x_1721_ =
                                    lean_array_fset(v_xs_x27_1716_, v_fst_1708_, v___x_1720_);
                                leanh::lean_dec(v_fst_1708_);
                                v___x_1722_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                                leanh::lean_ctor_set(v___x_1722_, 0, v___x_1710_);
                                leanh::lean_ctor_set(v___x_1722_, 1, v_rupUnits_1690_);
                                leanh::lean_ctor_set(v___x_1722_, 2, v_ratUnits_1691_);
                                leanh::lean_ctor_set(v___x_1722_, 3, v___x_1721_);
                                return v___x_1722_;
                            }
                        } else {
                            state = 2;
                            continue;
                        }
                    } else {
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1697_ = leanh::lean_box(0);
                v___x_1698_ = lean_array_set(v_clauses_1689_, v_id_1688_, v___x_1697_);
                if v_isShared_1695_ == 0 {
                    leanh::lean_ctor_set(v___x_1694_, 0, v___x_1698_);
                    v___x_1700_ = v___x_1694_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1701_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 0, v___x_1698_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 1, v_rupUnits_1690_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 2, v_ratUnits_1691_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1701_, 3, v_assignments_1692_);
                    v___x_1700_ = v_reuseFailAlloc_1701_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1700_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg___boxed(
    mut v_f_1724_: *mut leanh::LeanObject,
    mut v_id_1725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1726_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(
        v_f_1724_, v_id_1725_,
    );
    leanh::lean_dec(v_id_1725_);
    return v_res_1726_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(
    mut v_n_1727_: *mut leanh::LeanObject,
    mut v_f_1728_: *mut leanh::LeanObject,
    mut v_id_1729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1730_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(
        v_f_1728_, v_id_1729_,
    );
    return v___x_1730_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___boxed(
    mut v_n_1731_: *mut leanh::LeanObject,
    mut v_f_1732_: *mut leanh::LeanObject,
    mut v_id_1733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1734_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne(
        v_n_1731_, v_f_1732_, v_id_1733_,
    );
    leanh::lean_dec(v_id_1733_);
    leanh::lean_dec(v_n_1731_);
    return v_res_1734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(
    mut v_as_1735_: *mut leanh::LeanObject,
    mut v_i_1736_: usize,
    mut v_stop_1737_: usize,
    mut v_b_1738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1739_: u8 = 0;
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: usize = 0;
    let mut v___x_1743_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1739_ = lean_usize_dec_eq(v_i_1736_, v_stop_1737_);
                if v___x_1739_ == 0 {
                    v___x_1740_ = lean_array_uget_borrowed(v_as_1735_, v_i_1736_);
                    v___x_1741_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_deleteOne___redArg(
                            v_b_1738_,
                            v___x_1740_,
                        );
                    v___x_1742_ = 1usize;
                    v___x_1743_ = lean_usize_add(v_i_1736_, v___x_1742_);
                    v_i_1736_ = v___x_1743_;
                    v_b_1738_ = v___x_1741_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1738_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg___boxed(
    mut v_as_1745_: *mut leanh::LeanObject,
    mut v_i_1746_: *mut leanh::LeanObject,
    mut v_stop_1747_: *mut leanh::LeanObject,
    mut v_b_1748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1749_: usize = 0;
    let mut v_stop_boxed_1750_: usize = 0;
    let mut v_res_1751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1749_ = leanh::lean_unbox_usize(v_i_1746_);
    leanh::lean_dec(v_i_1746_);
    v_stop_boxed_1750_ = leanh::lean_unbox_usize(v_stop_1747_);
    leanh::lean_dec(v_stop_1747_);
    v_res_1751_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_as_1745_, v_i_boxed_1749_, v_stop_boxed_1750_, v_b_1748_);
    leanh::lean_dec_ref(v_as_1745_);
    return v_res_1751_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(
    mut v_n_1752_: *mut leanh::LeanObject,
    mut v_f_1753_: *mut leanh::LeanObject,
    mut v_ids_1754_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1757_: u8 = 0;
    v___x_1755_ = leanh::lean_unsigned_to_nat(0);
    v___x_1756_ = lean_array_get_size(v_ids_1754_);
    v___x_1757_ = lean_nat_dec_lt(v___x_1755_, v___x_1756_);
    if v___x_1757_ == 0 {
        return v_f_1753_;
    } else {
        let mut v___x_1758_: u8 = 0;
        v___x_1758_ = lean_nat_dec_le(v___x_1756_, v___x_1756_);
        if v___x_1758_ == 0 {
            if v___x_1757_ == 0 {
                return v_f_1753_;
            } else {
                let mut v___x_1759_: usize = 0;
                let mut v___x_1760_: usize = 0;
                let mut v___x_1761_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_1759_ = 0usize;
                v___x_1760_ = lean_usize_of_nat(v___x_1756_);
                v___x_1761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_ids_1754_, v___x_1759_, v___x_1760_, v_f_1753_);
                return v___x_1761_;
            }
        } else {
            let mut v___x_1762_: usize = 0;
            let mut v___x_1763_: usize = 0;
            let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1762_ = 0usize;
            v___x_1763_ = lean_usize_of_nat(v___x_1756_);
            v___x_1764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_ids_1754_, v___x_1762_, v___x_1763_, v_f_1753_);
            return v___x_1764_;
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete___boxed(
    mut v_n_1765_: *mut leanh::LeanObject,
    mut v_f_1766_: *mut leanh::LeanObject,
    mut v_ids_1767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1768_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete(
        v_n_1765_,
        v_f_1766_,
        v_ids_1767_,
    );
    leanh::lean_dec_ref(v_ids_1767_);
    leanh::lean_dec(v_n_1765_);
    return v_res_1768_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(
    mut v_n_1769_: *mut leanh::LeanObject,
    mut v_as_1770_: *mut leanh::LeanObject,
    mut v_i_1771_: usize,
    mut v_stop_1772_: usize,
    mut v_b_1773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1774_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___redArg(v_as_1770_, v_i_1771_, v_stop_1772_, v_b_1773_);
    return v___x_1774_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0___boxed(
    mut v_n_1775_: *mut leanh::LeanObject,
    mut v_as_1776_: *mut leanh::LeanObject,
    mut v_i_1777_: *mut leanh::LeanObject,
    mut v_stop_1778_: *mut leanh::LeanObject,
    mut v_b_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1780_: usize = 0;
    let mut v_stop_boxed_1781_: usize = 0;
    let mut v_res_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1780_ = leanh::lean_unbox_usize(v_i_1777_);
    leanh::lean_dec(v_i_1777_);
    v_stop_boxed_1781_ = leanh::lean_unbox_usize(v_stop_1778_);
    leanh::lean_dec(v_stop_1778_);
    v_res_1782_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_delete_spec__0(v_n_1775_, v_as_1776_, v_i_boxed_1780_, v_stop_boxed_1781_, v_b_1779_);
    leanh::lean_dec_ref(v_as_1776_);
    leanh::lean_dec(v_n_1775_);
    return v_res_1782_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(
    mut v_n_1783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1784_ = leanh::lean_box(0);
    return v___x_1784_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin___boxed(
    mut v_n_1785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1786_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_instEntailsPosFin(v_n_1785_);
    leanh::lean_dec(v_n_1785_);
    return v_res_1786_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(
    mut v_x_1787_: *mut leanh::LeanObject,
    mut v_x_1788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_1789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1795_: u8 = 0;
    let mut v_fst_1796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: u8 = 0;
    let mut v___x_1799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_curAssignment_1800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: u8 = 0;
    let mut v___x_1802_: u8 = 0;
    let mut v___x_1803_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1806_: u8 = 0;
    let mut v___x_1807_: u8 = 0;
    let mut v_units_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1811_: u8 = 0;
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: u8 = 0;
    let mut v___x_1822_: u8 = 0;
    let mut v___x_1823_: u8 = 0;
    let mut v___x_1824_: u8 = 0;
    let mut v___x_1825_: u8 = 0;
    let mut v___x_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: u8 = 0;
    let mut v_v_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: u8 = 0;
    let mut v___x_1832_: u8 = 0;
    let mut v___x_1833_: u8 = 0;
    let mut v___x_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v_unused_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_1789_ = leanh::lean_ctor_get(v_x_1787_, 1);
                leanh::lean_inc(v_snd_1789_);
                v_fst_1790_ = leanh::lean_ctor_get(v_x_1787_, 0);
                v_fst_1791_ = leanh::lean_ctor_get(v_snd_1789_, 0);
                v_snd_1792_ = leanh::lean_ctor_get(v_snd_1789_, 1);
                v_isSharedCheck_1839_ = (!leanh::lean_is_exclusive(v_snd_1789_)) as u8;
                if v_isSharedCheck_1839_ == 0 {
                    v___x_1794_ = v_snd_1789_;
                    v_isShared_1795_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1792_);
                    leanh::lean_inc(v_fst_1791_);
                    leanh::lean_dec(v_snd_1789_);
                    v___x_1794_ = leanh::lean_box(0);
                    v_isShared_1795_ = v_isSharedCheck_1839_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_1796_ = leanh::lean_ctor_get(v_x_1788_, 0);
                leanh::lean_inc(v_fst_1796_);
                v_snd_1797_ = leanh::lean_ctor_get(v_x_1788_, 1);
                leanh::lean_inc(v_snd_1797_);
                v___x_1798_ = 0;
                v___x_1799_ = leanh::lean_box((v___x_1798_) as usize);
                v_curAssignment_1800_ = lean_array_get(v___x_1799_, v_fst_1791_, v_fst_1796_);
                leanh::lean_dec(v___x_1799_);
                v___x_1801_ = (leanh::lean_unbox(v_snd_1797_) as u8);
                v___x_1802_ = (leanh::lean_unbox(v_curAssignment_1800_) as u8);
                v___x_1803_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(
                    v___x_1801_,
                    v___x_1802_,
                );
                if v___x_1803_ == 0 {
                    leanh::lean_inc(v_fst_1790_);
                    v_isSharedCheck_1836_ = (!leanh::lean_is_exclusive(v_x_1787_)) as u8;
                    if v_isSharedCheck_1836_ == 0 {
                        v_unused_1837_ = leanh::lean_ctor_get(v_x_1787_, 1);
                        leanh::lean_dec(v_unused_1837_);
                        v_unused_1838_ = leanh::lean_ctor_get(v_x_1787_, 0);
                        leanh::lean_dec(v_unused_1838_);
                        v___x_1805_ = v_x_1787_;
                        v_isShared_1806_ = v_isSharedCheck_1836_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v_x_1787_);
                        v___x_1805_ = leanh::lean_box(0);
                        v_isShared_1806_ = v_isSharedCheck_1836_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_curAssignment_1800_);
                    leanh::lean_dec(v_snd_1797_);
                    leanh::lean_dec(v_fst_1796_);
                    leanh::lean_del_object(v___x_1794_);
                    leanh::lean_dec(v_snd_1792_);
                    leanh::lean_dec(v_fst_1791_);
                    leanh::lean_dec_ref(v_x_1788_);
                    return v_x_1787_;
                }
            }
            2 => {
                v___x_1807_ = 1;
                v_units_1808_ = lean_array_push(v_fst_1790_, v_x_1788_);
                v___x_1826_ = lean_array_get_size(v_fst_1791_);
                v___x_1827_ = lean_nat_dec_lt(v_fst_1796_, v___x_1826_);
                if v___x_1827_ == 0 {
                    leanh::lean_dec(v_snd_1797_);
                    leanh::lean_dec(v_fst_1796_);
                    v___y_1820_ = v_fst_1791_;
                    state = 6;
                    continue;
                } else {
                    v_v_1828_ = lean_array_fget(v_fst_1791_, v_fst_1796_);
                    v___x_1829_ = leanh::lean_box(0);
                    v_xs_x27_1830_ = lean_array_fset(v_fst_1791_, v_fst_1796_, v___x_1829_);
                    v___x_1831_ = (leanh::lean_unbox(v_snd_1797_) as u8);
                    leanh::lean_dec(v_snd_1797_);
                    v___x_1832_ = (leanh::lean_unbox(v_v_1828_) as u8);
                    leanh::lean_dec(v_v_1828_);
                    v___x_1833_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(
                        v___x_1831_,
                        v___x_1832_,
                    );
                    v___x_1834_ = leanh::lean_box((v___x_1833_) as usize);
                    v___x_1835_ = lean_array_fset(v_xs_x27_1830_, v_fst_1796_, v___x_1834_);
                    leanh::lean_dec(v_fst_1796_);
                    v___y_1820_ = v___x_1835_;
                    state = 6;
                    continue;
                }
            }
            3 => {
                v___x_1812_ = leanh::lean_box((v___y_1811_) as usize);
                if v_isShared_1795_ == 0 {
                    leanh::lean_ctor_set(v___x_1794_, 1, v___x_1812_);
                    leanh::lean_ctor_set(v___x_1794_, 0, v___y_1810_);
                    v___x_1814_ = v___x_1794_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v___y_1810_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 1, v___x_1812_);
                    v___x_1814_ = v_reuseFailAlloc_1818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1806_ == 0 {
                    leanh::lean_ctor_set(v___x_1805_, 1, v___x_1814_);
                    leanh::lean_ctor_set(v___x_1805_, 0, v_units_1808_);
                    v___x_1816_ = v___x_1805_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 0, v_units_1808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1817_, 1, v___x_1814_);
                    v___x_1816_ = v_reuseFailAlloc_1817_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1816_;
            }
            6 => {
                v___x_1821_ = (leanh::lean_unbox(v_snd_1792_) as u8);
                if v___x_1821_ == 0 {
                    v___x_1822_ = 3;
                    v___x_1823_ = (leanh::lean_unbox(v_curAssignment_1800_) as u8);
                    leanh::lean_dec(v_curAssignment_1800_);
                    v___x_1824_ = l_Std_Tactic_BVDecide_LRAT_Internal_instBEqAssignment_beq(
                        v___x_1823_,
                        v___x_1822_,
                    );
                    if v___x_1824_ == 0 {
                        leanh::lean_dec(v_snd_1792_);
                        v___y_1810_ = v___y_1820_;
                        v___y_1811_ = v___x_1807_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1825_ = (leanh::lean_unbox(v_snd_1792_) as u8);
                        leanh::lean_dec(v_snd_1792_);
                        v___y_1810_ = v___y_1820_;
                        v___y_1811_ = v___x_1825_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_curAssignment_1800_);
                    leanh::lean_dec(v_snd_1792_);
                    v___y_1810_ = v___y_1820_;
                    v___y_1811_ = v___x_1807_;
                    state = 3;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(
    mut v_n_1840_: *mut leanh::LeanObject,
    mut v_x_1841_: *mut leanh::LeanObject,
    mut v_x_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1843_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(
        v_x_1841_, v_x_1842_,
    );
    return v___x_1843_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___boxed(
    mut v_n_1844_: *mut leanh::LeanObject,
    mut v_x_1845_: *mut leanh::LeanObject,
    mut v_x_1846_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1847_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1847_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit(
        v_n_1844_, v_x_1845_, v_x_1846_,
    );
    leanh::lean_dec(v_n_1844_);
    return v_res_1847_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(
    mut v_x_1848_: *mut leanh::LeanObject,
    mut v_x_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1849_) == 0 {
                    return v_x_1848_;
                } else {
                    v_head_1850_ = leanh::lean_ctor_get(v_x_1849_, 0);
                    leanh::lean_inc(v_head_1850_);
                    v_tail_1851_ = leanh::lean_ctor_get(v_x_1849_, 1);
                    leanh::lean_inc(v_tail_1851_);
                    leanh::lean_dec_ref_known(v_x_1849_, 2);
                    v___x_1852_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertUnit___redArg(
                            v_x_1848_,
                            v_head_1850_,
                        );
                    v_x_1848_ = v___x_1852_;
                    v_x_1849_ = v_tail_1851_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(
    mut v_n_1854_: *mut leanh::LeanObject,
    mut v_f_1855_: *mut leanh::LeanObject,
    mut v_ls_1856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1875_: u8 = 0;
    let mut v___x_1877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1882_: u8 = 0;
    let mut v_isSharedCheck_1883_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_1857_ = leanh::lean_ctor_get(v_f_1855_, 0);
                v_rupUnits_1858_ = leanh::lean_ctor_get(v_f_1855_, 1);
                v_ratUnits_1859_ = leanh::lean_ctor_get(v_f_1855_, 2);
                v_assignments_1860_ = leanh::lean_ctor_get(v_f_1855_, 3);
                v_isSharedCheck_1883_ = (!leanh::lean_is_exclusive(v_f_1855_)) as u8;
                if v_isSharedCheck_1883_ == 0 {
                    v___x_1862_ = v_f_1855_;
                    v_isShared_1863_ = v_isSharedCheck_1883_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_1860_);
                    leanh::lean_inc(v_ratUnits_1859_);
                    leanh::lean_inc(v_rupUnits_1858_);
                    leanh::lean_inc(v_clauses_1857_);
                    leanh::lean_dec(v_f_1855_);
                    v___x_1862_ = leanh::lean_box(0);
                    v_isShared_1863_ = v_isSharedCheck_1883_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1864_ = 0;
                v___x_1865_ = leanh::lean_box((v___x_1864_) as usize);
                v___x_1866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1866_, 0, v_assignments_1860_);
                leanh::lean_ctor_set(v___x_1866_, 1, v___x_1865_);
                v___x_1867_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1867_, 0, v_rupUnits_1858_);
                leanh::lean_ctor_set(v___x_1867_, 1, v___x_1866_);
                v___x_1868_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_1867_, v_ls_1856_);
                v_snd_1869_ = leanh::lean_ctor_get(v___x_1868_, 1);
                leanh::lean_inc(v_snd_1869_);
                v_fst_1870_ = leanh::lean_ctor_get(v___x_1868_, 0);
                leanh::lean_inc(v_fst_1870_);
                leanh::lean_dec_ref(v___x_1868_);
                v_fst_1871_ = leanh::lean_ctor_get(v_snd_1869_, 0);
                v_snd_1872_ = leanh::lean_ctor_get(v_snd_1869_, 1);
                v_isSharedCheck_1882_ = (!leanh::lean_is_exclusive(v_snd_1869_)) as u8;
                if v_isSharedCheck_1882_ == 0 {
                    v___x_1874_ = v_snd_1869_;
                    v_isShared_1875_ = v_isSharedCheck_1882_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1872_);
                    leanh::lean_inc(v_fst_1871_);
                    leanh::lean_dec(v_snd_1869_);
                    v___x_1874_ = leanh::lean_box(0);
                    v_isShared_1875_ = v_isSharedCheck_1882_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1863_ == 0 {
                    leanh::lean_ctor_set(v___x_1862_, 3, v_fst_1871_);
                    leanh::lean_ctor_set(v___x_1862_, 1, v_fst_1870_);
                    v___x_1877_ = v___x_1862_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1881_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 0, v_clauses_1857_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 1, v_fst_1870_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 2, v_ratUnits_1859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1881_, 3, v_fst_1871_);
                    v___x_1877_ = v_reuseFailAlloc_1881_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1875_ == 0 {
                    leanh::lean_ctor_set(v___x_1874_, 0, v___x_1877_);
                    v___x_1879_ = v___x_1874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1880_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 0, v___x_1877_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_snd_1872_);
                    v___x_1879_ = v_reuseFailAlloc_1880_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1879_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits___boxed(
    mut v_n_1884_: *mut leanh::LeanObject,
    mut v_f_1885_: *mut leanh::LeanObject,
    mut v_ls_1886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1887_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(
        v_n_1884_, v_f_1885_, v_ls_1886_,
    );
    leanh::lean_dec(v_n_1884_);
    return v_res_1887_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(
    mut v_n_1888_: *mut leanh::LeanObject,
    mut v_x_1889_: *mut leanh::LeanObject,
    mut v_x_1890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1891_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v_x_1889_, v_x_1890_);
    return v___x_1891_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___boxed(
    mut v_n_1892_: *mut leanh::LeanObject,
    mut v_x_1893_: *mut leanh::LeanObject,
    mut v_x_1894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1895_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0(v_n_1892_, v_x_1893_, v_x_1894_);
    leanh::lean_dec(v_n_1892_);
    return v_res_1895_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(
    mut v_f_1896_: *mut leanh::LeanObject,
    mut v_ls_1897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1904_: u8 = 0;
    let mut v___x_1905_: u8 = 0;
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1923_: u8 = 0;
    let mut v_isSharedCheck_1924_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_1898_ = leanh::lean_ctor_get(v_f_1896_, 0);
                v_rupUnits_1899_ = leanh::lean_ctor_get(v_f_1896_, 1);
                v_ratUnits_1900_ = leanh::lean_ctor_get(v_f_1896_, 2);
                v_assignments_1901_ = leanh::lean_ctor_get(v_f_1896_, 3);
                v_isSharedCheck_1924_ = (!leanh::lean_is_exclusive(v_f_1896_)) as u8;
                if v_isSharedCheck_1924_ == 0 {
                    v___x_1903_ = v_f_1896_;
                    v_isShared_1904_ = v_isSharedCheck_1924_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_1901_);
                    leanh::lean_inc(v_ratUnits_1900_);
                    leanh::lean_inc(v_rupUnits_1899_);
                    leanh::lean_inc(v_clauses_1898_);
                    leanh::lean_dec(v_f_1896_);
                    v___x_1903_ = leanh::lean_box(0);
                    v_isShared_1904_ = v_isSharedCheck_1924_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1905_ = 0;
                v___x_1906_ = leanh::lean_box((v___x_1905_) as usize);
                v___x_1907_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1907_, 0, v_assignments_1901_);
                leanh::lean_ctor_set(v___x_1907_, 1, v___x_1906_);
                v___x_1908_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1908_, 0, v_ratUnits_1900_);
                leanh::lean_ctor_set(v___x_1908_, 1, v___x_1907_);
                v___x_1909_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits_spec__0___redArg(v___x_1908_, v_ls_1897_);
                v_snd_1910_ = leanh::lean_ctor_get(v___x_1909_, 1);
                leanh::lean_inc(v_snd_1910_);
                v_fst_1911_ = leanh::lean_ctor_get(v___x_1909_, 0);
                leanh::lean_inc(v_fst_1911_);
                leanh::lean_dec_ref(v___x_1909_);
                v_fst_1912_ = leanh::lean_ctor_get(v_snd_1910_, 0);
                v_snd_1913_ = leanh::lean_ctor_get(v_snd_1910_, 1);
                v_isSharedCheck_1923_ = (!leanh::lean_is_exclusive(v_snd_1910_)) as u8;
                if v_isSharedCheck_1923_ == 0 {
                    v___x_1915_ = v_snd_1910_;
                    v_isShared_1916_ = v_isSharedCheck_1923_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1913_);
                    leanh::lean_inc(v_fst_1912_);
                    leanh::lean_dec(v_snd_1910_);
                    v___x_1915_ = leanh::lean_box(0);
                    v_isShared_1916_ = v_isSharedCheck_1923_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1904_ == 0 {
                    leanh::lean_ctor_set(v___x_1903_, 3, v_fst_1912_);
                    leanh::lean_ctor_set(v___x_1903_, 2, v_fst_1911_);
                    v___x_1918_ = v___x_1903_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1922_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 0, v_clauses_1898_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 1, v_rupUnits_1899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 2, v_fst_1911_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1922_, 3, v_fst_1912_);
                    v___x_1918_ = v_reuseFailAlloc_1922_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1916_ == 0 {
                    leanh::lean_ctor_set(v___x_1915_, 0, v___x_1918_);
                    v___x_1920_ = v___x_1915_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1921_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 0, v___x_1918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1921_, 1, v_snd_1913_);
                    v___x_1920_ = v_reuseFailAlloc_1921_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(
    mut v_n_1925_: *mut leanh::LeanObject,
    mut v_f_1926_: *mut leanh::LeanObject,
    mut v_ls_1927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1928_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(
        v_f_1926_, v_ls_1927_,
    );
    return v___x_1928_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___boxed(
    mut v_n_1929_: *mut leanh::LeanObject,
    mut v_f_1930_: *mut leanh::LeanObject,
    mut v_ls_1931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1932_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits(
        v_n_1929_, v_f_1930_, v_ls_1931_,
    );
    leanh::lean_dec(v_n_1929_);
    return v_res_1932_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(
    mut v_x_1933_: *mut leanh::LeanObject,
    mut v_x_1934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: u8 = 0;
    v_fst_1935_ = leanh::lean_ctor_get(v_x_1934_, 0);
    v_snd_1936_ = leanh::lean_ctor_get(v_x_1934_, 1);
    v___x_1937_ = lean_array_get_size(v_x_1933_);
    v___x_1938_ = lean_nat_dec_lt(v_fst_1935_, v___x_1937_);
    if v___x_1938_ == 0 {
        return v_x_1933_;
    } else {
        let mut v_v_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_xs_x27_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1942_: u8 = 0;
        let mut v___x_1943_: u8 = 0;
        let mut v___x_1944_: u8 = 0;
        let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_1939_ = lean_array_fget(v_x_1933_, v_fst_1935_);
        v___x_1940_ = leanh::lean_box(0);
        v_xs_x27_1941_ = lean_array_fset(v_x_1933_, v_fst_1935_, v___x_1940_);
        v___x_1942_ = (leanh::lean_unbox(v_snd_1936_) as u8);
        v___x_1943_ = (leanh::lean_unbox(v_v_1939_) as u8);
        leanh::lean_dec(v_v_1939_);
        v___x_1944_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_removeAssignment(
            v___x_1942_,
            v___x_1943_,
        );
        v___x_1945_ = leanh::lean_box((v___x_1944_) as usize);
        v___x_1946_ = lean_array_fset(v_xs_x27_1941_, v_fst_1935_, v___x_1945_);
        return v___x_1946_;
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg___boxed(
    mut v_x_1947_: *mut leanh::LeanObject,
    mut v_x_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1949_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_1947_, v_x_1948_);
    leanh::lean_dec_ref(v_x_1948_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(
    mut v_n_1950_: *mut leanh::LeanObject,
    mut v_x_1951_: *mut leanh::LeanObject,
    mut v_x_1952_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1953_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(v_x_1951_, v_x_1952_);
    return v___x_1953_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___boxed(
    mut v_n_1954_: *mut leanh::LeanObject,
    mut v_x_1955_: *mut leanh::LeanObject,
    mut v_x_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1957_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit(
        v_n_1954_, v_x_1955_, v_x_1956_,
    );
    leanh::lean_dec_ref(v_x_1956_);
    leanh::lean_dec(v_n_1954_);
    return v_res_1957_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(
    mut v_as_1958_: *mut leanh::LeanObject,
    mut v_i_1959_: usize,
    mut v_stop_1960_: usize,
    mut v_b_1961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1962_: u8 = 0;
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1965_: usize = 0;
    let mut v___x_1966_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1962_ = lean_usize_dec_eq(v_i_1959_, v_stop_1960_);
                if v___x_1962_ == 0 {
                    v___x_1963_ = lean_array_uget_borrowed(v_as_1958_, v_i_1959_);
                    v___x_1964_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(
                            v_b_1961_,
                            v___x_1963_,
                        );
                    v___x_1965_ = 1usize;
                    v___x_1966_ = lean_usize_add(v_i_1959_, v___x_1965_);
                    v_i_1959_ = v___x_1966_;
                    v_b_1961_ = v___x_1964_;
                    state = 0;
                    continue;
                } else {
                    return v_b_1961_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg___boxed(
    mut v_as_1968_: *mut leanh::LeanObject,
    mut v_i_1969_: *mut leanh::LeanObject,
    mut v_stop_1970_: *mut leanh::LeanObject,
    mut v_b_1971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1972_: usize = 0;
    let mut v_stop_boxed_1973_: usize = 0;
    let mut v_res_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1972_ = leanh::lean_unbox_usize(v_i_1969_);
    leanh::lean_dec(v_i_1969_);
    v_stop_boxed_1973_ = leanh::lean_unbox_usize(v_stop_1970_);
    leanh::lean_dec(v_stop_1970_);
    v_res_1974_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_1968_, v_i_boxed_1972_, v_stop_boxed_1973_, v_b_1971_);
    leanh::lean_dec_ref(v_as_1968_);
    return v_res_1974_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(
    mut v_n_1975_: *mut leanh::LeanObject,
    mut v_f_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_1978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_1979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_1980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1983_: u8 = 0;
    let mut v___y_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: u8 = 0;
    let mut v___x_1993_: u8 = 0;
    let mut v___x_1994_: usize = 0;
    let mut v___x_1995_: usize = 0;
    let mut v___x_1996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1997_: usize = 0;
    let mut v___x_1998_: usize = 0;
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2000_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_1977_ = leanh::lean_ctor_get(v_f_1976_, 0);
                v_rupUnits_1978_ = leanh::lean_ctor_get(v_f_1976_, 1);
                v_ratUnits_1979_ = leanh::lean_ctor_get(v_f_1976_, 2);
                v_assignments_1980_ = leanh::lean_ctor_get(v_f_1976_, 3);
                v_isSharedCheck_2000_ = (!leanh::lean_is_exclusive(v_f_1976_)) as u8;
                if v_isSharedCheck_2000_ == 0 {
                    v___x_1982_ = v_f_1976_;
                    v_isShared_1983_ = v_isSharedCheck_2000_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_1980_);
                    leanh::lean_inc(v_ratUnits_1979_);
                    leanh::lean_inc(v_rupUnits_1978_);
                    leanh::lean_inc(v_clauses_1977_);
                    leanh::lean_dec(v_f_1976_);
                    v___x_1982_ = leanh::lean_box(0);
                    v_isShared_1983_ = v_isSharedCheck_2000_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1990_ = leanh::lean_unsigned_to_nat(0);
                v___x_1991_ = lean_array_get_size(v_rupUnits_1978_);
                v___x_1992_ = lean_nat_dec_lt(v___x_1990_, v___x_1991_);
                if v___x_1992_ == 0 {
                    leanh::lean_dec_ref(v_rupUnits_1978_);
                    v___y_1985_ = v_assignments_1980_;
                    state = 2;
                    continue;
                } else {
                    v___x_1993_ = lean_nat_dec_le(v___x_1991_, v___x_1991_);
                    if v___x_1993_ == 0 {
                        if v___x_1992_ == 0 {
                            leanh::lean_dec_ref(v_rupUnits_1978_);
                            v___y_1985_ = v_assignments_1980_;
                            state = 2;
                            continue;
                        } else {
                            v___x_1994_ = 0usize;
                            v___x_1995_ = lean_usize_of_nat(v___x_1991_);
                            v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_1978_, v___x_1994_, v___x_1995_, v_assignments_1980_);
                            leanh::lean_dec_ref(v_rupUnits_1978_);
                            v___y_1985_ = v___x_1996_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_1997_ = 0usize;
                        v___x_1998_ = lean_usize_of_nat(v___x_1991_);
                        v___x_1999_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_rupUnits_1978_, v___x_1997_, v___x_1998_, v_assignments_1980_);
                        leanh::lean_dec_ref(v_rupUnits_1978_);
                        v___y_1985_ = v___x_1999_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1986_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
                if v_isShared_1983_ == 0 {
                    leanh::lean_ctor_set(v___x_1982_, 3, v___y_1985_);
                    leanh::lean_ctor_set(v___x_1982_, 1, v___x_1986_);
                    v___x_1988_ = v___x_1982_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1989_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 0, v_clauses_1977_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 1, v___x_1986_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 2, v_ratUnits_1979_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1989_, 3, v___y_1985_);
                    v___x_1988_ = v_reuseFailAlloc_1989_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1988_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits___boxed(
    mut v_n_2001_: *mut leanh::LeanObject,
    mut v_f_2002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2003_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(v_n_2001_, v_f_2002_);
    leanh::lean_dec(v_n_2001_);
    return v_res_2003_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(
    mut v_n_2004_: *mut leanh::LeanObject,
    mut v_as_2005_: *mut leanh::LeanObject,
    mut v_i_2006_: usize,
    mut v_stop_2007_: usize,
    mut v_b_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2009_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_as_2005_, v_i_2006_, v_stop_2007_, v_b_2008_);
    return v___x_2009_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___boxed(
    mut v_n_2010_: *mut leanh::LeanObject,
    mut v_as_2011_: *mut leanh::LeanObject,
    mut v_i_2012_: *mut leanh::LeanObject,
    mut v_stop_2013_: *mut leanh::LeanObject,
    mut v_b_2014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2015_: usize = 0;
    let mut v_stop_boxed_2016_: usize = 0;
    let mut v_res_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2015_ = leanh::lean_unbox_usize(v_i_2012_);
    leanh::lean_dec(v_i_2012_);
    v_stop_boxed_2016_ = leanh::lean_unbox_usize(v_stop_2013_);
    leanh::lean_dec(v_stop_2013_);
    v_res_2017_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0(v_n_2010_, v_as_2011_, v_i_boxed_2015_, v_stop_boxed_2016_, v_b_2014_);
    leanh::lean_dec_ref(v_as_2011_);
    leanh::lean_dec(v_n_2010_);
    return v_res_2017_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(
    mut v_f_2018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2025_: u8 = 0;
    let mut v___y_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: u8 = 0;
    let mut v___x_2035_: u8 = 0;
    let mut v___x_2036_: usize = 0;
    let mut v___x_2037_: usize = 0;
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: usize = 0;
    let mut v___x_2040_: usize = 0;
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2042_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_2019_ = leanh::lean_ctor_get(v_f_2018_, 0);
                v_rupUnits_2020_ = leanh::lean_ctor_get(v_f_2018_, 1);
                v_ratUnits_2021_ = leanh::lean_ctor_get(v_f_2018_, 2);
                v_assignments_2022_ = leanh::lean_ctor_get(v_f_2018_, 3);
                v_isSharedCheck_2042_ = (!leanh::lean_is_exclusive(v_f_2018_)) as u8;
                if v_isSharedCheck_2042_ == 0 {
                    v___x_2024_ = v_f_2018_;
                    v_isShared_2025_ = v_isSharedCheck_2042_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_2022_);
                    leanh::lean_inc(v_ratUnits_2021_);
                    leanh::lean_inc(v_rupUnits_2020_);
                    leanh::lean_inc(v_clauses_2019_);
                    leanh::lean_dec(v_f_2018_);
                    v___x_2024_ = leanh::lean_box(0);
                    v_isShared_2025_ = v_isSharedCheck_2042_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2032_ = leanh::lean_unsigned_to_nat(0);
                v___x_2033_ = lean_array_get_size(v_ratUnits_2021_);
                v___x_2034_ = lean_nat_dec_lt(v___x_2032_, v___x_2033_);
                if v___x_2034_ == 0 {
                    leanh::lean_dec_ref(v_ratUnits_2021_);
                    v___y_2027_ = v_assignments_2022_;
                    state = 2;
                    continue;
                } else {
                    v___x_2035_ = lean_nat_dec_le(v___x_2033_, v___x_2033_);
                    if v___x_2035_ == 0 {
                        if v___x_2034_ == 0 {
                            leanh::lean_dec_ref(v_ratUnits_2021_);
                            v___y_2027_ = v_assignments_2022_;
                            state = 2;
                            continue;
                        } else {
                            v___x_2036_ = 0usize;
                            v___x_2037_ = lean_usize_of_nat(v___x_2033_);
                            v___x_2038_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_2021_, v___x_2036_, v___x_2037_, v_assignments_2022_);
                            leanh::lean_dec_ref(v_ratUnits_2021_);
                            v___y_2027_ = v___x_2038_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_2039_ = 0usize;
                        v___x_2040_ = lean_usize_of_nat(v___x_2033_);
                        v___x_2041_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits_spec__0___redArg(v_ratUnits_2021_, v___x_2039_, v___x_2040_, v_assignments_2022_);
                        leanh::lean_dec_ref(v_ratUnits_2021_);
                        v___y_2027_ = v___x_2041_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2028_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
                if v_isShared_2025_ == 0 {
                    leanh::lean_ctor_set(v___x_2024_, 3, v___y_2027_);
                    leanh::lean_ctor_set(v___x_2024_, 2, v___x_2028_);
                    v___x_2030_ = v___x_2024_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2031_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_clauses_2019_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_rupUnits_2020_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 2, v___x_2028_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2031_, 3, v___y_2027_);
                    v___x_2030_ = v_reuseFailAlloc_2031_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2030_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(
    mut v_n_2043_: *mut leanh::LeanObject,
    mut v_f_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2045_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(v_f_2044_);
    return v___x_2045_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___boxed(
    mut v_n_2046_: *mut leanh::LeanObject,
    mut v_f_2047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2048_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits(v_n_2046_, v_f_2047_);
    leanh::lean_dec(v_n_2046_);
    return v_res_2048_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(
    mut v_x_2049_: *mut leanh::LeanObject,
    mut v_x_2050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2050_) == 0 {
                    return v_x_2049_;
                } else {
                    v_head_2051_ = leanh::lean_ctor_get(v_x_2050_, 0);
                    v_tail_2052_ = leanh::lean_ctor_get(v_x_2050_, 1);
                    v___x_2053_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearUnit___redArg(
                            v_x_2049_,
                            v_head_2051_,
                        );
                    v_x_2049_ = v___x_2053_;
                    v_x_2050_ = v_tail_2052_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg___boxed(
    mut v_x_2055_: *mut leanh::LeanObject,
    mut v_x_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2057_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_2055_, v_x_2056_);
    leanh::lean_dec(v_x_2056_);
    return v_res_2057_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(
    mut v_n_2058_: *mut leanh::LeanObject,
    mut v_assignments_2059_: *mut leanh::LeanObject,
    mut v_derivedLits_2060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2061_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_2059_, v_derivedLits_2060_);
    return v___x_2061_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments___boxed(
    mut v_n_2062_: *mut leanh::LeanObject,
    mut v_assignments_2063_: *mut leanh::LeanObject,
    mut v_derivedLits_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2065_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments(
        v_n_2062_,
        v_assignments_2063_,
        v_derivedLits_2064_,
    );
    leanh::lean_dec(v_derivedLits_2064_);
    leanh::lean_dec(v_n_2062_);
    return v_res_2065_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(
    mut v_n_2066_: *mut leanh::LeanObject,
    mut v_x_2067_: *mut leanh::LeanObject,
    mut v_x_2068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2069_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_x_2067_, v_x_2068_);
    return v___x_2069_;
}
pub unsafe fn l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___boxed(
    mut v_n_2070_: *mut leanh::LeanObject,
    mut v_x_2071_: *mut leanh::LeanObject,
    mut v_x_2072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2073_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0(v_n_2070_, v_x_2071_, v_x_2072_);
    leanh::lean_dec(v_x_2072_);
    leanh::lean_dec(v_n_2070_);
    return v_res_2073_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(
    mut v_n_2074_: *mut leanh::LeanObject,
    mut v_clauses_2075_: *mut leanh::LeanObject,
    mut v_x_2076_: *mut leanh::LeanObject,
    mut v_id_2077_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: u8 = 0;
    let mut v_fst_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2085_: u8 = 0;
    let mut v___x_2086_: u8 = 0;
    let mut v_fst_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2090_: u8 = 0;
    let mut v_fst_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2094_: u8 = 0;
    let mut v___x_2095_: u8 = 0;
    let mut v___x_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: u8 = 0;
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: u8 = 0;
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: u8 = 0;
    let mut v___x_2119_: u8 = 0;
    let mut v___x_2120_: u8 = 0;
    let mut v___y_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: u8 = 0;
    let mut v_v_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: u8 = 0;
    let mut v___x_2135_: u8 = 0;
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2141_: u8 = 0;
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2147_: u8 = 0;
    let mut v_unused_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2158_: u8 = 0;
    let mut v_unused_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2160_: u8 = 0;
    let mut v_unused_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2162_: u8 = 0;
    let mut v_unused_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2078_ = leanh::lean_ctor_get(v_x_2076_, 1);
                leanh::lean_inc(v_snd_2078_);
                v_snd_2079_ = leanh::lean_ctor_get(v_snd_2078_, 1);
                leanh::lean_inc(v_snd_2079_);
                v_snd_2080_ = leanh::lean_ctor_get(v_snd_2079_, 1);
                v___x_2081_ = (leanh::lean_unbox(v_snd_2080_) as u8);
                if v___x_2081_ == 0 {
                    v_fst_2082_ = leanh::lean_ctor_get(v_snd_2079_, 0);
                    v_isSharedCheck_2162_ = (!leanh::lean_is_exclusive(v_snd_2079_)) as u8;
                    if v_isSharedCheck_2162_ == 0 {
                        v_unused_2163_ = leanh::lean_ctor_get(v_snd_2079_, 1);
                        leanh::lean_dec(v_unused_2163_);
                        v___x_2084_ = v_snd_2079_;
                        v_isShared_2085_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2082_);
                        leanh::lean_dec(v_snd_2079_);
                        v___x_2084_ = leanh::lean_box(0);
                        v_isShared_2085_ = v_isSharedCheck_2162_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_2079_);
                    leanh::lean_dec(v_snd_2078_);
                    return v_x_2076_;
                }
            }
            1 => {
                v___x_2086_ = (leanh::lean_unbox(v_fst_2082_) as u8);
                if v___x_2086_ == 0 {
                    v_fst_2087_ = leanh::lean_ctor_get(v_x_2076_, 0);
                    v_isSharedCheck_2160_ = (!leanh::lean_is_exclusive(v_x_2076_)) as u8;
                    if v_isSharedCheck_2160_ == 0 {
                        v_unused_2161_ = leanh::lean_ctor_get(v_x_2076_, 1);
                        leanh::lean_dec(v_unused_2161_);
                        v___x_2089_ = v_x_2076_;
                        v_isShared_2090_ = v_isSharedCheck_2160_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2087_);
                        leanh::lean_dec(v_x_2076_);
                        v___x_2089_ = leanh::lean_box(0);
                        v_isShared_2090_ = v_isSharedCheck_2160_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2084_);
                    leanh::lean_dec(v_fst_2082_);
                    leanh::lean_dec(v_snd_2078_);
                    return v_x_2076_;
                }
            }
            2 => {
                v_fst_2091_ = leanh::lean_ctor_get(v_snd_2078_, 0);
                v_isSharedCheck_2158_ = (!leanh::lean_is_exclusive(v_snd_2078_)) as u8;
                if v_isSharedCheck_2158_ == 0 {
                    v_unused_2159_ = leanh::lean_ctor_get(v_snd_2078_, 1);
                    leanh::lean_dec(v_unused_2159_);
                    v___x_2093_ = v_snd_2078_;
                    v_isShared_2094_ = v_isSharedCheck_2158_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2091_);
                    leanh::lean_dec(v_snd_2078_);
                    v___x_2093_ = leanh::lean_box(0);
                    v_isShared_2094_ = v_isSharedCheck_2158_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2095_ = 1;
                v___x_2107_ = lean_array_get_size(v_clauses_2075_);
                v___x_2108_ = lean_nat_dec_lt(v_id_2077_, v___x_2107_);
                if v___x_2108_ == 0 {
                    state = 4;
                    continue;
                } else {
                    v___x_2109_ = lean_array_fget_borrowed(v_clauses_2075_, v_id_2077_);
                    if leanh::lean_obj_tag(v___x_2109_) == 0 {
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2093_);
                        leanh::lean_del_object(v___x_2089_);
                        leanh::lean_del_object(v___x_2084_);
                        v_val_2110_ = leanh::lean_ctor_get(v___x_2109_, 0);
                        leanh::lean_inc(v_val_2110_);
                        v___x_2111_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultClause_reduce(
                            v_n_2074_,
                            v_val_2110_,
                            v_fst_2087_,
                        );
                        match leanh::lean_obj_tag(v___x_2111_) {
                            2 => {
                                v_l_2112_ = leanh::lean_ctor_get(v___x_2111_, 0);
                                leanh::lean_inc_ref(v_l_2112_);
                                leanh::lean_dec_ref_known(v___x_2111_, 1);
                                v_fst_2113_ = leanh::lean_ctor_get(v_l_2112_, 0);
                                v_snd_2114_ = leanh::lean_ctor_get(v_l_2112_, 1);
                                v___x_2115_ = 0;
                                v___x_2116_ = leanh::lean_box((v___x_2115_) as usize);
                                v___x_2117_ = lean_array_get(v___x_2116_, v_fst_2087_, v_fst_2113_);
                                leanh::lean_dec(v___x_2116_);
                                v___x_2118_ = (leanh::lean_unbox(v_snd_2114_) as u8);
                                v___x_2119_ = (leanh::lean_unbox(v___x_2117_) as u8);
                                leanh::lean_dec(v___x_2117_);
                                v___x_2120_ =
                                    l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_hasAssignment(
                                        v___x_2118_,
                                        v___x_2119_,
                                    );
                                if v___x_2120_ == 0 {
                                    leanh::lean_dec(v_fst_2082_);
                                    v___x_2129_ = lean_array_get_size(v_fst_2087_);
                                    v___x_2130_ = lean_nat_dec_lt(v_fst_2113_, v___x_2129_);
                                    if v___x_2130_ == 0 {
                                        v___y_2122_ = v_fst_2087_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v_v_2131_ = lean_array_fget(v_fst_2087_, v_fst_2113_);
                                        v___x_2132_ = leanh::lean_box(0);
                                        v_xs_x27_2133_ =
                                            lean_array_fset(v_fst_2087_, v_fst_2113_, v___x_2132_);
                                        v___x_2134_ = (leanh::lean_unbox(v_snd_2114_) as u8);
                                        v___x_2135_ = (leanh::lean_unbox(v_v_2131_) as u8);
                                        leanh::lean_dec(v_v_2131_);
                                        v___x_2136_ = l_Std_Tactic_BVDecide_LRAT_Internal_Assignment_addAssignment(v___x_2134_, v___x_2135_);
                                        v___x_2137_ =
                                            leanh::lean_box((v___x_2136_) as usize);
                                        v___x_2138_ = lean_array_fset(
                                            v_xs_x27_2133_,
                                            v_fst_2113_,
                                            v___x_2137_,
                                        );
                                        v___y_2122_ = v___x_2138_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    v_isSharedCheck_2147_ =
                                        (!leanh::lean_is_exclusive(v_l_2112_)) as u8;
                                    if v_isSharedCheck_2147_ == 0 {
                                        v_unused_2148_ = leanh::lean_ctor_get(v_l_2112_, 1);
                                        leanh::lean_dec(v_unused_2148_);
                                        v_unused_2149_ = leanh::lean_ctor_get(v_l_2112_, 0);
                                        leanh::lean_dec(v_unused_2149_);
                                        v___x_2140_ = v_l_2112_;
                                        v_isShared_2141_ = v_isSharedCheck_2147_;
                                        state = 9;
                                        continue;
                                    } else {
                                        leanh::lean_dec(v_l_2112_);
                                        v___x_2140_ = leanh::lean_box(0);
                                        v_isShared_2141_ = v_isSharedCheck_2147_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                            3 => {
                                v___x_2150_ = leanh::lean_box((v___x_2095_) as usize);
                                v___x_2151_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2151_, 0, v_fst_2082_);
                                leanh::lean_ctor_set(v___x_2151_, 1, v___x_2150_);
                                v___x_2152_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2152_, 0, v_fst_2091_);
                                leanh::lean_ctor_set(v___x_2152_, 1, v___x_2151_);
                                v___x_2153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2153_, 0, v_fst_2087_);
                                leanh::lean_ctor_set(v___x_2153_, 1, v___x_2152_);
                                return v___x_2153_;
                            }
                            _ => {
                                leanh::lean_dec(v___x_2111_);
                                v___x_2154_ = leanh::lean_box((v___x_2095_) as usize);
                                v___x_2155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2155_, 0, v___x_2154_);
                                leanh::lean_ctor_set(v___x_2155_, 1, v_fst_2082_);
                                v___x_2156_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2156_, 0, v_fst_2091_);
                                leanh::lean_ctor_set(v___x_2156_, 1, v___x_2155_);
                                v___x_2157_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2157_, 0, v_fst_2087_);
                                leanh::lean_ctor_set(v___x_2157_, 1, v___x_2156_);
                                return v___x_2157_;
                            }
                        }
                    }
                }
            }
            4 => {
                v___x_2097_ = leanh::lean_box((v___x_2095_) as usize);
                if v_isShared_2085_ == 0 {
                    leanh::lean_ctor_set(v___x_2084_, 1, v___x_2097_);
                    v___x_2099_ = v___x_2084_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 0, v_fst_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2106_, 1, v___x_2097_);
                    v___x_2099_ = v_reuseFailAlloc_2106_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_2094_ == 0 {
                    leanh::lean_ctor_set(v___x_2093_, 1, v___x_2099_);
                    v___x_2101_ = v___x_2093_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_fst_2091_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2105_, 1, v___x_2099_);
                    v___x_2101_ = v_reuseFailAlloc_2105_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2090_ == 0 {
                    leanh::lean_ctor_set(v___x_2089_, 1, v___x_2101_);
                    v___x_2103_ = v___x_2089_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 0, v_fst_2087_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2104_, 1, v___x_2101_);
                    v___x_2103_ = v_reuseFailAlloc_2104_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2103_;
            }
            8 => {
                v___x_2123_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2123_, 0, v_l_2112_);
                leanh::lean_ctor_set(v___x_2123_, 1, v_fst_2091_);
                v___x_2124_ = leanh::lean_box((v___x_2120_) as usize);
                v___x_2125_ = leanh::lean_box((v___x_2120_) as usize);
                v___x_2126_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2126_, 0, v___x_2124_);
                leanh::lean_ctor_set(v___x_2126_, 1, v___x_2125_);
                v___x_2127_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2127_, 0, v___x_2123_);
                leanh::lean_ctor_set(v___x_2127_, 1, v___x_2126_);
                v___x_2128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2128_, 0, v___y_2122_);
                leanh::lean_ctor_set(v___x_2128_, 1, v___x_2127_);
                return v___x_2128_;
            }
            9 => {
                leanh::lean_inc(v_fst_2082_);
                if v_isShared_2141_ == 0 {
                    leanh::lean_ctor_set(v___x_2140_, 1, v_fst_2082_);
                    leanh::lean_ctor_set(v___x_2140_, 0, v_fst_2082_);
                    v___x_2143_ = v___x_2140_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 0, v_fst_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2146_, 1, v_fst_2082_);
                    v___x_2143_ = v_reuseFailAlloc_2146_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2144_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2144_, 0, v_fst_2091_);
                leanh::lean_ctor_set(v___x_2144_, 1, v___x_2143_);
                v___x_2145_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2145_, 0, v_fst_2087_);
                leanh::lean_ctor_set(v___x_2145_, 1, v___x_2144_);
                return v___x_2145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint___boxed(
    mut v_n_2164_: *mut leanh::LeanObject,
    mut v_clauses_2165_: *mut leanh::LeanObject,
    mut v_x_2166_: *mut leanh::LeanObject,
    mut v_id_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2168_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(
        v_n_2164_,
        v_clauses_2165_,
        v_x_2166_,
        v_id_2167_,
    );
    leanh::lean_dec(v_id_2167_);
    leanh::lean_dec_ref(v_clauses_2165_);
    leanh::lean_dec(v_n_2164_);
    return v_res_2168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(
    mut v_n_2169_: *mut leanh::LeanObject,
    mut v_clauses_2170_: *mut leanh::LeanObject,
    mut v_as_2171_: *mut leanh::LeanObject,
    mut v_i_2172_: usize,
    mut v_stop_2173_: usize,
    mut v_b_2174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2175_: u8 = 0;
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2175_ = lean_usize_dec_eq(v_i_2172_, v_stop_2173_);
                if v___x_2175_ == 0 {
                    v___x_2176_ = lean_array_uget_borrowed(v_as_2171_, v_i_2172_);
                    v___x_2177_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_confirmRupHint(
                        v_n_2169_,
                        v_clauses_2170_,
                        v_b_2174_,
                        v___x_2176_,
                    );
                    v___x_2178_ = 1usize;
                    v___x_2179_ = lean_usize_add(v_i_2172_, v___x_2178_);
                    v_i_2172_ = v___x_2179_;
                    v_b_2174_ = v___x_2177_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2174_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0___boxed(
    mut v_n_2181_: *mut leanh::LeanObject,
    mut v_clauses_2182_: *mut leanh::LeanObject,
    mut v_as_2183_: *mut leanh::LeanObject,
    mut v_i_2184_: *mut leanh::LeanObject,
    mut v_stop_2185_: *mut leanh::LeanObject,
    mut v_b_2186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2187_: usize = 0;
    let mut v_stop_boxed_2188_: usize = 0;
    let mut v_res_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2187_ = leanh::lean_unbox_usize(v_i_2184_);
    leanh::lean_dec(v_i_2184_);
    v_stop_boxed_2188_ = leanh::lean_unbox_usize(v_stop_2185_);
    leanh::lean_dec(v_stop_2185_);
    v_res_2189_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_2181_, v_clauses_2182_, v_as_2183_, v_i_boxed_2187_, v_stop_boxed_2188_, v_b_2186_);
    leanh::lean_dec_ref(v_as_2183_);
    leanh::lean_dec_ref(v_clauses_2182_);
    leanh::lean_dec(v_n_2181_);
    return v_res_2189_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(
    mut v_n_2197_: *mut leanh::LeanObject,
    mut v_f_2198_: *mut leanh::LeanObject,
    mut v_rupHints_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2206_: u8 = 0;
    let mut v_fst_2208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: u8 = 0;
    let mut v___x_2222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2224_: usize = 0;
    let mut v___x_2225_: usize = 0;
    let mut v___x_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2230_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_2200_ = leanh::lean_ctor_get(v_f_2198_, 0);
                v_rupUnits_2201_ = leanh::lean_ctor_get(v_f_2198_, 1);
                v_ratUnits_2202_ = leanh::lean_ctor_get(v_f_2198_, 2);
                v_assignments_2203_ = leanh::lean_ctor_get(v_f_2198_, 3);
                v_isSharedCheck_2230_ = (!leanh::lean_is_exclusive(v_f_2198_)) as u8;
                if v_isSharedCheck_2230_ == 0 {
                    v___x_2205_ = v_f_2198_;
                    v_isShared_2206_ = v_isSharedCheck_2230_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_2203_);
                    leanh::lean_inc(v_ratUnits_2202_);
                    leanh::lean_inc(v_rupUnits_2201_);
                    leanh::lean_inc(v_clauses_2200_);
                    leanh::lean_dec(v_f_2198_);
                    v___x_2205_ = leanh::lean_box(0);
                    v_isShared_2206_ = v_isSharedCheck_2230_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2218_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___closed__1;
                v___x_2219_ = leanh::lean_unsigned_to_nat(0);
                v___x_2220_ = lean_array_get_size(v_rupHints_2199_);
                v___x_2221_ = lean_nat_dec_lt(v___x_2219_, v___x_2220_);
                if v___x_2221_ == 0 {
                    v_fst_2208_ = v_assignments_2203_;
                    v_snd_2209_ = v___x_2218_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_assignments_2203_);
                    v___x_2222_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2222_, 0, v_assignments_2203_);
                    leanh::lean_ctor_set(v___x_2222_, 1, v___x_2218_);
                    v___x_2223_ = lean_nat_dec_le(v___x_2220_, v___x_2220_);
                    if v___x_2223_ == 0 {
                        if v___x_2221_ == 0 {
                            leanh::lean_dec_ref_known(v___x_2222_, 2);
                            v_fst_2208_ = v_assignments_2203_;
                            v_snd_2209_ = v___x_2218_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_assignments_2203_);
                            v___x_2224_ = 0usize;
                            v___x_2225_ = lean_usize_of_nat(v___x_2220_);
                            v___x_2226_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_2197_, v_clauses_2200_, v_rupHints_2199_, v___x_2224_, v___x_2225_, v___x_2222_);
                            v___y_2215_ = v___x_2226_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_assignments_2203_);
                        v___x_2227_ = 0usize;
                        v___x_2228_ = lean_usize_of_nat(v___x_2220_);
                        v___x_2229_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck_spec__0(v_n_2197_, v_clauses_2200_, v_rupHints_2199_, v___x_2227_, v___x_2228_, v___x_2222_);
                        v___y_2215_ = v___x_2229_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2206_ == 0 {
                    leanh::lean_ctor_set(v___x_2205_, 3, v_fst_2208_);
                    v___x_2211_ = v___x_2205_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2213_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_clauses_2200_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_rupUnits_2201_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_ratUnits_2202_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2213_, 3, v_fst_2208_);
                    v___x_2211_ = v_reuseFailAlloc_2213_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2212_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2212_, 0, v___x_2211_);
                leanh::lean_ctor_set(v___x_2212_, 1, v_snd_2209_);
                return v___x_2212_;
            }
            4 => {
                v_fst_2216_ = leanh::lean_ctor_get(v___y_2215_, 0);
                leanh::lean_inc(v_fst_2216_);
                v_snd_2217_ = leanh::lean_ctor_get(v___y_2215_, 1);
                leanh::lean_inc(v_snd_2217_);
                leanh::lean_dec_ref(v___y_2215_);
                v_fst_2208_ = v_fst_2216_;
                v_snd_2209_ = v_snd_2217_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck___boxed(
    mut v_n_2231_: *mut leanh::LeanObject,
    mut v_f_2232_: *mut leanh::LeanObject,
    mut v_rupHints_2233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2234_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(
        v_n_2231_,
        v_f_2232_,
        v_rupHints_2233_,
    );
    leanh::lean_dec_ref(v_rupHints_2233_);
    leanh::lean_dec(v_n_2231_);
    return v_res_2234_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(
    mut v_a_2235_: *mut leanh::LeanObject,
    mut v_a_2236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2242_: u8 = 0;
    let mut v___y_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: u8 = 0;
    let mut v_fst_2251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v___x_2255_: u8 = 0;
    let mut v___x_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_unused_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2265_: u8 = 0;
    let mut v___x_2266_: u8 = 0;
    let mut v___x_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2271_: u8 = 0;
    let mut v_unused_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2273_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2235_) == 0 {
                    v___x_2237_ = l_List_reverse___redArg(v_a_2236_);
                    return v___x_2237_;
                } else {
                    v_head_2238_ = leanh::lean_ctor_get(v_a_2235_, 0);
                    v_tail_2239_ = leanh::lean_ctor_get(v_a_2235_, 1);
                    v_isSharedCheck_2273_ = (!leanh::lean_is_exclusive(v_a_2235_)) as u8;
                    if v_isSharedCheck_2273_ == 0 {
                        v___x_2241_ = v_a_2235_;
                        v_isShared_2242_ = v_isSharedCheck_2273_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2239_);
                        leanh::lean_inc(v_head_2238_);
                        leanh::lean_dec(v_a_2235_);
                        v___x_2241_ = leanh::lean_box(0);
                        v_isShared_2242_ = v_isSharedCheck_2273_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2249_ = leanh::lean_ctor_get(v_head_2238_, 1);
                v___x_2250_ = (leanh::lean_unbox(v_snd_2249_) as u8);
                if v___x_2250_ == 0 {
                    v_fst_2251_ = leanh::lean_ctor_get(v_head_2238_, 0);
                    v_isSharedCheck_2260_ = (!leanh::lean_is_exclusive(v_head_2238_)) as u8;
                    if v_isSharedCheck_2260_ == 0 {
                        v_unused_2261_ = leanh::lean_ctor_get(v_head_2238_, 1);
                        leanh::lean_dec(v_unused_2261_);
                        v___x_2253_ = v_head_2238_;
                        v_isShared_2254_ = v_isSharedCheck_2260_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2251_);
                        leanh::lean_dec(v_head_2238_);
                        v___x_2253_ = leanh::lean_box(0);
                        v_isShared_2254_ = v_isSharedCheck_2260_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_fst_2262_ = leanh::lean_ctor_get(v_head_2238_, 0);
                    v_isSharedCheck_2271_ = (!leanh::lean_is_exclusive(v_head_2238_)) as u8;
                    if v_isSharedCheck_2271_ == 0 {
                        v_unused_2272_ = leanh::lean_ctor_get(v_head_2238_, 1);
                        leanh::lean_dec(v_unused_2272_);
                        v___x_2264_ = v_head_2238_;
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2262_);
                        leanh::lean_dec(v_head_2238_);
                        v___x_2264_ = leanh::lean_box(0);
                        v_isShared_2265_ = v_isSharedCheck_2271_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2242_ == 0 {
                    leanh::lean_ctor_set(v___x_2241_, 1, v_a_2236_);
                    leanh::lean_ctor_set(v___x_2241_, 0, v___y_2244_);
                    v___x_2246_ = v___x_2241_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2248_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v___y_2244_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_a_2236_);
                    v___x_2246_ = v_reuseFailAlloc_2248_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_2235_ = v_tail_2239_;
                v_a_2236_ = v___x_2246_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2255_ = 1;
                v___x_2256_ = leanh::lean_box((v___x_2255_) as usize);
                if v_isShared_2254_ == 0 {
                    leanh::lean_ctor_set(v___x_2253_, 1, v___x_2256_);
                    v___x_2258_ = v___x_2253_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_fst_2251_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2259_, 1, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2244_ = v___x_2258_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2266_ = 0;
                v___x_2267_ = leanh::lean_box((v___x_2266_) as usize);
                if v_isShared_2265_ == 0 {
                    leanh::lean_ctor_set(v___x_2264_, 1, v___x_2267_);
                    v___x_2269_ = v___x_2264_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2270_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 0, v_fst_2262_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2270_, 1, v___x_2267_);
                    v___x_2269_ = v_reuseFailAlloc_2270_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2244_ = v___x_2269_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(
    mut v_n_2274_: *mut leanh::LeanObject,
    mut v_f_2275_: *mut leanh::LeanObject,
    mut v_c_2276_: *mut leanh::LeanObject,
    mut v_rupHints_2277_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negC_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2285_: u8 = 0;
    let mut v___x_2286_: u8 = 0;
    let mut v___x_2287_: u8 = 0;
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2292_: u8 = 0;
    let mut v_fst_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2297_: u8 = 0;
    let mut v_fst_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_clauses_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2310_: u8 = 0;
    let mut v_assignments_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2321_: u8 = 0;
    let mut v_isSharedCheck_2322_: u8 = 0;
    let mut v_unused_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2326_: u8 = 0;
    let mut v_fst_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2331_: u8 = 0;
    let mut v_unused_2332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2340_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2278_ = leanh::lean_box(0);
                leanh::lean_inc(v_c_2276_);
                v_negC_2279_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v_c_2276_, v___x_2278_);
                v___x_2280_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(
                    v_n_2274_,
                    v_f_2275_,
                    v_negC_2279_,
                );
                v_fst_2281_ = leanh::lean_ctor_get(v___x_2280_, 0);
                v_snd_2282_ = leanh::lean_ctor_get(v___x_2280_, 1);
                v_isSharedCheck_2340_ = (!leanh::lean_is_exclusive(v___x_2280_)) as u8;
                if v_isSharedCheck_2340_ == 0 {
                    v___x_2284_ = v___x_2280_;
                    v_isShared_2285_ = v_isSharedCheck_2340_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2282_);
                    leanh::lean_inc(v_fst_2281_);
                    leanh::lean_dec(v___x_2280_);
                    v___x_2284_ = leanh::lean_box(0);
                    v_isShared_2285_ = v_isSharedCheck_2340_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2286_ = 1;
                v___x_2287_ = (leanh::lean_unbox(v_snd_2282_) as u8);
                if v___x_2287_ == 0 {
                    leanh::lean_del_object(v___x_2284_);
                    v___x_2288_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(
                            v_n_2274_,
                            v_fst_2281_,
                            v_rupHints_2277_,
                        );
                    v_snd_2289_ = leanh::lean_ctor_get(v___x_2288_, 1);
                    leanh::lean_inc(v_snd_2289_);
                    v_snd_2290_ = leanh::lean_ctor_get(v_snd_2289_, 1);
                    leanh::lean_inc(v_snd_2290_);
                    v_snd_2291_ = leanh::lean_ctor_get(v_snd_2290_, 1);
                    v___x_2292_ = (leanh::lean_unbox(v_snd_2291_) as u8);
                    if v___x_2292_ == 0 {
                        leanh::lean_inc(v_snd_2291_);
                        leanh::lean_dec(v_snd_2282_);
                        v_fst_2293_ = leanh::lean_ctor_get(v_snd_2290_, 0);
                        v_isSharedCheck_2322_ =
                            (!leanh::lean_is_exclusive(v_snd_2290_)) as u8;
                        if v_isSharedCheck_2322_ == 0 {
                            v_unused_2323_ = leanh::lean_ctor_get(v_snd_2290_, 1);
                            leanh::lean_dec(v_unused_2323_);
                            v___x_2295_ = v_snd_2290_;
                            v_isShared_2296_ = v_isSharedCheck_2322_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_2293_);
                            leanh::lean_dec(v_snd_2290_);
                            v___x_2295_ = leanh::lean_box(0);
                            v_isShared_2296_ = v_isSharedCheck_2322_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_2289_);
                        leanh::lean_dec(v_c_2276_);
                        v_isSharedCheck_2331_ =
                            (!leanh::lean_is_exclusive(v_snd_2290_)) as u8;
                        if v_isSharedCheck_2331_ == 0 {
                            v_unused_2332_ = leanh::lean_ctor_get(v_snd_2290_, 1);
                            leanh::lean_dec(v_unused_2332_);
                            v_unused_2333_ = leanh::lean_ctor_get(v_snd_2290_, 0);
                            leanh::lean_dec(v_unused_2333_);
                            v___x_2325_ = v_snd_2290_;
                            v_isShared_2326_ = v_isSharedCheck_2331_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_dec(v_snd_2290_);
                            v___x_2325_ = leanh::lean_box(0);
                            v_isShared_2326_ = v_isSharedCheck_2331_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_snd_2282_);
                    v_f_2334_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(
                        v_n_2274_,
                        v_fst_2281_,
                    );
                    v___x_2335_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(
                            v_f_2334_, v_c_2276_,
                        );
                    v___x_2336_ = leanh::lean_box((v___x_2286_) as usize);
                    if v_isShared_2285_ == 0 {
                        leanh::lean_ctor_set(v___x_2284_, 1, v___x_2336_);
                        leanh::lean_ctor_set(v___x_2284_, 0, v___x_2335_);
                        v___x_2338_ = v___x_2284_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2339_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2335_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2339_, 1, v___x_2336_);
                        v___x_2338_ = v_reuseFailAlloc_2339_;
                        state = 9;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2297_ = (leanh::lean_unbox(v_fst_2293_) as u8);
                leanh::lean_dec(v_fst_2293_);
                if v___x_2297_ == 0 {
                    leanh::lean_dec(v_snd_2289_);
                    leanh::lean_dec(v_c_2276_);
                    v_fst_2298_ = leanh::lean_ctor_get(v___x_2288_, 0);
                    leanh::lean_inc(v_fst_2298_);
                    leanh::lean_dec_ref(v___x_2288_);
                    if v_isShared_2296_ == 0 {
                        leanh::lean_ctor_set(v___x_2295_, 0, v_fst_2298_);
                        v___x_2300_ = v___x_2295_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_fst_2298_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_snd_2291_);
                        v___x_2300_ = v_reuseFailAlloc_2301_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_2291_);
                    v_fst_2302_ = leanh::lean_ctor_get(v___x_2288_, 0);
                    leanh::lean_inc(v_fst_2302_);
                    leanh::lean_dec_ref(v___x_2288_);
                    v_fst_2303_ = leanh::lean_ctor_get(v_snd_2289_, 0);
                    leanh::lean_inc(v_fst_2303_);
                    leanh::lean_dec(v_snd_2289_);
                    v_clauses_2304_ = leanh::lean_ctor_get(v_fst_2302_, 0);
                    v_rupUnits_2305_ = leanh::lean_ctor_get(v_fst_2302_, 1);
                    v_ratUnits_2306_ = leanh::lean_ctor_get(v_fst_2302_, 2);
                    v_assignments_2307_ = leanh::lean_ctor_get(v_fst_2302_, 3);
                    v_isSharedCheck_2321_ = (!leanh::lean_is_exclusive(v_fst_2302_)) as u8;
                    if v_isSharedCheck_2321_ == 0 {
                        v___x_2309_ = v_fst_2302_;
                        v_isShared_2310_ = v_isSharedCheck_2321_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_assignments_2307_);
                        leanh::lean_inc(v_ratUnits_2306_);
                        leanh::lean_inc(v_rupUnits_2305_);
                        leanh::lean_inc(v_clauses_2304_);
                        leanh::lean_dec(v_fst_2302_);
                        v___x_2309_ = leanh::lean_box(0);
                        v_isShared_2310_ = v_isSharedCheck_2321_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2300_;
            }
            4 => {
                v_assignments_2311_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_2307_, v_fst_2303_);
                leanh::lean_dec(v_fst_2303_);
                if v_isShared_2310_ == 0 {
                    leanh::lean_ctor_set(v___x_2309_, 3, v_assignments_2311_);
                    v___x_2313_ = v___x_2309_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2320_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 0, v_clauses_2304_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 1, v_rupUnits_2305_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 2, v_ratUnits_2306_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2320_, 3, v_assignments_2311_);
                    v___x_2313_ = v_reuseFailAlloc_2320_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_f_2314_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(
                    v_n_2274_,
                    v___x_2313_,
                );
                v___x_2315_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(
                    v_f_2314_, v_c_2276_,
                );
                v___x_2316_ = leanh::lean_box((v___x_2286_) as usize);
                if v_isShared_2296_ == 0 {
                    leanh::lean_ctor_set(v___x_2295_, 1, v___x_2316_);
                    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2315_);
                    v___x_2318_ = v___x_2295_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2315_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v___x_2316_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2318_;
            }
            7 => {
                v_fst_2327_ = leanh::lean_ctor_get(v___x_2288_, 0);
                leanh::lean_inc(v_fst_2327_);
                leanh::lean_dec_ref(v___x_2288_);
                if v_isShared_2326_ == 0 {
                    leanh::lean_ctor_set(v___x_2325_, 1, v_snd_2282_);
                    leanh::lean_ctor_set(v___x_2325_, 0, v_fst_2327_);
                    v___x_2329_ = v___x_2325_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2330_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_fst_2327_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_snd_2282_);
                    v___x_2329_ = v_reuseFailAlloc_2330_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2329_;
            }
            9 => {
                return v___x_2338_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd___boxed(
    mut v_n_2341_: *mut leanh::LeanObject,
    mut v_f_2342_: *mut leanh::LeanObject,
    mut v_c_2343_: *mut leanh::LeanObject,
    mut v_rupHints_2344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2345_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd(
        v_n_2341_,
        v_f_2342_,
        v_c_2343_,
        v_rupHints_2344_,
    );
    leanh::lean_dec_ref(v_rupHints_2344_);
    leanh::lean_dec(v_n_2341_);
    return v_res_2345_;
}
pub unsafe fn l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(
    mut v_a_2346_: *mut leanh::LeanObject,
    mut v_x_2347_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2348_: u8 = 0;
    let mut v_head_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2352_: u8 = 0;
    let mut v_fst_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u8 = 0;
    let mut v___x_2359_: u8 = 0;
    let mut v___x_2360_: u8 = 0;
    let mut v___x_2362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2347_) == 0 {
                    v___x_2348_ = 0;
                    return v___x_2348_;
                } else {
                    v_head_2349_ = leanh::lean_ctor_get(v_x_2347_, 0);
                    v_tail_2350_ = leanh::lean_ctor_get(v_x_2347_, 1);
                    v_fst_2354_ = leanh::lean_ctor_get(v_a_2346_, 0);
                    v_snd_2355_ = leanh::lean_ctor_get(v_a_2346_, 1);
                    v_fst_2356_ = leanh::lean_ctor_get(v_head_2349_, 0);
                    v_snd_2357_ = leanh::lean_ctor_get(v_head_2349_, 1);
                    v___x_2358_ = lean_nat_dec_eq(v_fst_2354_, v_fst_2356_);
                    if v___x_2358_ == 0 {
                        v___y_2352_ = v___x_2358_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2359_ = (leanh::lean_unbox(v_snd_2355_) as u8);
                        if v___x_2359_ == 0 {
                            v___x_2360_ = (leanh::lean_unbox(v_snd_2357_) as u8);
                            if v___x_2360_ == 0 {
                                v___y_2352_ = v___x_2358_;
                                state = 1;
                                continue;
                            } else {
                                v_x_2347_ = v_tail_2350_;
                                state = 0;
                                continue;
                            }
                        } else {
                            v___x_2362_ = (leanh::lean_unbox(v_snd_2357_) as u8);
                            v___y_2352_ = v___x_2362_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_2352_ == 0 {
                    v_x_2347_ = v_tail_2350_;
                    state = 0;
                    continue;
                } else {
                    return v___y_2352_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg___boxed(
    mut v_a_2363_: *mut leanh::LeanObject,
    mut v_x_2364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2365_: u8 = 0;
    let mut v_r_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2365_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_2363_, v_x_2364_);
    leanh::lean_dec(v_x_2364_);
    leanh::lean_dec_ref(v_a_2363_);
    v_r_2366_ = leanh::lean_box((v_res_2365_) as usize);
    return v_r_2366_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(
    mut v_clauses_2367_: *mut leanh::LeanObject,
    mut v_n_2368_: *mut leanh::LeanObject,
    mut v___y_2369_: *mut leanh::LeanObject,
    mut v_as_2370_: *mut leanh::LeanObject,
    mut v_i_2371_: usize,
    mut v_stop_2372_: usize,
    mut v_b_2373_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: usize = 0;
    let mut v___x_2377_: usize = 0;
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: u8 = 0;
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2379_ = lean_usize_dec_eq(v_i_2371_, v_stop_2372_);
                if v___x_2379_ == 0 {
                    v___x_2380_ = leanh::lean_box(0);
                    v___x_2381_ = lean_array_uget_borrowed(v_as_2370_, v_i_2371_);
                    v___x_2382_ =
                        lean_array_get_borrowed(v___x_2380_, v_clauses_2367_, v___x_2381_);
                    if leanh::lean_obj_tag(v___x_2382_) == 0 {
                        v___y_2375_ = v_b_2373_;
                        state = 1;
                        continue;
                    } else {
                        v_val_2383_ = leanh::lean_ctor_get(v___x_2382_, 0);
                        v___x_2384_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v___y_2369_, v_val_2383_);
                        if v___x_2384_ == 0 {
                            v___y_2375_ = v_b_2373_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v___x_2381_);
                            v___x_2385_ = lean_array_push(v_b_2373_, v___x_2381_);
                            v___y_2375_ = v___x_2385_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    return v_b_2373_;
                }
            }
            1 => {
                v___x_2376_ = 1usize;
                v___x_2377_ = lean_usize_add(v_i_2371_, v___x_2376_);
                v_i_2371_ = v___x_2377_;
                v_b_2373_ = v___y_2375_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1___boxed(
    mut v_clauses_2386_: *mut leanh::LeanObject,
    mut v_n_2387_: *mut leanh::LeanObject,
    mut v___y_2388_: *mut leanh::LeanObject,
    mut v_as_2389_: *mut leanh::LeanObject,
    mut v_i_2390_: *mut leanh::LeanObject,
    mut v_stop_2391_: *mut leanh::LeanObject,
    mut v_b_2392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2393_: usize = 0;
    let mut v_stop_boxed_2394_: usize = 0;
    let mut v_res_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2393_ = leanh::lean_unbox_usize(v_i_2390_);
    leanh::lean_dec(v_i_2390_);
    v_stop_boxed_2394_ = leanh::lean_unbox_usize(v_stop_2391_);
    leanh::lean_dec(v_stop_2391_);
    v_res_2395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_2386_, v_n_2387_, v___y_2388_, v_as_2389_, v_i_boxed_2393_, v_stop_boxed_2394_, v_b_2392_);
    leanh::lean_dec_ref(v_as_2389_);
    leanh::lean_dec_ref(v___y_2388_);
    leanh::lean_dec(v_n_2387_);
    leanh::lean_dec_ref(v_clauses_2386_);
    return v_res_2395_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(
    mut v_n_2398_: *mut leanh::LeanObject,
    mut v_clauses_2399_: *mut leanh::LeanObject,
    mut v_l_2400_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u8 = 0;
    let mut v___x_2409_: u8 = 0;
    let mut v___x_2410_: usize = 0;
    let mut v___x_2411_: usize = 0;
    let mut v___x_2412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: usize = 0;
    let mut v___x_2414_: usize = 0;
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: u8 = 0;
    let mut v_fst_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2421_: u8 = 0;
    let mut v___x_2422_: u8 = 0;
    let mut v___x_2423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2427_: u8 = 0;
    let mut v_unused_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2432_: u8 = 0;
    let mut v___x_2433_: u8 = 0;
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut v_unused_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_2416_ = leanh::lean_ctor_get(v_l_2400_, 1);
                v___x_2417_ = (leanh::lean_unbox(v_snd_2416_) as u8);
                if v___x_2417_ == 0 {
                    v_fst_2418_ = leanh::lean_ctor_get(v_l_2400_, 0);
                    v_isSharedCheck_2427_ = (!leanh::lean_is_exclusive(v_l_2400_)) as u8;
                    if v_isSharedCheck_2427_ == 0 {
                        v_unused_2428_ = leanh::lean_ctor_get(v_l_2400_, 1);
                        leanh::lean_dec(v_unused_2428_);
                        v___x_2420_ = v_l_2400_;
                        v_isShared_2421_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2418_);
                        leanh::lean_dec(v_l_2400_);
                        v___x_2420_ = leanh::lean_box(0);
                        v_isShared_2421_ = v_isSharedCheck_2427_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_fst_2429_ = leanh::lean_ctor_get(v_l_2400_, 0);
                    v_isSharedCheck_2438_ = (!leanh::lean_is_exclusive(v_l_2400_)) as u8;
                    if v_isSharedCheck_2438_ == 0 {
                        v_unused_2439_ = leanh::lean_ctor_get(v_l_2400_, 1);
                        leanh::lean_dec(v_unused_2439_);
                        v___x_2431_ = v_l_2400_;
                        v_isShared_2432_ = v_isSharedCheck_2438_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2429_);
                        leanh::lean_dec(v_l_2400_);
                        v___x_2431_ = leanh::lean_box(0);
                        v_isShared_2432_ = v_isSharedCheck_2438_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2403_ = lean_array_get_size(v_clauses_2399_);
                v___x_2404_ = l_Array_range(v___x_2403_);
                v___x_2405_ = leanh::lean_unsigned_to_nat(0);
                v___x_2406_ = lean_array_get_size(v___x_2404_);
                v___x_2407_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___closed__0;
                v___x_2408_ = lean_nat_dec_lt(v___x_2405_, v___x_2406_);
                if v___x_2408_ == 0 {
                    leanh::lean_dec_ref(v___x_2404_);
                    leanh::lean_dec_ref(v___y_2402_);
                    return v___x_2407_;
                } else {
                    v___x_2409_ = lean_nat_dec_le(v___x_2406_, v___x_2406_);
                    if v___x_2409_ == 0 {
                        if v___x_2408_ == 0 {
                            leanh::lean_dec_ref(v___x_2404_);
                            leanh::lean_dec_ref(v___y_2402_);
                            return v___x_2407_;
                        } else {
                            v___x_2410_ = 0usize;
                            v___x_2411_ = lean_usize_of_nat(v___x_2406_);
                            v___x_2412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_2399_, v_n_2398_, v___y_2402_, v___x_2404_, v___x_2410_, v___x_2411_, v___x_2407_);
                            leanh::lean_dec_ref(v___x_2404_);
                            leanh::lean_dec_ref(v___y_2402_);
                            return v___x_2412_;
                        }
                    } else {
                        v___x_2413_ = 0usize;
                        v___x_2414_ = lean_usize_of_nat(v___x_2406_);
                        v___x_2415_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__1(v_clauses_2399_, v_n_2398_, v___y_2402_, v___x_2404_, v___x_2413_, v___x_2414_, v___x_2407_);
                        leanh::lean_dec_ref(v___x_2404_);
                        leanh::lean_dec_ref(v___y_2402_);
                        return v___x_2415_;
                    }
                }
            }
            2 => {
                v___x_2422_ = 1;
                v___x_2423_ = leanh::lean_box((v___x_2422_) as usize);
                if v_isShared_2421_ == 0 {
                    leanh::lean_ctor_set(v___x_2420_, 1, v___x_2423_);
                    v___x_2425_ = v___x_2420_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v_fst_2418_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v___x_2423_);
                    v___x_2425_ = v_reuseFailAlloc_2426_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_2402_ = v___x_2425_;
                state = 1;
                continue;
            }
            4 => {
                v___x_2433_ = 0;
                v___x_2434_ = leanh::lean_box((v___x_2433_) as usize);
                if v_isShared_2432_ == 0 {
                    leanh::lean_ctor_set(v___x_2431_, 1, v___x_2434_);
                    v___x_2436_ = v___x_2431_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v_fst_2429_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v___x_2434_);
                    v___x_2436_ = v_reuseFailAlloc_2437_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2402_ = v___x_2436_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices___boxed(
    mut v_n_2440_: *mut leanh::LeanObject,
    mut v_clauses_2441_: *mut leanh::LeanObject,
    mut v_l_2442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2443_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(
        v_n_2440_,
        v_clauses_2441_,
        v_l_2442_,
    );
    leanh::lean_dec_ref(v_clauses_2441_);
    leanh::lean_dec(v_n_2440_);
    return v_res_2443_;
}
pub unsafe fn l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(
    mut v_n_2444_: *mut leanh::LeanObject,
    mut v_a_2445_: *mut leanh::LeanObject,
    mut v_x_2446_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2447_: u8 = 0;
    v___x_2447_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___redArg(v_a_2445_, v_x_2446_);
    return v___x_2447_;
}
pub unsafe fn l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0___boxed(
    mut v_n_2448_: *mut leanh::LeanObject,
    mut v_a_2449_: *mut leanh::LeanObject,
    mut v_x_2450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2451_: u8 = 0;
    let mut v_r_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2451_ = l_List_elem___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices_spec__0(v_n_2448_, v_a_2449_, v_x_2450_);
    leanh::lean_dec(v_x_2450_);
    leanh::lean_dec_ref(v_a_2449_);
    leanh::lean_dec(v_n_2448_);
    v_r_2452_ = leanh::lean_box((v_res_2451_) as usize);
    return v_r_2452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(
    mut v_sz_2453_: usize,
    mut v_i_2454_: usize,
    mut v_bs_2455_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2456_: u8 = 0;
    let mut v_v_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: usize = 0;
    let mut v___x_2462_: usize = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2456_ = lean_usize_dec_lt(v_i_2454_, v_sz_2453_);
                if v___x_2456_ == 0 {
                    return v_bs_2455_;
                } else {
                    v_v_2457_ = lean_array_uget_borrowed(v_bs_2455_, v_i_2454_);
                    v_fst_2458_ = leanh::lean_ctor_get(v_v_2457_, 0);
                    leanh::lean_inc(v_fst_2458_);
                    v___x_2459_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_2460_ = lean_array_uset(v_bs_2455_, v_i_2454_, v___x_2459_);
                    v___x_2461_ = 1usize;
                    v___x_2462_ = lean_usize_add(v_i_2454_, v___x_2461_);
                    v___x_2463_ = lean_array_uset(v_bs_x27_2460_, v_i_2454_, v_fst_2458_);
                    v_i_2454_ = v___x_2462_;
                    v_bs_2455_ = v___x_2463_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0___boxed(
    mut v_sz_2465_: *mut leanh::LeanObject,
    mut v_i_2466_: *mut leanh::LeanObject,
    mut v_bs_2467_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2468_: usize = 0;
    let mut v_i_boxed_2469_: usize = 0;
    let mut v_res_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2468_ = leanh::lean_unbox_usize(v_sz_2465_);
    leanh::lean_dec(v_sz_2465_);
    v_i_boxed_2469_ = leanh::lean_unbox_usize(v_i_2466_);
    leanh::lean_dec(v_i_2466_);
    v_res_2470_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_boxed_2468_, v_i_boxed_2469_, v_bs_2467_);
    return v_res_2470_;
}
pub unsafe fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(
    mut v_xs_2471_: *mut leanh::LeanObject,
    mut v_ys_2472_: *mut leanh::LeanObject,
    mut v_x_2473_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_2474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_2475_: u8 = 0;
    let mut v_one_2476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_2474_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_2475_ = lean_nat_dec_eq(v_x_2473_, v_zero_2474_);
                if v_isZero_2475_ == 1 {
                    leanh::lean_dec(v_x_2473_);
                    return v_isZero_2475_;
                } else {
                    v_one_2476_ = leanh::lean_unsigned_to_nat(1);
                    v_n_2477_ = lean_nat_sub(v_x_2473_, v_one_2476_);
                    leanh::lean_dec(v_x_2473_);
                    v___x_2478_ = lean_array_fget_borrowed(v_xs_2471_, v_n_2477_);
                    v___x_2479_ = lean_array_fget_borrowed(v_ys_2472_, v_n_2477_);
                    v___x_2480_ = lean_nat_dec_eq(v___x_2478_, v___x_2479_);
                    if v___x_2480_ == 0 {
                        leanh::lean_dec(v_n_2477_);
                        return v___x_2480_;
                    } else {
                        v_x_2473_ = v_n_2477_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg___boxed(
    mut v_xs_2482_: *mut leanh::LeanObject,
    mut v_ys_2483_: *mut leanh::LeanObject,
    mut v_x_2484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2485_: u8 = 0;
    let mut v_r_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2485_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_2482_, v_ys_2483_, v_x_2484_);
    leanh::lean_dec_ref(v_ys_2483_);
    leanh::lean_dec_ref(v_xs_2482_);
    v_r_2486_ = leanh::lean_box((v_res_2485_) as usize);
    return v_r_2486_;
}
pub unsafe fn l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(
    mut v_xs_2487_: *mut leanh::LeanObject,
    mut v_ys_2488_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: u8 = 0;
    v___x_2489_ = lean_array_get_size(v_xs_2487_);
    v___x_2490_ = lean_array_get_size(v_ys_2488_);
    v___x_2491_ = lean_nat_dec_eq(v___x_2489_, v___x_2490_);
    if v___x_2491_ == 0 {
        return v___x_2491_;
    } else {
        let mut v___x_2492_: u8 = 0;
        v___x_2492_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_2487_, v_ys_2488_, v___x_2489_);
        return v___x_2492_;
    }
}
pub unsafe fn l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1___boxed(
    mut v_xs_2493_: *mut leanh::LeanObject,
    mut v_ys_2494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2495_: u8 = 0;
    let mut v_r_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2495_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_xs_2493_, v_ys_2494_);
    leanh::lean_dec_ref(v_ys_2494_);
    leanh::lean_dec_ref(v_xs_2493_);
    v_r_2496_ = leanh::lean_box((v_res_2495_) as usize);
    return v_r_2496_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(
    mut v_n_2497_: *mut leanh::LeanObject,
    mut v_f_2498_: *mut leanh::LeanObject,
    mut v_pivot_2499_: *mut leanh::LeanObject,
    mut v_ratHints_2500_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_clauses_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratClauseIndices_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2503_: usize = 0;
    let mut v___x_2504_: usize = 0;
    let mut v_ratHintIndices_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: u8 = 0;
    v_clauses_2501_ = leanh::lean_ctor_get(v_f_2498_, 0);
    v_ratClauseIndices_2502_ =
        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_getRatClauseIndices(
            v_n_2497_,
            v_clauses_2501_,
            v_pivot_2499_,
        );
    v_sz_2503_ = lean_array_size(v_ratHints_2500_);
    v___x_2504_ = 0usize;
    v_ratHintIndices_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__0(v_sz_2503_, v___x_2504_, v_ratHints_2500_);
    v___x_2506_ = l_Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1(v_ratClauseIndices_2502_, v_ratHintIndices_2505_);
    leanh::lean_dec_ref(v_ratHintIndices_2505_);
    leanh::lean_dec_ref(v_ratClauseIndices_2502_);
    return v___x_2506_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive___boxed(
    mut v_n_2507_: *mut leanh::LeanObject,
    mut v_f_2508_: *mut leanh::LeanObject,
    mut v_pivot_2509_: *mut leanh::LeanObject,
    mut v_ratHints_2510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2511_: u8 = 0;
    let mut v_r_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2511_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(
        v_n_2507_,
        v_f_2508_,
        v_pivot_2509_,
        v_ratHints_2510_,
    );
    leanh::lean_dec_ref(v_f_2508_);
    leanh::lean_dec(v_n_2507_);
    v_r_2512_ = leanh::lean_box((v_res_2511_) as usize);
    return v_r_2512_;
}
pub unsafe fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(
    mut v_xs_2513_: *mut leanh::LeanObject,
    mut v_ys_2514_: *mut leanh::LeanObject,
    mut v_hsz_2515_: *mut leanh::LeanObject,
    mut v_x_2516_: *mut leanh::LeanObject,
    mut v_x_2517_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2518_: u8 = 0;
    v___x_2518_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___redArg(v_xs_2513_, v_ys_2514_, v_x_2516_);
    return v___x_2518_;
}
pub unsafe fn l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1___boxed(
    mut v_xs_2519_: *mut leanh::LeanObject,
    mut v_ys_2520_: *mut leanh::LeanObject,
    mut v_hsz_2521_: *mut leanh::LeanObject,
    mut v_x_2522_: *mut leanh::LeanObject,
    mut v_x_2523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2524_: u8 = 0;
    let mut v_r_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2524_ = l_Array_isEqvAux___at___00Array_instDecidableEqImpl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive_spec__1_spec__1(v_xs_2519_, v_ys_2520_, v_hsz_2521_, v_x_2522_, v_x_2523_);
    leanh::lean_dec_ref(v_ys_2520_);
    leanh::lean_dec_ref(v_xs_2519_);
    v_r_2525_ = leanh::lean_box((v_res_2524_) as usize);
    return v_r_2525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(
    mut v_as_2526_: *mut leanh::LeanObject,
    mut v_i_2527_: usize,
    mut v_stop_2528_: usize,
    mut v_b_2529_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2530_: u8 = 0;
    let mut v___x_2531_: usize = 0;
    let mut v___x_2532_: usize = 0;
    let mut v___x_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2530_ = lean_usize_dec_eq(v_i_2527_, v_stop_2528_);
                if v___x_2530_ == 0 {
                    v___x_2531_ = 1usize;
                    v___x_2532_ = lean_usize_sub(v_i_2527_, v___x_2531_);
                    v___x_2533_ = lean_array_uget_borrowed(v_as_2526_, v___x_2532_);
                    leanh::lean_inc(v___x_2533_);
                    v___x_2534_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2534_, 0, v___x_2533_);
                    leanh::lean_ctor_set(v___x_2534_, 1, v_b_2529_);
                    v_i_2527_ = v___x_2532_;
                    v_b_2529_ = v___x_2534_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2529_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0___boxed(
    mut v_as_2536_: *mut leanh::LeanObject,
    mut v_i_2537_: *mut leanh::LeanObject,
    mut v_stop_2538_: *mut leanh::LeanObject,
    mut v_b_2539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_2540_: usize = 0;
    let mut v_stop_boxed_2541_: usize = 0;
    let mut v_res_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2540_ = leanh::lean_unbox_usize(v_i_2537_);
    leanh::lean_dec(v_i_2537_);
    v_stop_boxed_2541_ = leanh::lean_unbox_usize(v_stop_2538_);
    leanh::lean_dec(v_stop_2538_);
    v_res_2542_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_as_2536_, v_i_boxed_2540_, v_stop_boxed_2541_, v_b_2539_);
    leanh::lean_dec_ref(v_as_2536_);
    return v_res_2542_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(
    mut v_l_2543_: *mut leanh::LeanObject,
    mut v_a_2544_: *mut leanh::LeanObject,
    mut v_a_2545_: *mut leanh::LeanObject,
    mut v_a_2546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2553_: u8 = 0;
    let mut v___x_2554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: u8 = 0;
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: usize = 0;
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: u8 = 0;
    let mut v___x_2565_: u8 = 0;
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2545_) == 0 {
                    leanh::lean_dec_ref(v_a_2546_);
                    leanh::lean_inc(v_l_2543_);
                    return v_l_2543_;
                } else {
                    v_head_2547_ = leanh::lean_ctor_get(v_a_2545_, 0);
                    leanh::lean_inc(v_head_2547_);
                    v_tail_2548_ = leanh::lean_ctor_get(v_a_2545_, 1);
                    leanh::lean_inc(v_tail_2548_);
                    leanh::lean_dec_ref_known(v_a_2545_, 2);
                    v_fst_2560_ = leanh::lean_ctor_get(v_head_2547_, 0);
                    v_snd_2561_ = leanh::lean_ctor_get(v_head_2547_, 1);
                    v_fst_2562_ = leanh::lean_ctor_get(v_a_2544_, 0);
                    v_snd_2563_ = leanh::lean_ctor_get(v_a_2544_, 1);
                    v___x_2564_ = lean_nat_dec_eq(v_fst_2560_, v_fst_2562_);
                    if v___x_2564_ == 0 {
                        v___y_2553_ = v___x_2564_;
                        state = 2;
                        continue;
                    } else {
                        v___x_2565_ = (leanh::lean_unbox(v_snd_2561_) as u8);
                        if v___x_2565_ == 0 {
                            v___x_2566_ = (leanh::lean_unbox(v_snd_2563_) as u8);
                            if v___x_2566_ == 0 {
                                v___y_2553_ = v___x_2564_;
                                state = 2;
                                continue;
                            } else {
                                state = 1;
                                continue;
                            }
                        } else {
                            v___x_2567_ = (leanh::lean_unbox(v_snd_2563_) as u8);
                            v___y_2553_ = v___x_2567_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2550_ = lean_array_push(v_a_2546_, v_head_2547_);
                v_a_2545_ = v_tail_2548_;
                v_a_2546_ = v___x_2550_;
                state = 0;
                continue;
            }
            2 => {
                if v___y_2553_ == 0 {
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_head_2547_);
                    v___x_2554_ = lean_array_get_size(v_a_2546_);
                    v___x_2555_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2556_ = lean_nat_dec_lt(v___x_2555_, v___x_2554_);
                    if v___x_2556_ == 0 {
                        leanh::lean_dec_ref(v_a_2546_);
                        return v_tail_2548_;
                    } else {
                        v___x_2557_ = lean_usize_of_nat(v___x_2554_);
                        v___x_2558_ = 0usize;
                        v___x_2559_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00__private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0_spec__0(v_a_2546_, v___x_2557_, v___x_2558_, v_tail_2548_);
                        leanh::lean_dec_ref(v_a_2546_);
                        return v___x_2559_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg___boxed(
    mut v_l_2568_: *mut leanh::LeanObject,
    mut v_a_2569_: *mut leanh::LeanObject,
    mut v_a_2570_: *mut leanh::LeanObject,
    mut v_a_2571_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2572_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_2568_, v_a_2569_, v_a_2570_, v_a_2571_);
    leanh::lean_dec_ref(v_a_2569_);
    leanh::lean_dec(v_l_2568_);
    return v_res_2572_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(
    mut v_n_2573_: *mut leanh::LeanObject,
    mut v_f_2574_: *mut leanh::LeanObject,
    mut v_negPivot_2575_: *mut leanh::LeanObject,
    mut v_ratHint_2576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2583_: u8 = 0;
    let mut v_fst_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v___x_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negC_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2611_: u8 = 0;
    let mut v___x_2612_: u8 = 0;
    let mut v___x_2613_: u8 = 0;
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2623_: u8 = 0;
    let mut v_clauses_2624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v_assignments_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: u8 = 0;
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_isSharedCheck_2649_: u8 = 0;
    let mut v_f_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_reuseFailAlloc_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2657_: u8 = 0;
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_clauses_2577_ = leanh::lean_ctor_get(v_f_2574_, 0);
                v_rupUnits_2578_ = leanh::lean_ctor_get(v_f_2574_, 1);
                v_ratUnits_2579_ = leanh::lean_ctor_get(v_f_2574_, 2);
                v_assignments_2580_ = leanh::lean_ctor_get(v_f_2574_, 3);
                v_isSharedCheck_2658_ = (!leanh::lean_is_exclusive(v_f_2574_)) as u8;
                if v_isSharedCheck_2658_ == 0 {
                    v___x_2582_ = v_f_2574_;
                    v_isShared_2583_ = v_isSharedCheck_2658_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_2580_);
                    leanh::lean_inc(v_ratUnits_2579_);
                    leanh::lean_inc(v_rupUnits_2578_);
                    leanh::lean_inc(v_clauses_2577_);
                    leanh::lean_dec(v_f_2574_);
                    v___x_2582_ = leanh::lean_box(0);
                    v_isShared_2583_ = v_isSharedCheck_2658_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2584_ = leanh::lean_ctor_get(v_ratHint_2576_, 0);
                v_snd_2585_ = leanh::lean_ctor_get(v_ratHint_2576_, 1);
                v_isSharedCheck_2657_ = (!leanh::lean_is_exclusive(v_ratHint_2576_)) as u8;
                if v_isSharedCheck_2657_ == 0 {
                    v___x_2587_ = v_ratHint_2576_;
                    v_isShared_2588_ = v_isSharedCheck_2657_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2585_);
                    leanh::lean_inc(v_fst_2584_);
                    leanh::lean_dec(v_ratHint_2576_);
                    v___x_2587_ = leanh::lean_box(0);
                    v_isShared_2588_ = v_isSharedCheck_2657_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2589_ = leanh::lean_box(0);
                v___x_2590_ = lean_array_get_borrowed(v___x_2589_, v_clauses_2577_, v_fst_2584_);
                leanh::lean_dec(v_fst_2584_);
                if leanh::lean_obj_tag(v___x_2590_) == 0 {
                    leanh::lean_dec(v_snd_2585_);
                    if v_isShared_2583_ == 0 {
                        v___x_2592_ = v___x_2582_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2598_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_clauses_2577_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_rupUnits_2578_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 2, v_ratUnits_2579_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 3, v_assignments_2580_);
                        v___x_2592_ = v_reuseFailAlloc_2598_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2587_);
                    v_val_2599_ = leanh::lean_ctor_get(v___x_2590_, 0);
                    v___x_2600_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ofArray___closed__0;
                    leanh::lean_inc(v_val_2599_);
                    v___x_2601_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_val_2599_, v_negPivot_2575_, v_val_2599_, v___x_2600_);
                    v___x_2602_ = leanh::lean_box(0);
                    v_negC_2603_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupAdd_spec__0(v___x_2601_, v___x_2602_);
                    if v_isShared_2583_ == 0 {
                        v___x_2605_ = v___x_2582_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2656_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 0, v_clauses_2577_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 1, v_rupUnits_2578_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 2, v_ratUnits_2579_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2656_, 3, v_assignments_2580_);
                        v___x_2605_ = v_reuseFailAlloc_2656_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2593_ = 0;
                v___x_2594_ = leanh::lean_box((v___x_2593_) as usize);
                if v_isShared_2588_ == 0 {
                    leanh::lean_ctor_set(v___x_2587_, 1, v___x_2594_);
                    leanh::lean_ctor_set(v___x_2587_, 0, v___x_2592_);
                    v___x_2596_ = v___x_2587_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2597_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 0, v___x_2592_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2597_, 1, v___x_2594_);
                    v___x_2596_ = v_reuseFailAlloc_2597_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2596_;
            }
            5 => {
                v___x_2606_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRatUnits___redArg(
                        v___x_2605_,
                        v_negC_2603_,
                    );
                v_fst_2607_ = leanh::lean_ctor_get(v___x_2606_, 0);
                v_snd_2608_ = leanh::lean_ctor_get(v___x_2606_, 1);
                v_isSharedCheck_2655_ = (!leanh::lean_is_exclusive(v___x_2606_)) as u8;
                if v_isSharedCheck_2655_ == 0 {
                    v___x_2610_ = v___x_2606_;
                    v_isShared_2611_ = v_isSharedCheck_2655_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2608_);
                    leanh::lean_inc(v_fst_2607_);
                    leanh::lean_dec(v___x_2606_);
                    v___x_2610_ = leanh::lean_box(0);
                    v_isShared_2611_ = v_isSharedCheck_2655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2612_ = 1;
                v___x_2613_ = (leanh::lean_unbox(v_snd_2608_) as u8);
                if v___x_2613_ == 0 {
                    leanh::lean_del_object(v___x_2610_);
                    v___x_2614_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(
                            v_n_2573_,
                            v_fst_2607_,
                            v_snd_2585_,
                        );
                    leanh::lean_dec(v_snd_2585_);
                    v_snd_2615_ = leanh::lean_ctor_get(v___x_2614_, 1);
                    leanh::lean_inc(v_snd_2615_);
                    v_snd_2616_ = leanh::lean_ctor_get(v_snd_2615_, 1);
                    leanh::lean_inc(v_snd_2616_);
                    v_fst_2617_ = leanh::lean_ctor_get(v___x_2614_, 0);
                    leanh::lean_inc(v_fst_2617_);
                    leanh::lean_dec_ref(v___x_2614_);
                    v_fst_2618_ = leanh::lean_ctor_get(v_snd_2615_, 0);
                    leanh::lean_inc(v_fst_2618_);
                    leanh::lean_dec(v_snd_2615_);
                    v_fst_2619_ = leanh::lean_ctor_get(v_snd_2616_, 0);
                    v_snd_2620_ = leanh::lean_ctor_get(v_snd_2616_, 1);
                    v_isSharedCheck_2649_ = (!leanh::lean_is_exclusive(v_snd_2616_)) as u8;
                    if v_isSharedCheck_2649_ == 0 {
                        v___x_2622_ = v_snd_2616_;
                        v_isShared_2623_ = v_isSharedCheck_2649_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2620_);
                        leanh::lean_inc(v_fst_2619_);
                        leanh::lean_dec(v_snd_2616_);
                        v___x_2622_ = leanh::lean_box(0);
                        v_isShared_2623_ = v_isSharedCheck_2649_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_2608_);
                    leanh::lean_dec(v_snd_2585_);
                    v_f_2650_ =
                        l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(
                            v_fst_2607_,
                        );
                    v___x_2651_ = leanh::lean_box((v___x_2612_) as usize);
                    if v_isShared_2611_ == 0 {
                        leanh::lean_ctor_set(v___x_2610_, 1, v___x_2651_);
                        leanh::lean_ctor_set(v___x_2610_, 0, v_f_2650_);
                        v___x_2653_ = v___x_2610_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2654_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_f_2650_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2654_, 1, v___x_2651_);
                        v___x_2653_ = v_reuseFailAlloc_2654_;
                        state = 13;
                        continue;
                    }
                }
            }
            7 => {
                v_clauses_2624_ = leanh::lean_ctor_get(v_fst_2617_, 0);
                v_rupUnits_2625_ = leanh::lean_ctor_get(v_fst_2617_, 1);
                v_ratUnits_2626_ = leanh::lean_ctor_get(v_fst_2617_, 2);
                v_assignments_2627_ = leanh::lean_ctor_get(v_fst_2617_, 3);
                v_isSharedCheck_2648_ = (!leanh::lean_is_exclusive(v_fst_2617_)) as u8;
                if v_isSharedCheck_2648_ == 0 {
                    v___x_2629_ = v_fst_2617_;
                    v_isShared_2630_ = v_isSharedCheck_2648_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_2627_);
                    leanh::lean_inc(v_ratUnits_2626_);
                    leanh::lean_inc(v_rupUnits_2625_);
                    leanh::lean_inc(v_clauses_2624_);
                    leanh::lean_dec(v_fst_2617_);
                    v___x_2629_ = leanh::lean_box(0);
                    v_isShared_2630_ = v_isSharedCheck_2648_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v_assignments_2631_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_2627_, v_fst_2618_);
                leanh::lean_dec(v_fst_2618_);
                if v_isShared_2630_ == 0 {
                    leanh::lean_ctor_set(v___x_2629_, 3, v_assignments_2631_);
                    v___x_2633_ = v___x_2629_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2647_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_clauses_2624_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_rupUnits_2625_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 2, v_ratUnits_2626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2647_, 3, v_assignments_2631_);
                    v___x_2633_ = v_reuseFailAlloc_2647_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_f_2634_ =
                    l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRatUnits___redArg(
                        v___x_2633_,
                    );
                v___x_2635_ = (leanh::lean_unbox(v_snd_2620_) as u8);
                leanh::lean_dec(v_snd_2620_);
                if v___x_2635_ == 0 {
                    v___x_2636_ = (leanh::lean_unbox(v_fst_2619_) as u8);
                    leanh::lean_dec(v_fst_2619_);
                    if v___x_2636_ == 0 {
                        if v_isShared_2623_ == 0 {
                            leanh::lean_ctor_set(v___x_2622_, 1, v_snd_2608_);
                            leanh::lean_ctor_set(v___x_2622_, 0, v_f_2634_);
                            v___x_2638_ = v___x_2622_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2639_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 0, v_f_2634_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2639_, 1, v_snd_2608_);
                            v___x_2638_ = v_reuseFailAlloc_2639_;
                            state = 10;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_2608_);
                        v___x_2640_ = leanh::lean_box((v___x_2612_) as usize);
                        if v_isShared_2623_ == 0 {
                            leanh::lean_ctor_set(v___x_2622_, 1, v___x_2640_);
                            leanh::lean_ctor_set(v___x_2622_, 0, v_f_2634_);
                            v___x_2642_ = v___x_2622_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_2643_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_f_2634_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2643_, 1, v___x_2640_);
                            v___x_2642_ = v_reuseFailAlloc_2643_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_fst_2619_);
                    if v_isShared_2623_ == 0 {
                        leanh::lean_ctor_set(v___x_2622_, 1, v_snd_2608_);
                        leanh::lean_ctor_set(v___x_2622_, 0, v_f_2634_);
                        v___x_2645_ = v___x_2622_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_2646_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v_f_2634_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 1, v_snd_2608_);
                        v___x_2645_ = v_reuseFailAlloc_2646_;
                        state = 12;
                        continue;
                    }
                }
            }
            10 => {
                return v___x_2638_;
            }
            11 => {
                return v___x_2642_;
            }
            12 => {
                return v___x_2645_;
            }
            13 => {
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck___boxed(
    mut v_n_2659_: *mut leanh::LeanObject,
    mut v_f_2660_: *mut leanh::LeanObject,
    mut v_negPivot_2661_: *mut leanh::LeanObject,
    mut v_ratHint_2662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2663_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(
        v_n_2659_,
        v_f_2660_,
        v_negPivot_2661_,
        v_ratHint_2662_,
    );
    leanh::lean_dec_ref(v_negPivot_2661_);
    leanh::lean_dec(v_n_2659_);
    return v_res_2663_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(
    mut v_n_2664_: *mut leanh::LeanObject,
    mut v_l_2665_: *mut leanh::LeanObject,
    mut v_a_2666_: *mut leanh::LeanObject,
    mut v_a_2667_: *mut leanh::LeanObject,
    mut v_a_2668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2669_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___redArg(v_l_2665_, v_a_2666_, v_a_2667_, v_a_2668_);
    return v___x_2669_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0___boxed(
    mut v_n_2670_: *mut leanh::LeanObject,
    mut v_l_2671_: *mut leanh::LeanObject,
    mut v_a_2672_: *mut leanh::LeanObject,
    mut v_a_2673_: *mut leanh::LeanObject,
    mut v_a_2674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2675_ = l___private_Init_Data_List_Impl_0__List_eraseTR_go___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck_spec__0(v_n_2670_, v_l_2671_, v_a_2672_, v_a_2673_, v_a_2674_);
    leanh::lean_dec_ref(v_a_2672_);
    leanh::lean_dec(v_l_2671_);
    leanh::lean_dec(v_n_2670_);
    return v_res_2675_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(
    mut v_pivot_2676_: *mut leanh::LeanObject,
    mut v_n_2677_: *mut leanh::LeanObject,
    mut v_fst_2678_: u8,
    mut v_as_2679_: *mut leanh::LeanObject,
    mut v_i_2680_: usize,
    mut v_stop_2681_: usize,
    mut v_b_2682_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2685_: usize = 0;
    let mut v___x_2686_: usize = 0;
    let mut v___x_2688_: u8 = 0;
    let mut v_snd_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: u8 = 0;
    let mut v_fst_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v_fst_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v_unused_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2688_ = lean_usize_dec_eq(v_i_2680_, v_stop_2681_);
                if v___x_2688_ == 0 {
                    v_snd_2689_ = leanh::lean_ctor_get(v_b_2682_, 1);
                    v___x_2690_ = (leanh::lean_unbox(v_snd_2689_) as u8);
                    if v___x_2690_ == 0 {
                        v___y_2684_ = v_b_2682_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2689_);
                        v_fst_2691_ = leanh::lean_ctor_get(v_b_2682_, 0);
                        v_isSharedCheck_2708_ = (!leanh::lean_is_exclusive(v_b_2682_)) as u8;
                        if v_isSharedCheck_2708_ == 0 {
                            v_unused_2709_ = leanh::lean_ctor_get(v_b_2682_, 1);
                            leanh::lean_dec(v_unused_2709_);
                            v___x_2693_ = v_b_2682_;
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_2691_);
                            leanh::lean_dec(v_b_2682_);
                            v___x_2693_ = leanh::lean_box(0);
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    return v_b_2682_;
                }
            }
            1 => {
                v___x_2685_ = 1usize;
                v___x_2686_ = lean_usize_add(v_i_2680_, v___x_2685_);
                v_i_2680_ = v___x_2686_;
                v_b_2682_ = v___y_2684_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_2695_ = leanh::lean_ctor_get(v_pivot_2676_, 0);
                v_snd_2696_ = leanh::lean_ctor_get(v_pivot_2676_, 1);
                v___x_2697_ = lean_array_uget_borrowed(v_as_2679_, v_i_2680_);
                v___x_2698_ = (leanh::lean_unbox(v_snd_2696_) as u8);
                if v___x_2698_ == 0 {
                    leanh::lean_inc(v_fst_2695_);
                    if v_isShared_2694_ == 0 {
                        leanh::lean_ctor_set(v___x_2693_, 0, v_fst_2695_);
                        v___x_2700_ = v___x_2693_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2702_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2702_, 0, v_fst_2695_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2702_, 1, v_snd_2689_);
                        v___x_2700_ = v_reuseFailAlloc_2702_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_snd_2689_);
                    v___x_2703_ = leanh::lean_box((v_fst_2678_) as usize);
                    leanh::lean_inc(v_fst_2695_);
                    if v_isShared_2694_ == 0 {
                        leanh::lean_ctor_set(v___x_2693_, 1, v___x_2703_);
                        leanh::lean_ctor_set(v___x_2693_, 0, v_fst_2695_);
                        v___x_2705_ = v___x_2693_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v_fst_2695_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 1, v___x_2703_);
                        v___x_2705_ = v_reuseFailAlloc_2707_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                leanh::lean_inc(v___x_2697_);
                v___x_2701_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(
                    v_n_2677_,
                    v_fst_2691_,
                    v___x_2700_,
                    v___x_2697_,
                );
                leanh::lean_dec_ref(v___x_2700_);
                v___y_2684_ = v___x_2701_;
                state = 1;
                continue;
            }
            4 => {
                leanh::lean_inc(v___x_2697_);
                v___x_2706_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatCheck(
                    v_n_2677_,
                    v_fst_2691_,
                    v___x_2705_,
                    v___x_2697_,
                );
                leanh::lean_dec_ref(v___x_2705_);
                v___y_2684_ = v___x_2706_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1___boxed(
    mut v_pivot_2710_: *mut leanh::LeanObject,
    mut v_n_2711_: *mut leanh::LeanObject,
    mut v_fst_2712_: *mut leanh::LeanObject,
    mut v_as_2713_: *mut leanh::LeanObject,
    mut v_i_2714_: *mut leanh::LeanObject,
    mut v_stop_2715_: *mut leanh::LeanObject,
    mut v_b_2716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1446__boxed_2717_: u8 = 0;
    let mut v_i_boxed_2718_: usize = 0;
    let mut v_stop_boxed_2719_: usize = 0;
    let mut v_res_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_1446__boxed_2717_ = (leanh::lean_unbox(v_fst_2712_) as u8);
    v_i_boxed_2718_ = leanh::lean_unbox_usize(v_i_2714_);
    leanh::lean_dec(v_i_2714_);
    v_stop_boxed_2719_ = leanh::lean_unbox_usize(v_stop_2715_);
    leanh::lean_dec(v_stop_2715_);
    v_res_2720_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_2710_, v_n_2711_, v_fst_1446__boxed_2717_, v_as_2713_, v_i_boxed_2718_, v_stop_boxed_2719_, v_b_2716_);
    leanh::lean_dec_ref(v_as_2713_);
    leanh::lean_dec(v_n_2711_);
    leanh::lean_dec_ref(v_pivot_2710_);
    return v_res_2720_;
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(
    mut v___x_2721_: u8,
    mut v_a_2722_: *mut leanh::LeanObject,
    mut v_a_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2729_: u8 = 0;
    let mut v___y_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: u8 = 0;
    let mut v_fst_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2741_: u8 = 0;
    let mut v___x_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2746_: u8 = 0;
    let mut v_unused_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2751_: u8 = 0;
    let mut v___x_2752_: u8 = 0;
    let mut v___x_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2757_: u8 = 0;
    let mut v_unused_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_2722_) == 0 {
                    v___x_2724_ = l_List_reverse___redArg(v_a_2723_);
                    return v___x_2724_;
                } else {
                    v_head_2725_ = leanh::lean_ctor_get(v_a_2722_, 0);
                    v_tail_2726_ = leanh::lean_ctor_get(v_a_2722_, 1);
                    v_isSharedCheck_2759_ = (!leanh::lean_is_exclusive(v_a_2722_)) as u8;
                    if v_isSharedCheck_2759_ == 0 {
                        v___x_2728_ = v_a_2722_;
                        v_isShared_2729_ = v_isSharedCheck_2759_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_2726_);
                        leanh::lean_inc(v_head_2725_);
                        leanh::lean_dec(v_a_2722_);
                        v___x_2728_ = leanh::lean_box(0);
                        v_isShared_2729_ = v_isSharedCheck_2759_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_2736_ = leanh::lean_ctor_get(v_head_2725_, 1);
                v___x_2737_ = (leanh::lean_unbox(v_snd_2736_) as u8);
                if v___x_2737_ == 0 {
                    v_fst_2738_ = leanh::lean_ctor_get(v_head_2725_, 0);
                    v_isSharedCheck_2746_ = (!leanh::lean_is_exclusive(v_head_2725_)) as u8;
                    if v_isSharedCheck_2746_ == 0 {
                        v_unused_2747_ = leanh::lean_ctor_get(v_head_2725_, 1);
                        leanh::lean_dec(v_unused_2747_);
                        v___x_2740_ = v_head_2725_;
                        v_isShared_2741_ = v_isSharedCheck_2746_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2738_);
                        leanh::lean_dec(v_head_2725_);
                        v___x_2740_ = leanh::lean_box(0);
                        v_isShared_2741_ = v_isSharedCheck_2746_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_fst_2748_ = leanh::lean_ctor_get(v_head_2725_, 0);
                    v_isSharedCheck_2757_ = (!leanh::lean_is_exclusive(v_head_2725_)) as u8;
                    if v_isSharedCheck_2757_ == 0 {
                        v_unused_2758_ = leanh::lean_ctor_get(v_head_2725_, 1);
                        leanh::lean_dec(v_unused_2758_);
                        v___x_2750_ = v_head_2725_;
                        v_isShared_2751_ = v_isSharedCheck_2757_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_2748_);
                        leanh::lean_dec(v_head_2725_);
                        v___x_2750_ = leanh::lean_box(0);
                        v_isShared_2751_ = v_isSharedCheck_2757_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2729_ == 0 {
                    leanh::lean_ctor_set(v___x_2728_, 1, v_a_2723_);
                    leanh::lean_ctor_set(v___x_2728_, 0, v___y_2731_);
                    v___x_2733_ = v___x_2728_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2735_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 0, v___y_2731_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2735_, 1, v_a_2723_);
                    v___x_2733_ = v_reuseFailAlloc_2735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_a_2722_ = v_tail_2726_;
                v_a_2723_ = v___x_2733_;
                state = 0;
                continue;
            }
            4 => {
                v___x_2742_ = leanh::lean_box((v___x_2721_) as usize);
                if v_isShared_2741_ == 0 {
                    leanh::lean_ctor_set(v___x_2740_, 1, v___x_2742_);
                    v___x_2744_ = v___x_2740_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2745_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 0, v_fst_2738_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2745_, 1, v___x_2742_);
                    v___x_2744_ = v_reuseFailAlloc_2745_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_2731_ = v___x_2744_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2752_ = 0;
                v___x_2753_ = leanh::lean_box((v___x_2752_) as usize);
                if v_isShared_2751_ == 0 {
                    leanh::lean_ctor_set(v___x_2750_, 1, v___x_2753_);
                    v___x_2755_ = v___x_2750_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2756_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 0, v_fst_2748_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2756_, 1, v___x_2753_);
                    v___x_2755_ = v_reuseFailAlloc_2756_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2731_ = v___x_2755_;
                state = 2;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0___boxed(
    mut v___x_2760_: *mut leanh::LeanObject,
    mut v_a_2761_: *mut leanh::LeanObject,
    mut v_a_2762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1499__boxed_2763_: u8 = 0;
    let mut v_res_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1499__boxed_2763_ = (leanh::lean_unbox(v___x_2760_) as u8);
    v_res_2764_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v___x_1499__boxed_2763_, v_a_2761_, v_a_2762_);
    return v_res_2764_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(
    mut v_n_2765_: *mut leanh::LeanObject,
    mut v_f_2766_: *mut leanh::LeanObject,
    mut v_c_2767_: *mut leanh::LeanObject,
    mut v_pivot_2768_: *mut leanh::LeanObject,
    mut v_rupHints_2769_: *mut leanh::LeanObject,
    mut v_ratHints_2770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2771_: u8 = 0;
    let mut v___x_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_negC_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut v_fst_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2785_: u8 = 0;
    let mut v_fst_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2790_: u8 = 0;
    let mut v___y_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_clauses_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rupUnits_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ratUnits_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignments_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v_assignments_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_f_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut v_fst_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2815_: u8 = 0;
    let mut v_fst_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2818_: u8 = 0;
    let mut v___x_2820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: u8 = 0;
    let mut v___x_2827_: u8 = 0;
    let mut v___x_2828_: u8 = 0;
    let mut v___x_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2831_: u8 = 0;
    let mut v___x_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: u8 = 0;
    let mut v___x_2836_: usize = 0;
    let mut v___x_2837_: usize = 0;
    let mut v___x_2838_: u8 = 0;
    let mut v___x_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: usize = 0;
    let mut v___x_2841_: usize = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2851_: u8 = 0;
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut v_isSharedCheck_2853_: u8 = 0;
    let mut v_fst_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2857_: u8 = 0;
    let mut v___x_2858_: u8 = 0;
    let mut v___x_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2863_: u8 = 0;
    let mut v_unused_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_ratHints_2770_);
                leanh::lean_inc_ref(v_pivot_2768_);
                v___x_2771_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_ratHintsExhaustive(
                    v_n_2765_,
                    v_f_2766_,
                    v_pivot_2768_,
                    v_ratHints_2770_,
                );
                if v___x_2771_ == 0 {
                    leanh::lean_dec_ref(v_ratHints_2770_);
                    leanh::lean_dec_ref(v_pivot_2768_);
                    leanh::lean_dec(v_c_2767_);
                    v___x_2772_ = leanh::lean_box((v___x_2771_) as usize);
                    v___x_2773_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2773_, 0, v_f_2766_);
                    leanh::lean_ctor_set(v___x_2773_, 1, v___x_2772_);
                    return v___x_2773_;
                } else {
                    v___x_2774_ = leanh::lean_box(0);
                    leanh::lean_inc(v_c_2767_);
                    v_negC_2775_ = l_List_mapTR_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__0(v___x_2771_, v_c_2767_, v___x_2774_);
                    v___x_2776_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insertRupUnits(
                        v_n_2765_,
                        v_f_2766_,
                        v_negC_2775_,
                    );
                    v_snd_2777_ = leanh::lean_ctor_get(v___x_2776_, 1);
                    leanh::lean_inc(v_snd_2777_);
                    v___x_2778_ = (leanh::lean_unbox(v_snd_2777_) as u8);
                    if v___x_2778_ == 0 {
                        v_fst_2779_ = leanh::lean_ctor_get(v___x_2776_, 0);
                        leanh::lean_inc(v_fst_2779_);
                        leanh::lean_dec_ref(v___x_2776_);
                        v___x_2780_ =
                            l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRupCheck(
                                v_n_2765_,
                                v_fst_2779_,
                                v_rupHints_2769_,
                            );
                        v_snd_2781_ = leanh::lean_ctor_get(v___x_2780_, 1);
                        v_fst_2782_ = leanh::lean_ctor_get(v___x_2780_, 0);
                        v_isSharedCheck_2853_ =
                            (!leanh::lean_is_exclusive(v___x_2780_)) as u8;
                        if v_isSharedCheck_2853_ == 0 {
                            v___x_2784_ = v___x_2780_;
                            v_isShared_2785_ = v_isSharedCheck_2853_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_2781_);
                            leanh::lean_inc(v_fst_2782_);
                            leanh::lean_dec(v___x_2780_);
                            v___x_2784_ = leanh::lean_box(0);
                            v_isShared_2785_ = v_isSharedCheck_2853_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_snd_2777_);
                        leanh::lean_dec_ref(v_ratHints_2770_);
                        leanh::lean_dec_ref(v_pivot_2768_);
                        leanh::lean_dec(v_c_2767_);
                        v_fst_2854_ = leanh::lean_ctor_get(v___x_2776_, 0);
                        v_isSharedCheck_2863_ =
                            (!leanh::lean_is_exclusive(v___x_2776_)) as u8;
                        if v_isSharedCheck_2863_ == 0 {
                            v_unused_2864_ = leanh::lean_ctor_get(v___x_2776_, 1);
                            leanh::lean_dec(v_unused_2864_);
                            v___x_2856_ = v___x_2776_;
                            v_isShared_2857_ = v_isSharedCheck_2863_;
                            state = 14;
                            continue;
                        } else {
                            leanh::lean_inc(v_fst_2854_);
                            leanh::lean_dec(v___x_2776_);
                            v___x_2856_ = leanh::lean_box(0);
                            v_isShared_2857_ = v_isSharedCheck_2863_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2786_ = leanh::lean_ctor_get(v_snd_2781_, 0);
                v_snd_2787_ = leanh::lean_ctor_get(v_snd_2781_, 1);
                v_isSharedCheck_2852_ = (!leanh::lean_is_exclusive(v_snd_2781_)) as u8;
                if v_isSharedCheck_2852_ == 0 {
                    v___x_2789_ = v_snd_2781_;
                    v_isShared_2790_ = v_isSharedCheck_2852_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2787_);
                    leanh::lean_inc(v_fst_2786_);
                    leanh::lean_dec(v_snd_2781_);
                    v___x_2789_ = leanh::lean_box(0);
                    v_isShared_2790_ = v_isSharedCheck_2852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_2811_ = leanh::lean_ctor_get(v_snd_2787_, 0);
                v_snd_2812_ = leanh::lean_ctor_get(v_snd_2787_, 1);
                v_isSharedCheck_2851_ = (!leanh::lean_is_exclusive(v_snd_2787_)) as u8;
                if v_isSharedCheck_2851_ == 0 {
                    v___x_2814_ = v_snd_2787_;
                    v_isShared_2815_ = v_isSharedCheck_2851_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2812_);
                    leanh::lean_inc(v_fst_2811_);
                    leanh::lean_dec(v_snd_2787_);
                    v___x_2814_ = leanh::lean_box(0);
                    v_isShared_2815_ = v_isSharedCheck_2851_;
                    state = 7;
                    continue;
                }
            }
            3 => {
                v_clauses_2793_ = leanh::lean_ctor_get(v___y_2792_, 0);
                v_rupUnits_2794_ = leanh::lean_ctor_get(v___y_2792_, 1);
                v_ratUnits_2795_ = leanh::lean_ctor_get(v___y_2792_, 2);
                v_assignments_2796_ = leanh::lean_ctor_get(v___y_2792_, 3);
                v_isSharedCheck_2810_ = (!leanh::lean_is_exclusive(v___y_2792_)) as u8;
                if v_isSharedCheck_2810_ == 0 {
                    v___x_2798_ = v___y_2792_;
                    v_isShared_2799_ = v_isSharedCheck_2810_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_assignments_2796_);
                    leanh::lean_inc(v_ratUnits_2795_);
                    leanh::lean_inc(v_rupUnits_2794_);
                    leanh::lean_inc(v_clauses_2793_);
                    leanh::lean_dec(v___y_2792_);
                    v___x_2798_ = leanh::lean_box(0);
                    v_isShared_2799_ = v_isSharedCheck_2810_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_assignments_2800_ = l_List_foldl___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_restoreAssignments_spec__0___redArg(v_assignments_2796_, v_fst_2786_);
                leanh::lean_dec(v_fst_2786_);
                if v_isShared_2799_ == 0 {
                    leanh::lean_ctor_set(v___x_2798_, 3, v_assignments_2800_);
                    v___x_2802_ = v___x_2798_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2809_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 0, v_clauses_2793_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 1, v_rupUnits_2794_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 2, v_ratUnits_2795_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2809_, 3, v_assignments_2800_);
                    v___x_2802_ = v_reuseFailAlloc_2809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_f_2803_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_clearRupUnits(
                    v_n_2765_,
                    v___x_2802_,
                );
                v___x_2804_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_insert___redArg(
                    v_f_2803_, v_c_2767_,
                );
                v___x_2805_ = leanh::lean_box((v___x_2771_) as usize);
                if v_isShared_2790_ == 0 {
                    leanh::lean_ctor_set(v___x_2789_, 1, v___x_2805_);
                    leanh::lean_ctor_set(v___x_2789_, 0, v___x_2804_);
                    v___x_2807_ = v___x_2789_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2804_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 1, v___x_2805_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2807_;
            }
            7 => {
                v___x_2827_ = (leanh::lean_unbox(v_snd_2812_) as u8);
                if v___x_2827_ == 0 {
                    leanh::lean_dec(v_snd_2777_);
                    v___x_2828_ = (leanh::lean_unbox(v_fst_2811_) as u8);
                    if v___x_2828_ == 0 {
                        leanh::lean_dec(v_snd_2812_);
                        v___x_2829_ = leanh::lean_unsigned_to_nat(0);
                        v___x_2830_ = lean_array_get_size(v_ratHints_2770_);
                        v___x_2831_ = lean_nat_dec_lt(v___x_2829_, v___x_2830_);
                        if v___x_2831_ == 0 {
                            leanh::lean_del_object(v___x_2784_);
                            leanh::lean_dec_ref(v_ratHints_2770_);
                            leanh::lean_dec_ref(v_pivot_2768_);
                            v_fst_2817_ = v_fst_2782_;
                            v_snd_2818_ = v___x_2771_;
                            state = 8;
                            continue;
                        } else {
                            v___x_2832_ = leanh::lean_box((v___x_2771_) as usize);
                            leanh::lean_inc(v_fst_2782_);
                            if v_isShared_2785_ == 0 {
                                leanh::lean_ctor_set(v___x_2784_, 1, v___x_2832_);
                                v___x_2834_ = v___x_2784_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2844_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2844_, 0, v_fst_2782_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_2844_, 1, v___x_2832_);
                                v___x_2834_ = v_reuseFailAlloc_2844_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_2814_);
                        leanh::lean_dec(v_fst_2811_);
                        leanh::lean_del_object(v___x_2789_);
                        leanh::lean_dec(v_fst_2786_);
                        leanh::lean_dec_ref(v_ratHints_2770_);
                        leanh::lean_dec_ref(v_pivot_2768_);
                        leanh::lean_dec(v_c_2767_);
                        if v_isShared_2785_ == 0 {
                            leanh::lean_ctor_set(v___x_2784_, 1, v_snd_2812_);
                            v___x_2846_ = v___x_2784_;
                            state = 12;
                            continue;
                        } else {
                            v_reuseFailAlloc_2847_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v_fst_2782_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_snd_2812_);
                            v___x_2846_ = v_reuseFailAlloc_2847_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2814_);
                    leanh::lean_dec(v_snd_2812_);
                    leanh::lean_dec(v_fst_2811_);
                    leanh::lean_del_object(v___x_2789_);
                    leanh::lean_dec(v_fst_2786_);
                    leanh::lean_dec_ref(v_ratHints_2770_);
                    leanh::lean_dec_ref(v_pivot_2768_);
                    leanh::lean_dec(v_c_2767_);
                    if v_isShared_2785_ == 0 {
                        leanh::lean_ctor_set(v___x_2784_, 1, v_snd_2777_);
                        v___x_2849_ = v___x_2784_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_2850_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_fst_2782_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2850_, 1, v_snd_2777_);
                        v___x_2849_ = v_reuseFailAlloc_2850_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                if v_snd_2818_ == 0 {
                    if v___x_2771_ == 0 {
                        leanh::lean_del_object(v___x_2814_);
                        leanh::lean_dec(v_fst_2811_);
                        v___y_2792_ = v_fst_2817_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_del_object(v___x_2789_);
                        leanh::lean_dec(v_fst_2786_);
                        leanh::lean_dec(v_c_2767_);
                        if v_isShared_2815_ == 0 {
                            leanh::lean_ctor_set(v___x_2814_, 1, v_fst_2811_);
                            leanh::lean_ctor_set(v___x_2814_, 0, v_fst_2817_);
                            v___x_2820_ = v___x_2814_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2821_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 0, v_fst_2817_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_2821_, 1, v_fst_2811_);
                            v___x_2820_ = v_reuseFailAlloc_2821_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_2814_);
                    leanh::lean_dec(v_fst_2811_);
                    v___y_2792_ = v_fst_2817_;
                    state = 3;
                    continue;
                }
            }
            9 => {
                return v___x_2820_;
            }
            10 => {
                v_fst_2824_ = leanh::lean_ctor_get(v___y_2823_, 0);
                leanh::lean_inc(v_fst_2824_);
                v_snd_2825_ = leanh::lean_ctor_get(v___y_2823_, 1);
                leanh::lean_inc(v_snd_2825_);
                leanh::lean_dec_ref(v___y_2823_);
                v___x_2826_ = (leanh::lean_unbox(v_snd_2825_) as u8);
                leanh::lean_dec(v_snd_2825_);
                v_fst_2817_ = v_fst_2824_;
                v_snd_2818_ = v___x_2826_;
                state = 8;
                continue;
            }
            11 => {
                v___x_2835_ = lean_nat_dec_le(v___x_2830_, v___x_2830_);
                if v___x_2835_ == 0 {
                    if v___x_2831_ == 0 {
                        leanh::lean_dec_ref(v___x_2834_);
                        leanh::lean_dec_ref(v_ratHints_2770_);
                        leanh::lean_dec_ref(v_pivot_2768_);
                        v_fst_2817_ = v_fst_2782_;
                        v_snd_2818_ = v___x_2771_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_2782_);
                        v___x_2836_ = 0usize;
                        v___x_2837_ = lean_usize_of_nat(v___x_2830_);
                        v___x_2838_ = (leanh::lean_unbox(v_fst_2811_) as u8);
                        v___x_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_2768_, v_n_2765_, v___x_2838_, v_ratHints_2770_, v___x_2836_, v___x_2837_, v___x_2834_);
                        leanh::lean_dec_ref(v_ratHints_2770_);
                        leanh::lean_dec_ref(v_pivot_2768_);
                        v___y_2823_ = v___x_2839_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_fst_2782_);
                    v___x_2840_ = 0usize;
                    v___x_2841_ = lean_usize_of_nat(v___x_2830_);
                    v___x_2842_ = (leanh::lean_unbox(v_fst_2811_) as u8);
                    v___x_2843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd_spec__1(v_pivot_2768_, v_n_2765_, v___x_2842_, v_ratHints_2770_, v___x_2840_, v___x_2841_, v___x_2834_);
                    leanh::lean_dec_ref(v_ratHints_2770_);
                    leanh::lean_dec_ref(v_pivot_2768_);
                    v___y_2823_ = v___x_2843_;
                    state = 10;
                    continue;
                }
            }
            12 => {
                return v___x_2846_;
            }
            13 => {
                return v___x_2849_;
            }
            14 => {
                v___x_2858_ = 0;
                v___x_2859_ = leanh::lean_box((v___x_2858_) as usize);
                if v_isShared_2857_ == 0 {
                    leanh::lean_ctor_set(v___x_2856_, 1, v___x_2859_);
                    v___x_2861_ = v___x_2856_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 0, v_fst_2854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2862_, 1, v___x_2859_);
                    v___x_2861_ = v_reuseFailAlloc_2862_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd___boxed(
    mut v_n_2865_: *mut leanh::LeanObject,
    mut v_f_2866_: *mut leanh::LeanObject,
    mut v_c_2867_: *mut leanh::LeanObject,
    mut v_pivot_2868_: *mut leanh::LeanObject,
    mut v_rupHints_2869_: *mut leanh::LeanObject,
    mut v_ratHints_2870_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2871_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_performRatAdd(
        v_n_2865_,
        v_f_2866_,
        v_c_2867_,
        v_pivot_2868_,
        v_rupHints_2869_,
        v_ratHints_2870_,
    );
    leanh::lean_dec_ref(v_rupHints_2869_);
    leanh::lean_dec(v_n_2865_);
    return v_res_2871_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(
    mut v_x_2872_: *mut leanh::LeanObject,
    mut v_x_2873_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_2872_) == 0 {
        if leanh::lean_obj_tag(v_x_2873_) == 0 {
            let mut v___x_2874_: u8 = 0;
            v___x_2874_ = 1;
            return v___x_2874_;
        } else {
            let mut v___x_2875_: u8 = 0;
            v___x_2875_ = 0;
            return v___x_2875_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_2873_) == 0 {
            let mut v___x_2876_: u8 = 0;
            v___x_2876_ = 0;
            return v___x_2876_;
        } else {
            let mut v_val_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2879_: u8 = 0;
            v_val_2877_ = leanh::lean_ctor_get(v_x_2872_, 0);
            v_val_2878_ = leanh::lean_ctor_get(v_x_2873_, 0);
            v___x_2879_ = l_List_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_instBEqDefaultClause_beq_spec__0___redArg(v_val_2877_, v_val_2878_);
            return v___x_2879_;
        }
    }
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg___boxed(
    mut v_x_2880_: *mut leanh::LeanObject,
    mut v_x_2881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2882_: u8 = 0;
    let mut v_r_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2882_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_2880_, v_x_2881_);
    leanh::lean_dec(v_x_2881_);
    leanh::lean_dec(v_x_2880_);
    v_r_2883_ = leanh::lean_box((v_res_2882_) as usize);
    return v_r_2883_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(
    mut v_n_2884_: *mut leanh::LeanObject,
    mut v_x_2885_: *mut leanh::LeanObject,
    mut v_x_2886_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_2887_: u8 = 0;
    v___x_2887_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_x_2885_, v_x_2886_);
    return v___x_2887_;
}
pub unsafe fn l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___boxed(
    mut v_n_2888_: *mut leanh::LeanObject,
    mut v_x_2889_: *mut leanh::LeanObject,
    mut v_x_2890_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2891_: u8 = 0;
    let mut v_r_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2891_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0(v_n_2888_, v_x_2889_, v_x_2890_);
    leanh::lean_dec(v_x_2890_);
    leanh::lean_dec(v_x_2889_);
    leanh::lean_dec(v_n_2888_);
    v_r_2892_ = leanh::lean_box((v_res_2891_) as usize);
    return v_r_2892_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(
    mut v_n_2893_: *mut leanh::LeanObject,
    mut v_as_2894_: *mut leanh::LeanObject,
    mut v_sz_2895_: usize,
    mut v_i_2896_: usize,
    mut v_b_2897_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2900_: usize = 0;
    let mut v___x_2901_: usize = 0;
    let mut v___x_2903_: u8 = 0;
    let mut v_a_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2903_ = lean_usize_dec_lt(v_i_2896_, v_sz_2895_);
                if v___x_2903_ == 0 {
                    return v_b_2897_;
                } else {
                    v_a_2904_ = lean_array_uget_borrowed(v_as_2894_, v_i_2896_);
                    v___x_2905_ = leanh::lean_box(0);
                    v___x_2906_ = l_Option_instBEq_beq___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__0___redArg(v_a_2904_, v___x_2905_);
                    if v___x_2906_ == 0 {
                        v___x_2907_ = leanh::lean_unsigned_to_nat(1);
                        v___x_2908_ = lean_nat_add(v_b_2897_, v___x_2907_);
                        leanh::lean_dec(v_b_2897_);
                        v_a_2899_ = v___x_2908_;
                        state = 1;
                        continue;
                    } else {
                        v_a_2899_ = v_b_2897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2900_ = 1usize;
                v___x_2901_ = lean_usize_add(v_i_2896_, v___x_2900_);
                v_i_2896_ = v___x_2901_;
                v_b_2897_ = v_a_2899_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1___boxed(
    mut v_n_2909_: *mut leanh::LeanObject,
    mut v_as_2910_: *mut leanh::LeanObject,
    mut v_sz_2911_: *mut leanh::LeanObject,
    mut v_i_2912_: *mut leanh::LeanObject,
    mut v_b_2913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2914_: usize = 0;
    let mut v_i_boxed_2915_: usize = 0;
    let mut v_res_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2914_ = leanh::lean_unbox_usize(v_sz_2911_);
    leanh::lean_dec(v_sz_2911_);
    v_i_boxed_2915_ = leanh::lean_unbox_usize(v_i_2912_);
    leanh::lean_dec(v_i_2912_);
    v_res_2916_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_2909_, v_as_2910_, v_sz_boxed_2914_, v_i_boxed_2915_, v_b_2913_);
    leanh::lean_dec_ref(v_as_2910_);
    leanh::lean_dec(v_n_2909_);
    return v_res_2916_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(
    mut v_n_2917_: *mut leanh::LeanObject,
    mut v_f_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_clauses_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numClauses_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2921_: usize = 0;
    let mut v___x_2922_: usize = 0;
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_clauses_2919_ = leanh::lean_ctor_get(v_f_2918_, 0);
    v_numClauses_2920_ = leanh::lean_unsigned_to_nat(0);
    v_sz_2921_ = lean_array_size(v_clauses_2919_);
    v___x_2922_ = 0usize;
    v___x_2923_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula_spec__1(v_n_2917_, v_clauses_2919_, v_sz_2921_, v___x_2922_, v_numClauses_2920_);
    return v___x_2923_;
}
pub unsafe fn l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula___boxed(
    mut v_n_2924_: *mut leanh::LeanObject,
    mut v_f_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2926_ = l_Std_Tactic_BVDecide_LRAT_Internal_DefaultFormula_numClausesInFormula(
        v_n_2924_, v_f_2925_,
    );
    leanh::lean_dec_ref(v_f_2925_);
    leanh::lean_dec(v_n_2924_);
    return v_res_2926_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Class(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Tactic_BVDecide_LRAT_Internal_Formula_Implementation(builtin);
}
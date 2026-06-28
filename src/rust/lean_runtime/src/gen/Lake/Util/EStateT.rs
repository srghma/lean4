// Lean compiler output
// Module: Lake.Util.EStateT
// Imports: Init.Control.State
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_4, lean_apply_5, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lake_EResult_instFunctor___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_instFunctor___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_EResult_instFunctor___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value) as *mut LeanObject;
pub static l_Lake_EResult_instFunctor___closed__1_value: LeanClosureObject<1> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_instFunctor___lam__1 as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 1,
    m_objs: [core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value) as *mut LeanObject],
};
static mut l_Lake_EResult_instFunctor___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value) as *mut LeanObject;
pub static l_Lake_EResult_instFunctor___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_EResult_instFunctor___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__2_value) as *mut LeanObject;
pub static l_Lake_EStateT_run_x27___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toExcept___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_EStateT_run_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_EStateT_toStateT___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_EStateT_toStateT___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd_x3f as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_EStateT_toStateT_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value: LeanClosureObject<3> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 3) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_result_x3f___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lake_EStateT_run_x3f_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lake_EResult_ctorIdx___redArg(mut v_x_1469_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1469_) == 0 {
        let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
        v___x_1470_ = lean_unsigned_to_nat(0);
        return v___x_1470_;
    } else {
        let mut v___x_1471_: *mut LeanObject = core::ptr::null_mut();
        v___x_1471_ = lean_unsigned_to_nat(1);
        return v___x_1471_;
    }
}
pub unsafe fn l_Lake_EResult_ctorIdx___redArg___boxed(
    mut v_x_1472_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1473_: *mut LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lake_EResult_ctorIdx___redArg(v_x_1472_);
    lean_dec_ref(v_x_1472_);
    return v_res_1473_;
}
pub unsafe fn l_Lake_EResult_ctorIdx(
    mut v_00_u03b5_1474_: *mut LeanObject,
    mut v_00_u03c3_1475_: *mut LeanObject,
    mut v_00_u03b1_1476_: *mut LeanObject,
    mut v_x_1477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Lake_EResult_ctorIdx___redArg(v_x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lake_EResult_ctorIdx___boxed(
    mut v_00_u03b5_1479_: *mut LeanObject,
    mut v_00_u03c3_1480_: *mut LeanObject,
    mut v_00_u03b1_1481_: *mut LeanObject,
    mut v_x_1482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1483_: *mut LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_Lake_EResult_ctorIdx(
        v_00_u03b5_1479_,
        v_00_u03c3_1480_,
        v_00_u03b1_1481_,
        v_x_1482_,
    );
    lean_dec_ref(v_x_1482_);
    return v_res_1483_;
}
pub unsafe fn l_Lake_EResult_ctorElim___redArg(
    mut v_t_1484_: *mut LeanObject,
    mut v_k_1485_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
    v_a_1486_ = lean_ctor_get(v_t_1484_, 0);
    lean_inc(v_a_1486_);
    v_a_1487_ = lean_ctor_get(v_t_1484_, 1);
    lean_inc(v_a_1487_);
    lean_dec_ref(v_t_1484_);
    v___x_1488_ = lean_apply_2(v_k_1485_, v_a_1486_, v_a_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lake_EResult_ctorElim(
    mut v_00_u03b5_1489_: *mut LeanObject,
    mut v_00_u03c3_1490_: *mut LeanObject,
    mut v_00_u03b1_1491_: *mut LeanObject,
    mut v_motive_1492_: *mut LeanObject,
    mut v_ctorIdx_1493_: *mut LeanObject,
    mut v_t_1494_: *mut LeanObject,
    mut v_h_1495_: *mut LeanObject,
    mut v_k_1496_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1497_: *mut LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lake_EResult_ctorElim___redArg(v_t_1494_, v_k_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_EResult_ctorElim___boxed(
    mut v_00_u03b5_1498_: *mut LeanObject,
    mut v_00_u03c3_1499_: *mut LeanObject,
    mut v_00_u03b1_1500_: *mut LeanObject,
    mut v_motive_1501_: *mut LeanObject,
    mut v_ctorIdx_1502_: *mut LeanObject,
    mut v_t_1503_: *mut LeanObject,
    mut v_h_1504_: *mut LeanObject,
    mut v_k_1505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1506_: *mut LeanObject = core::ptr::null_mut();
    v_res_1506_ = l_Lake_EResult_ctorElim(
        v_00_u03b5_1498_,
        v_00_u03c3_1499_,
        v_00_u03b1_1500_,
        v_motive_1501_,
        v_ctorIdx_1502_,
        v_t_1503_,
        v_h_1504_,
        v_k_1505_,
    );
    lean_dec(v_ctorIdx_1502_);
    return v_res_1506_;
}
pub unsafe fn l_Lake_EResult_ok_elim___redArg(
    mut v_t_1507_: *mut LeanObject,
    mut v_ok_1508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1509_: *mut LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lake_EResult_ctorElim___redArg(v_t_1507_, v_ok_1508_);
    return v___x_1509_;
}
pub unsafe fn l_Lake_EResult_ok_elim(
    mut v_00_u03b5_1510_: *mut LeanObject,
    mut v_00_u03c3_1511_: *mut LeanObject,
    mut v_00_u03b1_1512_: *mut LeanObject,
    mut v_motive_1513_: *mut LeanObject,
    mut v_t_1514_: *mut LeanObject,
    mut v_h_1515_: *mut LeanObject,
    mut v_ok_1516_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1517_: *mut LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_Lake_EResult_ctorElim___redArg(v_t_1514_, v_ok_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Lake_EResult_error_elim___redArg(
    mut v_t_1518_: *mut LeanObject,
    mut v_error_1519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1520_: *mut LeanObject = core::ptr::null_mut();
    v___x_1520_ = l_Lake_EResult_ctorElim___redArg(v_t_1518_, v_error_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lake_EResult_error_elim(
    mut v_00_u03b5_1521_: *mut LeanObject,
    mut v_00_u03c3_1522_: *mut LeanObject,
    mut v_00_u03b1_1523_: *mut LeanObject,
    mut v_motive_1524_: *mut LeanObject,
    mut v_t_1525_: *mut LeanObject,
    mut v_h_1526_: *mut LeanObject,
    mut v_error_1527_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lake_EResult_ctorElim___redArg(v_t_1525_, v_error_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Lake_EResult_instInhabited___redArg(
    mut v_inst_1529_: *mut LeanObject,
    mut v_inst_1530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1531_: *mut LeanObject = core::ptr::null_mut();
    v___x_1531_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1531_, 0, v_inst_1529_);
    lean_ctor_set(v___x_1531_, 1, v_inst_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lake_EResult_instInhabited(
    mut v_00_u03b1_1532_: *mut LeanObject,
    mut v_00_u03c3_1533_: *mut LeanObject,
    mut v_00_u03b5_1534_: *mut LeanObject,
    mut v_inst_1535_: *mut LeanObject,
    mut v_inst_1536_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1537_: *mut LeanObject = core::ptr::null_mut();
    v___x_1537_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1537_, 0, v_inst_1535_);
    lean_ctor_set(v___x_1537_, 1, v_inst_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1___redArg(
    mut v_inst_1538_: *mut LeanObject,
    mut v_inst_1539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1540_: *mut LeanObject = core::ptr::null_mut();
    v___x_1540_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1540_, 0, v_inst_1538_);
    lean_ctor_set(v___x_1540_, 1, v_inst_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1(
    mut v_00_u03b5_1541_: *mut LeanObject,
    mut v_00_u03c3_1542_: *mut LeanObject,
    mut v_00_u03b1_1543_: *mut LeanObject,
    mut v_inst_1544_: *mut LeanObject,
    mut v_inst_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1546_, 0, v_inst_1544_);
    lean_ctor_set(v___x_1546_, 1, v_inst_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lake_EResult_state___redArg(mut v_x_1547_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_1548_: *mut LeanObject = core::ptr::null_mut();
    v_a_1548_ = lean_ctor_get(v_x_1547_, 1);
    lean_inc(v_a_1548_);
    return v_a_1548_;
}
pub unsafe fn l_Lake_EResult_state___redArg___boxed(
    mut v_x_1549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1550_: *mut LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_EResult_state___redArg(v_x_1549_);
    lean_dec_ref(v_x_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_EResult_state(
    mut v_00_u03b5_1551_: *mut LeanObject,
    mut v_00_u03c3_1552_: *mut LeanObject,
    mut v_00_u03b1_1553_: *mut LeanObject,
    mut v_x_1554_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1555_: *mut LeanObject = core::ptr::null_mut();
    v_a_1555_ = lean_ctor_get(v_x_1554_, 1);
    lean_inc(v_a_1555_);
    return v_a_1555_;
}
pub unsafe fn l_Lake_EResult_state___boxed(
    mut v_00_u03b5_1556_: *mut LeanObject,
    mut v_00_u03c3_1557_: *mut LeanObject,
    mut v_00_u03b1_1558_: *mut LeanObject,
    mut v_x_1559_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1560_: *mut LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lake_EResult_state(
        v_00_u03b5_1556_,
        v_00_u03c3_1557_,
        v_00_u03b1_1558_,
        v_x_1559_,
    );
    lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lake_EResult_modifyState___redArg(
    mut v_f_1561_: *mut LeanObject,
    mut v_x_1562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_a_1573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1562_) == 0 {
                    v_a_1563_ = lean_ctor_get(v_x_1562_, 0);
                    v_a_1564_ = lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1572_ = (!lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1566_ = v_x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1564_);
                        lean_inc(v_a_1563_);
                        lean_dec(v_x_1562_);
                        v___x_1566_ = lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1573_ = lean_ctor_get(v_x_1562_, 0);
                    v_a_1574_ = lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1582_ = (!lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1582_ == 0 {
                        v___x_1576_ = v_x_1562_;
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1574_);
                        lean_inc(v_a_1573_);
                        lean_dec(v_x_1562_);
                        v___x_1576_ = lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1568_ = lean_apply_1(v_f_1561_, v_a_1564_);
                if v_isShared_1567_ == 0 {
                    lean_ctor_set(v___x_1566_, 1, v___x_1568_);
                    v___x_1570_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1563_);
                    lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1570_;
            }
            3 => {
                v___x_1578_ = lean_apply_1(v_f_1561_, v_a_1574_);
                if v_isShared_1577_ == 0 {
                    lean_ctor_set(v___x_1576_, 1, v___x_1578_);
                    v___x_1580_ = v___x_1576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1573_);
                    lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
                    v___x_1580_ = v_reuseFailAlloc_1581_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1580_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_modifyState(
    mut v_00_u03c3_1583_: *mut LeanObject,
    mut v_00_u03c3_x27_1584_: *mut LeanObject,
    mut v_00_u03b5_1585_: *mut LeanObject,
    mut v_00_u03b1_1586_: *mut LeanObject,
    mut v_f_1587_: *mut LeanObject,
    mut v_x_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_a_1599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1588_) == 0 {
                    v_a_1589_ = lean_ctor_get(v_x_1588_, 0);
                    v_a_1590_ = lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1598_ = (!lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1598_ == 0 {
                        v___x_1592_ = v_x_1588_;
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1590_);
                        lean_inc(v_a_1589_);
                        lean_dec(v_x_1588_);
                        v___x_1592_ = lean_box(0);
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1599_ = lean_ctor_get(v_x_1588_, 0);
                    v_a_1600_ = lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1608_ = (!lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v___x_1602_ = v_x_1588_;
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1600_);
                        lean_inc(v_a_1599_);
                        lean_dec(v_x_1588_);
                        v___x_1602_ = lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1594_ = lean_apply_1(v_f_1587_, v_a_1590_);
                if v_isShared_1593_ == 0 {
                    lean_ctor_set(v___x_1592_, 1, v___x_1594_);
                    v___x_1596_ = v___x_1592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1589_);
                    lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1596_;
            }
            3 => {
                v___x_1604_ = lean_apply_1(v_f_1587_, v_a_1600_);
                if v_isShared_1603_ == 0 {
                    lean_ctor_set(v___x_1602_, 1, v___x_1604_);
                    v___x_1606_ = v___x_1602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1607_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1599_);
                    lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
                    v___x_1606_ = v_reuseFailAlloc_1607_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1606_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_setState___redArg(
    mut v_s_1609_: *mut LeanObject,
    mut v_r_1610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut v_unused_1619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_unused_1628_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_1610_) == 0 {
                    v_a_1611_ = lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1618_ = (!lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v_unused_1619_ = lean_ctor_get(v_r_1610_, 1);
                        lean_dec(v_unused_1619_);
                        v___x_1613_ = v_r_1610_;
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1611_);
                        lean_dec(v_r_1610_);
                        v___x_1613_ = lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1620_ = lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1627_ = (!lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v_unused_1628_ = lean_ctor_get(v_r_1610_, 1);
                        lean_dec(v_unused_1628_);
                        v___x_1622_ = v_r_1610_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1620_);
                        lean_dec(v_r_1610_);
                        v___x_1622_ = lean_box(0);
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1614_ == 0 {
                    lean_ctor_set(v___x_1613_, 1, v_s_1609_);
                    v___x_1616_ = v___x_1613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
                    lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_s_1609_);
                    v___x_1616_ = v_reuseFailAlloc_1617_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1616_;
            }
            3 => {
                if v_isShared_1623_ == 0 {
                    lean_ctor_set(v___x_1622_, 1, v_s_1609_);
                    v___x_1625_ = v___x_1622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
                    lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_s_1609_);
                    v___x_1625_ = v_reuseFailAlloc_1626_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_setState(
    mut v_00_u03c3_x27_1629_: *mut LeanObject,
    mut v_00_u03b5_1630_: *mut LeanObject,
    mut v_00_u03c3_1631_: *mut LeanObject,
    mut v_00_u03b1_1632_: *mut LeanObject,
    mut v_s_1633_: *mut LeanObject,
    mut v_r_1634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_unused_1652_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_r_1634_) == 0 {
                    v_a_1635_ = lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1642_ = (!lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1642_ == 0 {
                        v_unused_1643_ = lean_ctor_get(v_r_1634_, 1);
                        lean_dec(v_unused_1643_);
                        v___x_1637_ = v_r_1634_;
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1635_);
                        lean_dec(v_r_1634_);
                        v___x_1637_ = lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1644_ = lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1651_ = (!lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v_unused_1652_ = lean_ctor_get(v_r_1634_, 1);
                        lean_dec(v_unused_1652_);
                        v___x_1646_ = v_r_1634_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1644_);
                        lean_dec(v_r_1634_);
                        v___x_1646_ = lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1638_ == 0 {
                    lean_ctor_set(v___x_1637_, 1, v_s_1633_);
                    v___x_1640_ = v___x_1637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
                    lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_s_1633_);
                    v___x_1640_ = v_reuseFailAlloc_1641_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1640_;
            }
            3 => {
                if v_isShared_1647_ == 0 {
                    lean_ctor_set(v___x_1646_, 1, v_s_1633_);
                    v___x_1649_ = v___x_1646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_s_1633_);
                    v___x_1649_ = v_reuseFailAlloc_1650_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1649_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_toProd___redArg(mut v_x_1653_: *mut LeanObject) -> *mut LeanObject {
    let mut v_a_1654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_a_1664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1668_: u8 = 0;
    let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1653_) == 0 {
                    v_a_1654_ = lean_ctor_get(v_x_1653_, 0);
                    v_a_1655_ = lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1663_ = (!lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1657_ = v_x_1653_;
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1655_);
                        lean_inc(v_a_1654_);
                        lean_dec(v_x_1653_);
                        v___x_1657_ = lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1664_ = lean_ctor_get(v_x_1653_, 0);
                    v_a_1665_ = lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1673_ = (!lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1673_ == 0 {
                        v___x_1667_ = v_x_1653_;
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1665_);
                        lean_inc(v_a_1664_);
                        lean_dec(v_x_1653_);
                        v___x_1667_ = lean_box(0);
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1659_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1659_, 0, v_a_1654_);
                if v_isShared_1658_ == 0 {
                    lean_ctor_set(v___x_1657_, 0, v___x_1659_);
                    v___x_1661_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
                    lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1661_;
            }
            3 => {
                v___x_1669_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1669_, 0, v_a_1664_);
                if v_isShared_1668_ == 0 {
                    lean_ctor_set_tag(v___x_1667_, 0);
                    lean_ctor_set(v___x_1667_, 0, v___x_1669_);
                    v___x_1671_ = v___x_1667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
                    lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1665_);
                    v___x_1671_ = v_reuseFailAlloc_1672_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_toProd(
    mut v_00_u03b5_1674_: *mut LeanObject,
    mut v_00_u03c3_1675_: *mut LeanObject,
    mut v_00_u03b1_1676_: *mut LeanObject,
    mut v_x_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1677_) == 0 {
                    v_a_1678_ = lean_ctor_get(v_x_1677_, 0);
                    v_a_1679_ = lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1687_ = (!lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1681_ = v_x_1677_;
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1679_);
                        lean_inc(v_a_1678_);
                        lean_dec(v_x_1677_);
                        v___x_1681_ = lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1688_ = lean_ctor_get(v_x_1677_, 0);
                    v_a_1689_ = lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1697_ = (!lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1691_ = v_x_1677_;
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1689_);
                        lean_inc(v_a_1688_);
                        lean_dec(v_x_1677_);
                        v___x_1691_ = lean_box(0);
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1683_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1683_, 0, v_a_1678_);
                if v_isShared_1682_ == 0 {
                    lean_ctor_set(v___x_1681_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1679_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1685_;
            }
            3 => {
                v___x_1693_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1693_, 0, v_a_1688_);
                if v_isShared_1692_ == 0 {
                    lean_ctor_set_tag(v___x_1691_, 0);
                    lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                    v___x_1695_ = v___x_1691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
                    lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1689_);
                    v___x_1695_ = v_reuseFailAlloc_1696_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1695_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_toProd_x3f___redArg(
    mut v_x_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1698_) == 0 {
                    v_a_1699_ = lean_ctor_get(v_x_1698_, 0);
                    v_a_1700_ = lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1708_ = (!lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v_x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1700_);
                        lean_inc(v_a_1699_);
                        lean_dec(v_x_1698_);
                        v___x_1702_ = lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1709_ = lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1717_ = (!lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = lean_ctor_get(v_x_1698_, 0);
                        lean_dec(v_unused_1718_);
                        v___x_1711_ = v_x_1698_;
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1709_);
                        lean_dec(v_x_1698_);
                        v___x_1711_ = lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1704_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1704_, 0, v_a_1699_);
                if v_isShared_1703_ == 0 {
                    lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                v___x_1713_ = lean_box(0);
                if v_isShared_1712_ == 0 {
                    lean_ctor_set_tag(v___x_1711_, 0);
                    lean_ctor_set(v___x_1711_, 0, v___x_1713_);
                    v___x_1715_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
                    lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1709_);
                    v___x_1715_ = v_reuseFailAlloc_1716_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_toProd_x3f(
    mut v_00_u03b5_1719_: *mut LeanObject,
    mut v_00_u03c3_1720_: *mut LeanObject,
    mut v_00_u03b1_1721_: *mut LeanObject,
    mut v_x_1722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1722_) == 0 {
                    v_a_1723_ = lean_ctor_get(v_x_1722_, 0);
                    v_a_1724_ = lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1732_ = (!lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1726_ = v_x_1722_;
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1724_);
                        lean_inc(v_a_1723_);
                        lean_dec(v_x_1722_);
                        v___x_1726_ = lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1733_ = lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1741_ = (!lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1741_ == 0 {
                        v_unused_1742_ = lean_ctor_get(v_x_1722_, 0);
                        lean_dec(v_unused_1742_);
                        v___x_1735_ = v_x_1722_;
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1733_);
                        lean_dec(v_x_1722_);
                        v___x_1735_ = lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1728_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1728_, 0, v_a_1723_);
                if v_isShared_1727_ == 0 {
                    lean_ctor_set(v___x_1726_, 0, v___x_1728_);
                    v___x_1730_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                    lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1724_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1730_;
            }
            3 => {
                v___x_1737_ = lean_box(0);
                if v_isShared_1736_ == 0 {
                    lean_ctor_set_tag(v___x_1735_, 0);
                    lean_ctor_set(v___x_1735_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1733_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___redArg(
    mut v_x_1743_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1743_) == 0 {
        let mut v_a_1744_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
        v_a_1744_ = lean_ctor_get(v_x_1743_, 0);
        lean_inc(v_a_1744_);
        v___x_1745_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1745_, 0, v_a_1744_);
        return v___x_1745_;
    } else {
        let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
        v___x_1746_ = lean_box(0);
        return v___x_1746_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___redArg___boxed(
    mut v_x_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1748_: *mut LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lake_EResult_result_x3f___redArg(v_x_1747_);
    lean_dec_ref(v_x_1747_);
    return v_res_1748_;
}
pub unsafe fn l_Lake_EResult_result_x3f(
    mut v_00_u03b5_1749_: *mut LeanObject,
    mut v_00_u03c3_1750_: *mut LeanObject,
    mut v_00_u03b1_1751_: *mut LeanObject,
    mut v_x_1752_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1752_) == 0 {
        let mut v_a_1753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
        v_a_1753_ = lean_ctor_get(v_x_1752_, 0);
        lean_inc(v_a_1753_);
        v___x_1754_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1754_, 0, v_a_1753_);
        return v___x_1754_;
    } else {
        let mut v___x_1755_: *mut LeanObject = core::ptr::null_mut();
        v___x_1755_ = lean_box(0);
        return v___x_1755_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___boxed(
    mut v_00_u03b5_1756_: *mut LeanObject,
    mut v_00_u03c3_1757_: *mut LeanObject,
    mut v_00_u03b1_1758_: *mut LeanObject,
    mut v_x_1759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1760_: *mut LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lake_EResult_result_x3f(
        v_00_u03b5_1756_,
        v_00_u03c3_1757_,
        v_00_u03b1_1758_,
        v_x_1759_,
    );
    lean_dec_ref(v_x_1759_);
    return v_res_1760_;
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg(mut v_x_1761_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1761_) == 0 {
        let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
        v___x_1762_ = lean_box(0);
        return v___x_1762_;
    } else {
        let mut v_a_1763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
        v_a_1763_ = lean_ctor_get(v_x_1761_, 0);
        lean_inc(v_a_1763_);
        v___x_1764_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1764_, 0, v_a_1763_);
        return v___x_1764_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg___boxed(
    mut v_x_1765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1766_: *mut LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lake_EResult_error_x3f___redArg(v_x_1765_);
    lean_dec_ref(v_x_1765_);
    return v_res_1766_;
}
pub unsafe fn l_Lake_EResult_error_x3f(
    mut v_00_u03b5_1767_: *mut LeanObject,
    mut v_00_u03c3_1768_: *mut LeanObject,
    mut v_00_u03b1_1769_: *mut LeanObject,
    mut v_x_1770_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1770_) == 0 {
        let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
        v___x_1771_ = lean_box(0);
        return v___x_1771_;
    } else {
        let mut v_a_1772_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
        v_a_1772_ = lean_ctor_get(v_x_1770_, 0);
        lean_inc(v_a_1772_);
        v___x_1773_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1773_, 0, v_a_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___boxed(
    mut v_00_u03b5_1774_: *mut LeanObject,
    mut v_00_u03c3_1775_: *mut LeanObject,
    mut v_00_u03b1_1776_: *mut LeanObject,
    mut v_x_1777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1778_: *mut LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lake_EResult_error_x3f(
        v_00_u03b5_1774_,
        v_00_u03c3_1775_,
        v_00_u03b1_1776_,
        v_x_1777_,
    );
    lean_dec_ref(v_x_1777_);
    return v_res_1778_;
}
pub unsafe fn l_Lake_EResult_toExcept___redArg(mut v_x_1779_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1779_) == 0 {
        let mut v_a_1780_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut LeanObject = core::ptr::null_mut();
        v_a_1780_ = lean_ctor_get(v_x_1779_, 0);
        lean_inc(v_a_1780_);
        v___x_1781_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1781_, 0, v_a_1780_);
        return v___x_1781_;
    } else {
        let mut v_a_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
        v_a_1782_ = lean_ctor_get(v_x_1779_, 0);
        lean_inc(v_a_1782_);
        v___x_1783_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1783_, 0, v_a_1782_);
        return v___x_1783_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___redArg___boxed(
    mut v_x_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1785_: *mut LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lake_EResult_toExcept___redArg(v_x_1784_);
    lean_dec_ref(v_x_1784_);
    return v_res_1785_;
}
pub unsafe fn l_Lake_EResult_toExcept(
    mut v_00_u03b5_1786_: *mut LeanObject,
    mut v_00_u03c3_1787_: *mut LeanObject,
    mut v_00_u03b1_1788_: *mut LeanObject,
    mut v_x_1789_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1789_) == 0 {
        let mut v_a_1790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
        v_a_1790_ = lean_ctor_get(v_x_1789_, 0);
        lean_inc(v_a_1790_);
        v___x_1791_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1791_, 0, v_a_1790_);
        return v___x_1791_;
    } else {
        let mut v_a_1792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
        v_a_1792_ = lean_ctor_get(v_x_1789_, 0);
        lean_inc(v_a_1792_);
        v___x_1793_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_1793_, 0, v_a_1792_);
        return v___x_1793_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___boxed(
    mut v_00_u03b5_1794_: *mut LeanObject,
    mut v_00_u03c3_1795_: *mut LeanObject,
    mut v_00_u03b1_1796_: *mut LeanObject,
    mut v_x_1797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1798_: *mut LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lake_EResult_toExcept(
        v_00_u03b5_1794_,
        v_00_u03c3_1795_,
        v_00_u03b1_1796_,
        v_x_1797_,
    );
    lean_dec_ref(v_x_1797_);
    return v_res_1798_;
}
pub unsafe fn l_Lake_EResult_map___redArg(
    mut v_f_1799_: *mut LeanObject,
    mut v_x_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_a_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1800_) == 0 {
                    v_a_1801_ = lean_ctor_get(v_x_1800_, 0);
                    v_a_1802_ = lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1810_ = (!lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1810_ == 0 {
                        v___x_1804_ = v_x_1800_;
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1802_);
                        lean_inc(v_a_1801_);
                        lean_dec(v_x_1800_);
                        v___x_1804_ = lean_box(0);
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1799_);
                    v_a_1811_ = lean_ctor_get(v_x_1800_, 0);
                    v_a_1812_ = lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1819_ = (!lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1814_ = v_x_1800_;
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1812_);
                        lean_inc(v_a_1811_);
                        lean_dec(v_x_1800_);
                        v___x_1814_ = lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1806_ = lean_apply_1(v_f_1799_, v_a_1801_);
                if v_isShared_1805_ == 0 {
                    lean_ctor_set(v___x_1804_, 0, v___x_1806_);
                    v___x_1808_ = v___x_1804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                    lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1802_);
                    v___x_1808_ = v_reuseFailAlloc_1809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1808_;
            }
            3 => {
                if v_isShared_1815_ == 0 {
                    v___x_1817_ = v___x_1814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
                    lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1812_);
                    v___x_1817_ = v_reuseFailAlloc_1818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_map(
    mut v_00_u03b1_1820_: *mut LeanObject,
    mut v_00_u03b2_1821_: *mut LeanObject,
    mut v_00_u03b5_1822_: *mut LeanObject,
    mut v_00_u03c3_1823_: *mut LeanObject,
    mut v_f_1824_: *mut LeanObject,
    mut v_x_1825_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut v_a_1836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1825_) == 0 {
                    v_a_1826_ = lean_ctor_get(v_x_1825_, 0);
                    v_a_1827_ = lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1835_ = (!lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1829_ = v_x_1825_;
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1827_);
                        lean_inc(v_a_1826_);
                        lean_dec(v_x_1825_);
                        v___x_1829_ = lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_1824_);
                    v_a_1836_ = lean_ctor_get(v_x_1825_, 0);
                    v_a_1837_ = lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1844_ = (!lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1844_ == 0 {
                        v___x_1839_ = v_x_1825_;
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1837_);
                        lean_inc(v_a_1836_);
                        lean_dec(v_x_1825_);
                        v___x_1839_ = lean_box(0);
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1831_ = lean_apply_1(v_f_1824_, v_a_1826_);
                if v_isShared_1830_ == 0 {
                    lean_ctor_set(v___x_1829_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
                    lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1827_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1833_;
            }
            3 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1836_);
                    lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1837_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_instFunctor___lam__0(
    mut v_00_u03b1_1845_: *mut LeanObject,
    mut v_00_u03b2_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_a_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v___y_1848_) == 0 {
                    v_a_1849_ = lean_ctor_get(v___y_1848_, 0);
                    v_a_1850_ = lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1858_ = (!lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1852_ = v___y_1848_;
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1850_);
                        lean_inc(v_a_1849_);
                        lean_dec(v___y_1848_);
                        v___x_1852_ = lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_1847_);
                    v_a_1859_ = lean_ctor_get(v___y_1848_, 0);
                    v_a_1860_ = lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1867_ = (!lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v___x_1862_ = v___y_1848_;
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1860_);
                        lean_inc(v_a_1859_);
                        lean_dec(v___y_1848_);
                        v___x_1862_ = lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1854_ = lean_apply_1(v___y_1847_, v_a_1849_);
                if v_isShared_1853_ == 0 {
                    lean_ctor_set(v___x_1852_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1850_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1856_;
            }
            3 => {
                if v_isShared_1863_ == 0 {
                    v___x_1865_ = v___x_1862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1866_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1859_);
                    lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_a_1860_);
                    v___x_1865_ = v_reuseFailAlloc_1866_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_instFunctor___lam__1(
    mut v___f_1868_: *mut LeanObject,
    mut v_00_u03b1_1869_: *mut LeanObject,
    mut v_00_u03b2_1870_: *mut LeanObject,
    mut v___y_1871_: *mut LeanObject,
    mut v___y_1872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_1873_, 0, lean_box(0));
    lean_closure_set(v___x_1873_, 1, lean_box(0));
    lean_closure_set(v___x_1873_, 2, v___y_1871_);
    v___x_1874_ = lean_apply_4(
        v___f_1868_,
        lean_box(0),
        lean_box(0),
        v___x_1873_,
        v___y_1872_,
    );
    return v___x_1874_;
}
pub unsafe fn l_Lake_EResult_instFunctor(
    mut v_00_u03b5_1881_: *mut LeanObject,
    mut v_00_u03c3_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lake_EResult_instFunctor___closed__2;
    return v___x_1883_;
}
pub unsafe fn l_Lake_EResult_toEStateMResult___redArg(
    mut v_x_1884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_a_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1884_) == 0 {
                    v_a_1885_ = lean_ctor_get(v_x_1884_, 0);
                    v_a_1886_ = lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1893_ = (!lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1888_ = v_x_1884_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1886_);
                        lean_inc(v_a_1885_);
                        lean_dec(v_x_1884_);
                        v___x_1888_ = lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1894_ = lean_ctor_get(v_x_1884_, 0);
                    v_a_1895_ = lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1902_ = (!lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1902_ == 0 {
                        v___x_1897_ = v_x_1884_;
                        v_isShared_1898_ = v_isSharedCheck_1902_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1895_);
                        lean_inc(v_a_1894_);
                        lean_dec(v_x_1884_);
                        v___x_1897_ = lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_1902_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1889_ == 0 {
                    v___x_1891_ = v___x_1888_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1892_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1885_);
                    lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1886_);
                    v___x_1891_ = v_reuseFailAlloc_1892_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1891_;
            }
            3 => {
                if v_isShared_1898_ == 0 {
                    v___x_1900_ = v___x_1897_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1901_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1894_);
                    lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1895_);
                    v___x_1900_ = v_reuseFailAlloc_1901_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_toEStateMResult(
    mut v_00_u03b5_1903_: *mut LeanObject,
    mut v_00_u03c3_1904_: *mut LeanObject,
    mut v_00_u03b1_1905_: *mut LeanObject,
    mut v_x_1906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lake_EResult_toEStateMResult___redArg(v_x_1906_);
    return v___x_1907_;
}
pub unsafe fn l_Lake_EResult_ofEStateMResult___redArg(
    mut v_x_1908_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1908_) == 0 {
                    v_a_1909_ = lean_ctor_get(v_x_1908_, 0);
                    v_a_1910_ = lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1917_ = (!lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1917_ == 0 {
                        v___x_1912_ = v_x_1908_;
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1910_);
                        lean_inc(v_a_1909_);
                        lean_dec(v_x_1908_);
                        v___x_1912_ = lean_box(0);
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1918_ = lean_ctor_get(v_x_1908_, 0);
                    v_a_1919_ = lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1926_ = (!lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1921_ = v_x_1908_;
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_1919_);
                        lean_inc(v_a_1918_);
                        lean_dec(v_x_1908_);
                        v___x_1921_ = lean_box(0);
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1913_ == 0 {
                    v___x_1915_ = v___x_1912_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1916_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
                    lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1910_);
                    v___x_1915_ = v_reuseFailAlloc_1916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1915_;
            }
            3 => {
                if v_isShared_1922_ == 0 {
                    v___x_1924_ = v___x_1921_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1925_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1918_);
                    lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1919_);
                    v___x_1924_ = v_reuseFailAlloc_1925_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1924_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EResult_ofEStateMResult(
    mut v_00_u03b5_1927_: *mut LeanObject,
    mut v_00_u03c3_1928_: *mut LeanObject,
    mut v_00_u03b1_1929_: *mut LeanObject,
    mut v_x_1930_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1931_: *mut LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_1930_);
    return v___x_1931_;
}
pub unsafe fn l_Lake_EStateT_mk___redArg(
    mut v_x_1932_: *mut LeanObject,
    mut v_a_1933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1934_: *mut LeanObject = core::ptr::null_mut();
    v___x_1934_ = lean_apply_1(v_x_1932_, v_a_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lake_EStateT_mk(
    mut v_00_u03b5_1935_: *mut LeanObject,
    mut v_00_u03c3_1936_: *mut LeanObject,
    mut v_00_u03b1_1937_: *mut LeanObject,
    mut v_m_1938_: *mut LeanObject,
    mut v_x_1939_: *mut LeanObject,
    mut v_a_1940_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1941_: *mut LeanObject = core::ptr::null_mut();
    v___x_1941_ = lean_apply_1(v_x_1939_, v_a_1940_);
    return v___x_1941_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(
    mut v_inst_1942_: *mut LeanObject,
    mut v_inst_1943_: *mut LeanObject,
    mut v_s_1944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut LeanObject = core::ptr::null_mut();
    v___x_1945_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_1945_, 0, v_inst_1942_);
    lean_ctor_set(v___x_1945_, 1, v_s_1944_);
    v___x_1946_ = lean_apply_2(v_inst_1943_, lean_box(0), v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(
    mut v_inst_1947_: *mut LeanObject,
    mut v_inst_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1949_: *mut LeanObject = core::ptr::null_mut();
    v___f_1949_ = lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1949_, 0, v_inst_1947_);
    lean_closure_set(v___f_1949_, 1, v_inst_1948_);
    return v___f_1949_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(
    mut v_00_u03b5_1950_: *mut LeanObject,
    mut v_00_u03c3_1951_: *mut LeanObject,
    mut v_00_u03b1_1952_: *mut LeanObject,
    mut v_m_1953_: *mut LeanObject,
    mut v_inst_1954_: *mut LeanObject,
    mut v_inst_1955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1956_: *mut LeanObject = core::ptr::null_mut();
    v___f_1956_ = lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1956_, 0, v_inst_1954_);
    lean_closure_set(v___f_1956_, 1, v_inst_1955_);
    return v___f_1956_;
}
pub unsafe fn l_Lake_EStateT_run___redArg(
    mut v_init_1957_: *mut LeanObject,
    mut v_self_1958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    v___x_1959_ = lean_apply_1(v_self_1958_, v_init_1957_);
    return v___x_1959_;
}
pub unsafe fn l_Lake_EStateT_run(
    mut v_00_u03b5_1960_: *mut LeanObject,
    mut v_00_u03c3_1961_: *mut LeanObject,
    mut v_00_u03b1_1962_: *mut LeanObject,
    mut v_m_1963_: *mut LeanObject,
    mut v_init_1964_: *mut LeanObject,
    mut v_self_1965_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1966_: *mut LeanObject = core::ptr::null_mut();
    v___x_1966_ = lean_apply_1(v_self_1965_, v_init_1964_);
    return v___x_1966_;
}
pub unsafe fn l_Lake_EStateT_run_x27___redArg(
    mut v_inst_1968_: *mut LeanObject,
    mut v_init_1969_: *mut LeanObject,
    mut v_x_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut LeanObject = core::ptr::null_mut();
    v_map_1971_ = lean_ctor_get(v_inst_1968_, 0);
    lean_inc(v_map_1971_);
    lean_dec_ref(v_inst_1968_);
    v___x_1972_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1973_ = lean_apply_1(v_x_1970_, v_init_1969_);
    v___x_1974_ = lean_apply_4(
        v_map_1971_,
        lean_box(0),
        lean_box(0),
        v___x_1972_,
        v___x_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn l_Lake_EStateT_run_x27(
    mut v_00_u03b5_1975_: *mut LeanObject,
    mut v_00_u03b1_1976_: *mut LeanObject,
    mut v_m_1977_: *mut LeanObject,
    mut v_00_u03c3_1978_: *mut LeanObject,
    mut v_inst_1979_: *mut LeanObject,
    mut v_init_1980_: *mut LeanObject,
    mut v_x_1981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut LeanObject = core::ptr::null_mut();
    v_map_1982_ = lean_ctor_get(v_inst_1979_, 0);
    lean_inc(v_map_1982_);
    lean_dec_ref(v_inst_1979_);
    v___x_1983_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1984_ = lean_apply_1(v_x_1981_, v_init_1980_);
    v___x_1985_ = lean_apply_4(
        v_map_1982_,
        lean_box(0),
        lean_box(0),
        v___x_1983_,
        v___x_1984_,
    );
    return v___x_1985_;
}
pub unsafe fn l_Lake_EStateT_toStateT___redArg(
    mut v_inst_1987_: *mut LeanObject,
    mut v_x_1988_: *mut LeanObject,
    mut v_s_1989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut LeanObject = core::ptr::null_mut();
    v_map_1990_ = lean_ctor_get(v_inst_1987_, 0);
    lean_inc(v_map_1990_);
    lean_dec_ref(v_inst_1987_);
    v___x_1991_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_1992_ = lean_apply_1(v_x_1988_, v_s_1989_);
    v___x_1993_ = lean_apply_4(
        v_map_1990_,
        lean_box(0),
        lean_box(0),
        v___x_1991_,
        v___x_1992_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_EStateT_toStateT(
    mut v_m_1994_: *mut LeanObject,
    mut v_00_u03b5_1995_: *mut LeanObject,
    mut v_00_u03c3_1996_: *mut LeanObject,
    mut v_00_u03b1_1997_: *mut LeanObject,
    mut v_inst_1998_: *mut LeanObject,
    mut v_x_1999_: *mut LeanObject,
    mut v_s_2000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut LeanObject = core::ptr::null_mut();
    v_map_2001_ = lean_ctor_get(v_inst_1998_, 0);
    lean_inc(v_map_2001_);
    lean_dec_ref(v_inst_1998_);
    v___x_2002_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_2003_ = lean_apply_1(v_x_1999_, v_s_2000_);
    v___x_2004_ = lean_apply_4(
        v_map_2001_,
        lean_box(0),
        lean_box(0),
        v___x_2002_,
        v___x_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f___redArg(
    mut v_inst_2006_: *mut LeanObject,
    mut v_x_2007_: *mut LeanObject,
    mut v_s_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut LeanObject = core::ptr::null_mut();
    v_map_2009_ = lean_ctor_get(v_inst_2006_, 0);
    lean_inc(v_map_2009_);
    lean_dec_ref(v_inst_2006_);
    v___x_2010_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2011_ = lean_apply_1(v_x_2007_, v_s_2008_);
    v___x_2012_ = lean_apply_4(
        v_map_2009_,
        lean_box(0),
        lean_box(0),
        v___x_2010_,
        v___x_2011_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f(
    mut v_m_2013_: *mut LeanObject,
    mut v_00_u03b5_2014_: *mut LeanObject,
    mut v_00_u03c3_2015_: *mut LeanObject,
    mut v_00_u03b1_2016_: *mut LeanObject,
    mut v_inst_2017_: *mut LeanObject,
    mut v_x_2018_: *mut LeanObject,
    mut v_s_2019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    v_map_2020_ = lean_ctor_get(v_inst_2017_, 0);
    lean_inc(v_map_2020_);
    lean_dec_ref(v_inst_2017_);
    v___x_2021_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2022_ = lean_apply_1(v_x_2018_, v_s_2019_);
    v___x_2023_ = lean_apply_4(
        v_map_2020_,
        lean_box(0),
        lean_box(0),
        v___x_2021_,
        v___x_2022_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lake_EStateT_run_x3f___redArg(
    mut v_inst_2024_: *mut LeanObject,
    mut v_init_2025_: *mut LeanObject,
    mut v_x_2026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut LeanObject = core::ptr::null_mut();
    v_map_2027_ = lean_ctor_get(v_inst_2024_, 0);
    lean_inc(v_map_2027_);
    lean_dec_ref(v_inst_2024_);
    v___x_2028_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2029_ = lean_apply_1(v_x_2026_, v_init_2025_);
    v___x_2030_ = lean_apply_4(
        v_map_2027_,
        lean_box(0),
        lean_box(0),
        v___x_2028_,
        v___x_2029_,
    );
    return v___x_2030_;
}
pub unsafe fn l_Lake_EStateT_run_x3f(
    mut v_00_u03c3_2031_: *mut LeanObject,
    mut v_00_u03b1_2032_: *mut LeanObject,
    mut v_m_2033_: *mut LeanObject,
    mut v_00_u03b5_2034_: *mut LeanObject,
    mut v_inst_2035_: *mut LeanObject,
    mut v_init_2036_: *mut LeanObject,
    mut v_x_2037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    v_map_2038_ = lean_ctor_get(v_inst_2035_, 0);
    lean_inc(v_map_2038_);
    lean_dec_ref(v_inst_2035_);
    v___x_2039_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2040_ = lean_apply_1(v_x_2037_, v_init_2036_);
    v___x_2041_ = lean_apply_4(
        v_map_2038_,
        lean_box(0),
        lean_box(0),
        v___x_2039_,
        v___x_2040_,
    );
    return v___x_2041_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27___redArg(
    mut v_inst_2043_: *mut LeanObject,
    mut v_init_2044_: *mut LeanObject,
    mut v_x_2045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut LeanObject = core::ptr::null_mut();
    v_map_2046_ = lean_ctor_get(v_inst_2043_, 0);
    lean_inc(v_map_2046_);
    lean_dec_ref(v_inst_2043_);
    v___x_2047_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2048_ = lean_apply_1(v_x_2045_, v_init_2044_);
    v___x_2049_ = lean_apply_4(
        v_map_2046_,
        lean_box(0),
        lean_box(0),
        v___x_2047_,
        v___x_2048_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27(
    mut v_m_2050_: *mut LeanObject,
    mut v_00_u03b5_2051_: *mut LeanObject,
    mut v_00_u03c3_2052_: *mut LeanObject,
    mut v_00_u03b1_2053_: *mut LeanObject,
    mut v_inst_2054_: *mut LeanObject,
    mut v_init_2055_: *mut LeanObject,
    mut v_x_2056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    v_map_2057_ = lean_ctor_get(v_inst_2054_, 0);
    lean_inc(v_map_2057_);
    lean_dec_ref(v_inst_2054_);
    v___x_2058_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2059_ = lean_apply_1(v_x_2056_, v_init_2055_);
    v___x_2060_ = lean_apply_4(
        v_map_2057_,
        lean_box(0),
        lean_box(0),
        v___x_2058_,
        v___x_2059_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg___lam__0(
    mut v_toPure_2061_: *mut LeanObject,
    mut v_h_2062_: *mut LeanObject,
    mut v_____do__lift_2063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2063_) == 0 {
                    lean_dec(v_h_2062_);
                    v_a_2064_ = lean_ctor_get(v_____do__lift_2063_, 0);
                    v_a_2065_ = lean_ctor_get(v_____do__lift_2063_, 1);
                    v_isSharedCheck_2073_ = (!lean_is_exclusive(v_____do__lift_2063_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2067_ = v_____do__lift_2063_;
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2065_);
                        lean_inc(v_a_2064_);
                        lean_dec(v_____do__lift_2063_);
                        v___x_2067_ = lean_box(0);
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_toPure_2061_);
                    v_a_2074_ = lean_ctor_get(v_____do__lift_2063_, 0);
                    lean_inc(v_a_2074_);
                    v_a_2075_ = lean_ctor_get(v_____do__lift_2063_, 1);
                    lean_inc(v_a_2075_);
                    lean_dec_ref_known(v_____do__lift_2063_, 2);
                    v___x_2076_ = lean_apply_2(v_h_2062_, v_a_2074_, v_a_2075_);
                    return v___x_2076_;
                }
            }
            1 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2064_);
                    lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2071_ = lean_apply_2(v_toPure_2061_, lean_box(0), v___x_2070_);
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg(
    mut v_inst_2077_: *mut LeanObject,
    mut v_x_2078_: *mut LeanObject,
    mut v_h_2079_: *mut LeanObject,
    mut v_s_2080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2081_ = lean_ctor_get(v_inst_2077_, 0);
    lean_inc_ref(v_toApplicative_2081_);
    v_toBind_2082_ = lean_ctor_get(v_inst_2077_, 1);
    lean_inc(v_toBind_2082_);
    lean_dec_ref(v_inst_2077_);
    v_toPure_2083_ = lean_ctor_get(v_toApplicative_2081_, 1);
    lean_inc(v_toPure_2083_);
    lean_dec_ref(v_toApplicative_2081_);
    v___x_2084_ = lean_apply_1(v_x_2078_, v_s_2080_);
    v___f_2085_ = lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2085_, 0, v_toPure_2083_);
    lean_closure_set(v___f_2085_, 1, v_h_2079_);
    v___x_2086_ = lean_apply_4(
        v_toBind_2082_,
        lean_box(0),
        lean_box(0),
        v___x_2084_,
        v___f_2085_,
    );
    return v___x_2086_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions(
    mut v_m_2087_: *mut LeanObject,
    mut v_00_u03b5_2088_: *mut LeanObject,
    mut v_00_u03c3_2089_: *mut LeanObject,
    mut v_00_u03b1_2090_: *mut LeanObject,
    mut v_inst_2091_: *mut LeanObject,
    mut v_x_2092_: *mut LeanObject,
    mut v_h_2093_: *mut LeanObject,
    mut v_s_2094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2095_ = lean_ctor_get(v_inst_2091_, 0);
    lean_inc_ref(v_toApplicative_2095_);
    v_toBind_2096_ = lean_ctor_get(v_inst_2091_, 1);
    lean_inc(v_toBind_2096_);
    lean_dec_ref(v_inst_2091_);
    v_toPure_2097_ = lean_ctor_get(v_toApplicative_2095_, 1);
    lean_inc(v_toPure_2097_);
    lean_dec_ref(v_toApplicative_2095_);
    v___x_2098_ = lean_apply_1(v_x_2092_, v_s_2094_);
    v___f_2099_ = lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2099_, 0, v_toPure_2097_);
    lean_closure_set(v___f_2099_, 1, v_h_2093_);
    v___x_2100_ = lean_apply_4(
        v_toBind_2096_,
        lean_box(0),
        lean_box(0),
        v___x_2098_,
        v___f_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg___lam__0(
    mut v_s_2101_: *mut LeanObject,
    mut v_toPure_2102_: *mut LeanObject,
    mut v_a_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut LeanObject = core::ptr::null_mut();
    v___x_2104_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2104_, 0, v_a_2103_);
    lean_ctor_set(v___x_2104_, 1, v_s_2101_);
    v___x_2105_ = lean_apply_2(v_toPure_2102_, lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg(
    mut v_inst_2106_: *mut LeanObject,
    mut v_x_2107_: *mut LeanObject,
    mut v_s_2108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2109_ = lean_ctor_get(v_inst_2106_, 0);
    lean_inc_ref(v_toApplicative_2109_);
    v_toBind_2110_ = lean_ctor_get(v_inst_2106_, 1);
    lean_inc(v_toBind_2110_);
    lean_dec_ref(v_inst_2106_);
    v_toPure_2111_ = lean_ctor_get(v_toApplicative_2109_, 1);
    lean_inc(v_toPure_2111_);
    lean_dec_ref(v_toApplicative_2109_);
    v___f_2112_ = lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2112_, 0, v_s_2108_);
    lean_closure_set(v___f_2112_, 1, v_toPure_2111_);
    v___x_2113_ = lean_apply_4(
        v_toBind_2110_,
        lean_box(0),
        lean_box(0),
        v_x_2107_,
        v___f_2112_,
    );
    return v___x_2113_;
}
pub unsafe fn l_Lake_EStateT_lift(
    mut v_m_2114_: *mut LeanObject,
    mut v_00_u03b5_2115_: *mut LeanObject,
    mut v_00_u03c3_2116_: *mut LeanObject,
    mut v_00_u03b1_2117_: *mut LeanObject,
    mut v_inst_2118_: *mut LeanObject,
    mut v_x_2119_: *mut LeanObject,
    mut v_s_2120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2121_ = lean_ctor_get(v_inst_2118_, 0);
    lean_inc_ref(v_toApplicative_2121_);
    v_toBind_2122_ = lean_ctor_get(v_inst_2118_, 1);
    lean_inc(v_toBind_2122_);
    lean_dec_ref(v_inst_2118_);
    v_toPure_2123_ = lean_ctor_get(v_toApplicative_2121_, 1);
    lean_inc(v_toPure_2123_);
    lean_dec_ref(v_toApplicative_2121_);
    v___f_2124_ = lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2124_, 0, v_s_2120_);
    lean_closure_set(v___f_2124_, 1, v_toPure_2123_);
    v___x_2125_ = lean_apply_4(
        v_toBind_2122_,
        lean_box(0),
        lean_box(0),
        v_x_2119_,
        v___f_2124_,
    );
    return v___x_2125_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(
    mut v___y_2126_: *mut LeanObject,
    mut v_toPure_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    v___x_2129_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2129_, 0, v_a_2128_);
    lean_ctor_set(v___x_2129_, 1, v___y_2126_);
    v___x_2130_ = lean_apply_2(v_toPure_2127_, lean_box(0), v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(
    mut v_inst_2131_: *mut LeanObject,
    mut v_00_u03b1_2132_: *mut LeanObject,
    mut v___y_2133_: *mut LeanObject,
    mut v___y_2134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2135_ = lean_ctor_get(v_inst_2131_, 0);
    lean_inc_ref(v_toApplicative_2135_);
    v_toBind_2136_ = lean_ctor_get(v_inst_2131_, 1);
    lean_inc(v_toBind_2136_);
    lean_dec_ref(v_inst_2131_);
    v_toPure_2137_ = lean_ctor_get(v_toApplicative_2135_, 1);
    lean_inc(v_toPure_2137_);
    lean_dec_ref(v_toApplicative_2135_);
    v___f_2138_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2138_, 0, v___y_2134_);
    lean_closure_set(v___f_2138_, 1, v_toPure_2137_);
    v___x_2139_ = lean_apply_4(
        v_toBind_2136_,
        lean_box(0),
        lean_box(0),
        v___y_2133_,
        v___f_2138_,
    );
    return v___x_2139_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg(
    mut v_inst_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2141_: *mut LeanObject = core::ptr::null_mut();
    v___f_2141_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2141_, 0, v_inst_2140_);
    return v___f_2141_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad(
    mut v_m_2142_: *mut LeanObject,
    mut v_00_u03b5_2143_: *mut LeanObject,
    mut v_00_u03c3_2144_: *mut LeanObject,
    mut v_inst_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2146_: *mut LeanObject = core::ptr::null_mut();
    v___f_2146_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2146_, 0, v_inst_2145_);
    return v___f_2146_;
}
pub unsafe fn l_Lake_EStateT_pure___redArg(
    mut v_inst_2147_: *mut LeanObject,
    mut v_a_2148_: *mut LeanObject,
    mut v_s_2149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    v___x_2150_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2150_, 0, v_a_2148_);
    lean_ctor_set(v___x_2150_, 1, v_s_2149_);
    v___x_2151_ = lean_apply_2(v_inst_2147_, lean_box(0), v___x_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lake_EStateT_pure(
    mut v_00_u03b5_2152_: *mut LeanObject,
    mut v_00_u03c3_2153_: *mut LeanObject,
    mut v_00_u03b1_2154_: *mut LeanObject,
    mut v_m_2155_: *mut LeanObject,
    mut v_inst_2156_: *mut LeanObject,
    mut v_a_2157_: *mut LeanObject,
    mut v_s_2158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    v___x_2159_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2159_, 0, v_a_2157_);
    lean_ctor_set(v___x_2159_, 1, v_s_2158_);
    v___x_2160_ = lean_apply_2(v_inst_2156_, lean_box(0), v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg___lam__0(
    mut v_inst_2161_: *mut LeanObject,
    mut v_00_u03b1_2162_: *mut LeanObject,
    mut v___y_2163_: *mut LeanObject,
    mut v___y_2164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut LeanObject = core::ptr::null_mut();
    v___x_2165_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2165_, 0, v___y_2163_);
    lean_ctor_set(v___x_2165_, 1, v___y_2164_);
    v___x_2166_ = lean_apply_2(v_inst_2161_, lean_box(0), v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg(
    mut v_inst_2167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2168_: *mut LeanObject = core::ptr::null_mut();
    v___f_2168_ = lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2168_, 0, v_inst_2167_);
    return v___f_2168_;
}
pub unsafe fn l_Lake_EStateT_instPure(
    mut v_00_u03b5_2169_: *mut LeanObject,
    mut v_00_u03c3_2170_: *mut LeanObject,
    mut v_m_2171_: *mut LeanObject,
    mut v_inst_2172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2173_: *mut LeanObject = core::ptr::null_mut();
    v___f_2173_ = lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2173_, 0, v_inst_2172_);
    return v___f_2173_;
}
pub unsafe fn l_Lake_EStateT_map___redArg___lam__0(
    mut v_f_2174_: *mut LeanObject,
    mut v_x_2175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2175_) == 0 {
                    v_a_2176_ = lean_ctor_get(v_x_2175_, 0);
                    v_a_2177_ = lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2185_ = (!lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2185_ == 0 {
                        v___x_2179_ = v_x_2175_;
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2177_);
                        lean_inc(v_a_2176_);
                        lean_dec(v_x_2175_);
                        v___x_2179_ = lean_box(0);
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_f_2174_);
                    v_a_2186_ = lean_ctor_get(v_x_2175_, 0);
                    v_a_2187_ = lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2194_ = (!lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v_x_2175_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2187_);
                        lean_inc(v_a_2186_);
                        lean_dec(v_x_2175_);
                        v___x_2189_ = lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2181_ = lean_apply_1(v_f_2174_, v_a_2176_);
                if v_isShared_2180_ == 0 {
                    lean_ctor_set(v___x_2179_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_a_2177_);
                    v___x_2183_ = v_reuseFailAlloc_2184_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2183_;
            }
            3 => {
                if v_isShared_2190_ == 0 {
                    v___x_2192_ = v___x_2189_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2193_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2186_);
                    lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2187_);
                    v___x_2192_ = v_reuseFailAlloc_2193_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_map___redArg(
    mut v_inst_2195_: *mut LeanObject,
    mut v_f_2196_: *mut LeanObject,
    mut v_x_2197_: *mut LeanObject,
    mut v_s_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut LeanObject = core::ptr::null_mut();
    v_map_2199_ = lean_ctor_get(v_inst_2195_, 0);
    lean_inc(v_map_2199_);
    lean_dec_ref(v_inst_2195_);
    v___f_2200_ = lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2200_, 0, v_f_2196_);
    v___x_2201_ = lean_apply_1(v_x_2197_, v_s_2198_);
    v___x_2202_ = lean_apply_4(
        v_map_2199_,
        lean_box(0),
        lean_box(0),
        v___f_2200_,
        v___x_2201_,
    );
    return v___x_2202_;
}
pub unsafe fn l_Lake_EStateT_map(
    mut v_00_u03b5_2203_: *mut LeanObject,
    mut v_00_u03c3_2204_: *mut LeanObject,
    mut v_00_u03b1_2205_: *mut LeanObject,
    mut v_00_u03b2_2206_: *mut LeanObject,
    mut v_m_2207_: *mut LeanObject,
    mut v_inst_2208_: *mut LeanObject,
    mut v_f_2209_: *mut LeanObject,
    mut v_x_2210_: *mut LeanObject,
    mut v_s_2211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    v_map_2212_ = lean_ctor_get(v_inst_2208_, 0);
    lean_inc(v_map_2212_);
    lean_dec_ref(v_inst_2208_);
    v___f_2213_ = lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2213_, 0, v_f_2209_);
    v___x_2214_ = lean_apply_1(v_x_2210_, v_s_2211_);
    v___x_2215_ = lean_apply_4(
        v_map_2212_,
        lean_box(0),
        lean_box(0),
        v___f_2213_,
        v___x_2214_,
    );
    return v___x_2215_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__0(
    mut v___y_2216_: *mut LeanObject,
    mut v_x_2217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2217_) == 0 {
                    v_a_2218_ = lean_ctor_get(v_x_2217_, 0);
                    v_a_2219_ = lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2227_ = (!lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2227_ == 0 {
                        v___x_2221_ = v_x_2217_;
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2219_);
                        lean_inc(v_a_2218_);
                        lean_dec(v_x_2217_);
                        v___x_2221_ = lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___y_2216_);
                    v_a_2228_ = lean_ctor_get(v_x_2217_, 0);
                    v_a_2229_ = lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2236_ = (!lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v_x_2217_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2229_);
                        lean_inc(v_a_2228_);
                        lean_dec(v_x_2217_);
                        v___x_2231_ = lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2223_ = lean_apply_1(v___y_2216_, v_a_2218_);
                if v_isShared_2222_ == 0 {
                    lean_ctor_set(v___x_2221_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
                    lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_a_2219_);
                    v___x_2225_ = v_reuseFailAlloc_2226_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2225_;
            }
            3 => {
                if v_isShared_2232_ == 0 {
                    v___x_2234_ = v___x_2231_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2235_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2228_);
                    lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2229_);
                    v___x_2234_ = v_reuseFailAlloc_2235_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2234_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__1(
    mut v_inst_2237_: *mut LeanObject,
    mut v_00_u03b1_2238_: *mut LeanObject,
    mut v_00_u03b2_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    v_map_2243_ = lean_ctor_get(v_inst_2237_, 0);
    lean_inc(v_map_2243_);
    lean_dec_ref(v_inst_2237_);
    v___f_2244_ = lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2244_, 0, v___y_2240_);
    v___x_2245_ = lean_apply_1(v___y_2241_, v___y_2242_);
    v___x_2246_ = lean_apply_4(
        v_map_2243_,
        lean_box(0),
        lean_box(0),
        v___f_2244_,
        v___x_2245_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__2(
    mut v___f_2247_: *mut LeanObject,
    mut v_00_u03b1_2248_: *mut LeanObject,
    mut v_00_u03b2_2249_: *mut LeanObject,
    mut v___y_2250_: *mut LeanObject,
    mut v___y_2251_: *mut LeanObject,
    mut v___y_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    v___x_2253_ = lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___x_2253_, 0, lean_box(0));
    lean_closure_set(v___x_2253_, 1, lean_box(0));
    lean_closure_set(v___x_2253_, 2, v___y_2250_);
    v___x_2254_ = lean_apply_5(
        v___f_2247_,
        lean_box(0),
        lean_box(0),
        v___x_2253_,
        v___y_2251_,
        v___y_2252_,
    );
    return v___x_2254_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg(
    mut v_inst_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    v___f_2256_ = lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2256_, 0, v_inst_2255_);
    lean_inc_ref(v___f_2256_);
    v___f_2257_ = lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2257_, 0, v___f_2256_);
    v___x_2258_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2258_, 0, v___f_2256_);
    lean_ctor_set(v___x_2258_, 1, v___f_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lake_EStateT_instFunctor(
    mut v_00_u03b5_2259_: *mut LeanObject,
    mut v_00_u03c3_2260_: *mut LeanObject,
    mut v_m_2261_: *mut LeanObject,
    mut v_inst_2262_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lake_EStateT_instFunctor___redArg(v_inst_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lake_EStateT_bind___redArg___lam__0(
    mut v_f_2264_: *mut LeanObject,
    mut v_toPure_2265_: *mut LeanObject,
    mut v_____do__lift_2266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2266_) == 0 {
                    lean_dec(v_toPure_2265_);
                    v_a_2267_ = lean_ctor_get(v_____do__lift_2266_, 0);
                    lean_inc(v_a_2267_);
                    v_a_2268_ = lean_ctor_get(v_____do__lift_2266_, 1);
                    lean_inc(v_a_2268_);
                    lean_dec_ref_known(v_____do__lift_2266_, 2);
                    v___x_2269_ = lean_apply_2(v_f_2264_, v_a_2267_, v_a_2268_);
                    return v___x_2269_;
                } else {
                    lean_dec(v_f_2264_);
                    v_a_2270_ = lean_ctor_get(v_____do__lift_2266_, 0);
                    v_a_2271_ = lean_ctor_get(v_____do__lift_2266_, 1);
                    v_isSharedCheck_2279_ = (!lean_is_exclusive(v_____do__lift_2266_)) as u8;
                    if v_isSharedCheck_2279_ == 0 {
                        v___x_2273_ = v_____do__lift_2266_;
                        v_isShared_2274_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2271_);
                        lean_inc(v_a_2270_);
                        lean_dec(v_____do__lift_2266_);
                        v___x_2273_ = lean_box(0);
                        v_isShared_2274_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2274_ == 0 {
                    v___x_2276_ = v___x_2273_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2278_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2270_);
                    lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2277_ = lean_apply_2(v_toPure_2265_, lean_box(0), v___x_2276_);
                return v___x_2277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_bind___redArg(
    mut v_inst_2280_: *mut LeanObject,
    mut v_x_2281_: *mut LeanObject,
    mut v_f_2282_: *mut LeanObject,
    mut v_s_2283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2284_ = lean_ctor_get(v_inst_2280_, 0);
    lean_inc_ref(v_toApplicative_2284_);
    v_toBind_2285_ = lean_ctor_get(v_inst_2280_, 1);
    lean_inc(v_toBind_2285_);
    lean_dec_ref(v_inst_2280_);
    v_toPure_2286_ = lean_ctor_get(v_toApplicative_2284_, 1);
    lean_inc(v_toPure_2286_);
    lean_dec_ref(v_toApplicative_2284_);
    v___x_2287_ = lean_apply_1(v_x_2281_, v_s_2283_);
    v___f_2288_ = lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2288_, 0, v_f_2282_);
    lean_closure_set(v___f_2288_, 1, v_toPure_2286_);
    v___x_2289_ = lean_apply_4(
        v_toBind_2285_,
        lean_box(0),
        lean_box(0),
        v___x_2287_,
        v___f_2288_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Lake_EStateT_bind(
    mut v_00_u03b5_2290_: *mut LeanObject,
    mut v_00_u03c3_2291_: *mut LeanObject,
    mut v_00_u03b1_2292_: *mut LeanObject,
    mut v_00_u03b2_2293_: *mut LeanObject,
    mut v_m_2294_: *mut LeanObject,
    mut v_inst_2295_: *mut LeanObject,
    mut v_x_2296_: *mut LeanObject,
    mut v_f_2297_: *mut LeanObject,
    mut v_s_2298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2299_ = lean_ctor_get(v_inst_2295_, 0);
    lean_inc_ref(v_toApplicative_2299_);
    v_toBind_2300_ = lean_ctor_get(v_inst_2295_, 1);
    lean_inc(v_toBind_2300_);
    lean_dec_ref(v_inst_2295_);
    v_toPure_2301_ = lean_ctor_get(v_toApplicative_2299_, 1);
    lean_inc(v_toPure_2301_);
    lean_dec_ref(v_toApplicative_2299_);
    v___x_2302_ = lean_apply_1(v_x_2296_, v_s_2298_);
    v___f_2303_ = lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2303_, 0, v_f_2297_);
    lean_closure_set(v___f_2303_, 1, v_toPure_2301_);
    v___x_2304_ = lean_apply_4(
        v_toBind_2300_,
        lean_box(0),
        lean_box(0),
        v___x_2302_,
        v___f_2303_,
    );
    return v___x_2304_;
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg___lam__0(
    mut v_y_2305_: *mut LeanObject,
    mut v_toPure_2306_: *mut LeanObject,
    mut v_____do__lift_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2307_) == 0 {
                    lean_dec(v_toPure_2306_);
                    v_a_2308_ = lean_ctor_get(v_____do__lift_2307_, 1);
                    lean_inc(v_a_2308_);
                    lean_dec_ref_known(v_____do__lift_2307_, 2);
                    v___x_2309_ = lean_box(0);
                    v___x_2310_ = lean_apply_2(v_y_2305_, v___x_2309_, v_a_2308_);
                    return v___x_2310_;
                } else {
                    lean_dec(v_y_2305_);
                    v_a_2311_ = lean_ctor_get(v_____do__lift_2307_, 0);
                    v_a_2312_ = lean_ctor_get(v_____do__lift_2307_, 1);
                    v_isSharedCheck_2320_ = (!lean_is_exclusive(v_____do__lift_2307_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2314_ = v_____do__lift_2307_;
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2312_);
                        lean_inc(v_a_2311_);
                        lean_dec(v_____do__lift_2307_);
                        v___x_2314_ = lean_box(0);
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2315_ == 0 {
                    v___x_2317_ = v___x_2314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
                    lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2318_ = lean_apply_2(v_toPure_2306_, lean_box(0), v___x_2317_);
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg(
    mut v_inst_2321_: *mut LeanObject,
    mut v_x_2322_: *mut LeanObject,
    mut v_y_2323_: *mut LeanObject,
    mut v_s_2324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2325_ = lean_ctor_get(v_inst_2321_, 0);
    lean_inc_ref(v_toApplicative_2325_);
    v_toBind_2326_ = lean_ctor_get(v_inst_2321_, 1);
    lean_inc(v_toBind_2326_);
    lean_dec_ref(v_inst_2321_);
    v_toPure_2327_ = lean_ctor_get(v_toApplicative_2325_, 1);
    lean_inc(v_toPure_2327_);
    lean_dec_ref(v_toApplicative_2325_);
    v___x_2328_ = lean_apply_1(v_x_2322_, v_s_2324_);
    v___f_2329_ = lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2329_, 0, v_y_2323_);
    lean_closure_set(v___f_2329_, 1, v_toPure_2327_);
    v___x_2330_ = lean_apply_4(
        v_toBind_2326_,
        lean_box(0),
        lean_box(0),
        v___x_2328_,
        v___f_2329_,
    );
    return v___x_2330_;
}
pub unsafe fn l_Lake_EStateT_seqRight(
    mut v_00_u03b5_2331_: *mut LeanObject,
    mut v_00_u03c3_2332_: *mut LeanObject,
    mut v_00_u03b1_2333_: *mut LeanObject,
    mut v_00_u03b2_2334_: *mut LeanObject,
    mut v_m_2335_: *mut LeanObject,
    mut v_inst_2336_: *mut LeanObject,
    mut v_x_2337_: *mut LeanObject,
    mut v_y_2338_: *mut LeanObject,
    mut v_s_2339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2340_ = lean_ctor_get(v_inst_2336_, 0);
    lean_inc_ref(v_toApplicative_2340_);
    v_toBind_2341_ = lean_ctor_get(v_inst_2336_, 1);
    lean_inc(v_toBind_2341_);
    lean_dec_ref(v_inst_2336_);
    v_toPure_2342_ = lean_ctor_get(v_toApplicative_2340_, 1);
    lean_inc(v_toPure_2342_);
    lean_dec_ref(v_toApplicative_2340_);
    v___x_2343_ = lean_apply_1(v_x_2337_, v_s_2339_);
    v___f_2344_ = lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2344_, 0, v_y_2338_);
    lean_closure_set(v___f_2344_, 1, v_toPure_2342_);
    v___x_2345_ = lean_apply_4(
        v_toBind_2341_,
        lean_box(0),
        lean_box(0),
        v___x_2343_,
        v___f_2344_,
    );
    return v___x_2345_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__0(
    mut v___y_2346_: *mut LeanObject,
    mut v_toPure_2347_: *mut LeanObject,
    mut v_____do__lift_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2348_) == 0 {
                    lean_dec(v_toPure_2347_);
                    v_a_2349_ = lean_ctor_get(v_____do__lift_2348_, 0);
                    lean_inc(v_a_2349_);
                    v_a_2350_ = lean_ctor_get(v_____do__lift_2348_, 1);
                    lean_inc(v_a_2350_);
                    lean_dec_ref_known(v_____do__lift_2348_, 2);
                    v___x_2351_ = lean_apply_2(v___y_2346_, v_a_2349_, v_a_2350_);
                    return v___x_2351_;
                } else {
                    lean_dec(v___y_2346_);
                    v_a_2352_ = lean_ctor_get(v_____do__lift_2348_, 0);
                    v_a_2353_ = lean_ctor_get(v_____do__lift_2348_, 1);
                    v_isSharedCheck_2361_ = (!lean_is_exclusive(v_____do__lift_2348_)) as u8;
                    if v_isSharedCheck_2361_ == 0 {
                        v___x_2355_ = v_____do__lift_2348_;
                        v_isShared_2356_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2353_);
                        lean_inc(v_a_2352_);
                        lean_dec(v_____do__lift_2348_);
                        v___x_2355_ = lean_box(0);
                        v_isShared_2356_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2356_ == 0 {
                    v___x_2358_ = v___x_2355_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2352_);
                    lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = lean_apply_2(v_toPure_2347_, lean_box(0), v___x_2358_);
                return v___x_2359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__1(
    mut v_toPure_2362_: *mut LeanObject,
    mut v_toBind_2363_: *mut LeanObject,
    mut v_00_u03b1_2364_: *mut LeanObject,
    mut v_00_u03b2_2365_: *mut LeanObject,
    mut v___y_2366_: *mut LeanObject,
    mut v___y_2367_: *mut LeanObject,
    mut v___y_2368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut LeanObject = core::ptr::null_mut();
    v___x_2369_ = lean_apply_1(v___y_2366_, v___y_2368_);
    v___f_2370_ = lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2370_, 0, v___y_2367_);
    lean_closure_set(v___f_2370_, 1, v_toPure_2362_);
    v___x_2371_ = lean_apply_4(
        v_toBind_2363_,
        lean_box(0),
        lean_box(0),
        v___x_2369_,
        v___f_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__2(
    mut v___y_2372_: *mut LeanObject,
    mut v_toPure_2373_: *mut LeanObject,
    mut v_____do__lift_2374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2374_) == 0 {
                    lean_dec(v_toPure_2373_);
                    v_a_2375_ = lean_ctor_get(v_____do__lift_2374_, 1);
                    lean_inc(v_a_2375_);
                    lean_dec_ref_known(v_____do__lift_2374_, 2);
                    v___x_2376_ = lean_box(0);
                    v___x_2377_ = lean_apply_2(v___y_2372_, v___x_2376_, v_a_2375_);
                    return v___x_2377_;
                } else {
                    lean_dec(v___y_2372_);
                    v_a_2378_ = lean_ctor_get(v_____do__lift_2374_, 0);
                    v_a_2379_ = lean_ctor_get(v_____do__lift_2374_, 1);
                    v_isSharedCheck_2387_ = (!lean_is_exclusive(v_____do__lift_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2381_ = v_____do__lift_2374_;
                        v_isShared_2382_ = v_isSharedCheck_2387_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2379_);
                        lean_inc(v_a_2378_);
                        lean_dec(v_____do__lift_2374_);
                        v___x_2381_ = lean_box(0);
                        v_isShared_2382_ = v_isSharedCheck_2387_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2382_ == 0 {
                    v___x_2384_ = v___x_2381_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
                    lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2385_ = lean_apply_2(v_toPure_2373_, lean_box(0), v___x_2384_);
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__3(
    mut v_toPure_2388_: *mut LeanObject,
    mut v_toBind_2389_: *mut LeanObject,
    mut v_00_u03b1_2390_: *mut LeanObject,
    mut v_00_u03b2_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
    mut v___y_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2395_ = lean_apply_1(v___y_2392_, v___y_2394_);
    v___f_2396_ = lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2396_, 0, v___y_2393_);
    lean_closure_set(v___f_2396_, 1, v_toPure_2388_);
    v___x_2397_ = lean_apply_4(
        v_toBind_2389_,
        lean_box(0),
        lean_box(0),
        v___x_2395_,
        v___f_2396_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6(
    mut v_a_2398_: *mut LeanObject,
    mut v_toPure_2399_: *mut LeanObject,
    mut v_x_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut LeanObject = core::ptr::null_mut();
    v___x_2402_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2402_, 0, v_a_2398_);
    lean_ctor_set(v___x_2402_, 1, v___y_2401_);
    v___x_2403_ = lean_apply_2(v_toPure_2399_, lean_box(0), v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6___boxed(
    mut v_a_2404_: *mut LeanObject,
    mut v_toPure_2405_: *mut LeanObject,
    mut v_x_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2408_: *mut LeanObject = core::ptr::null_mut();
    v_res_2408_ = l_Lake_EStateT_instMonad___redArg___lam__6(
        v_a_2404_,
        v_toPure_2405_,
        v_x_2406_,
        v___y_2407_,
    );
    lean_dec(v_x_2406_);
    return v_res_2408_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__4(
    mut v_toPure_2409_: *mut LeanObject,
    mut v_y_2410_: *mut LeanObject,
    mut v___f_2411_: *mut LeanObject,
    mut v_a_2412_: *mut LeanObject,
    mut v___y_2413_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    v___f_2414_ = lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    lean_closure_set(v___f_2414_, 0, v_a_2412_);
    lean_closure_set(v___f_2414_, 1, v_toPure_2409_);
    v___x_2415_ = lean_box(0);
    v___x_2416_ = lean_apply_1(v_y_2410_, v___x_2415_);
    v___x_2417_ = lean_apply_5(
        v___f_2411_,
        lean_box(0),
        lean_box(0),
        v___x_2416_,
        v___f_2414_,
        v___y_2413_,
    );
    return v___x_2417_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__5(
    mut v_toPure_2418_: *mut LeanObject,
    mut v___f_2419_: *mut LeanObject,
    mut v_00_u03b1_2420_: *mut LeanObject,
    mut v_00_u03b2_2421_: *mut LeanObject,
    mut v_x_2422_: *mut LeanObject,
    mut v_y_2423_: *mut LeanObject,
    mut v___y_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v___f_2419_);
    v___f_2425_ = lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        3,
    );
    lean_closure_set(v___f_2425_, 0, v_toPure_2418_);
    lean_closure_set(v___f_2425_, 1, v_y_2423_);
    lean_closure_set(v___f_2425_, 2, v___f_2419_);
    v___x_2426_ = lean_apply_5(
        v___f_2419_,
        lean_box(0),
        lean_box(0),
        v_x_2422_,
        v___f_2425_,
        v___y_2424_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__7(
    mut v_a_2427_: *mut LeanObject,
    mut v_x_2428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut v_a_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2428_) == 0 {
                    v_a_2429_ = lean_ctor_get(v_x_2428_, 0);
                    v_a_2430_ = lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2438_ = (!lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2438_ == 0 {
                        v___x_2432_ = v_x_2428_;
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2430_);
                        lean_inc(v_a_2429_);
                        lean_dec(v_x_2428_);
                        v___x_2432_ = lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2427_);
                    v_a_2439_ = lean_ctor_get(v_x_2428_, 0);
                    v_a_2440_ = lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2447_ = (!lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2447_ == 0 {
                        v___x_2442_ = v_x_2428_;
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2440_);
                        lean_inc(v_a_2439_);
                        lean_dec(v_x_2428_);
                        v___x_2442_ = lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2434_ = lean_apply_1(v_a_2427_, v_a_2429_);
                if v_isShared_2433_ == 0 {
                    lean_ctor_set(v___x_2432_, 0, v___x_2434_);
                    v___x_2436_ = v___x_2432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
                    lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2430_);
                    v___x_2436_ = v_reuseFailAlloc_2437_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2436_;
            }
            3 => {
                if v_isShared_2443_ == 0 {
                    v___x_2445_ = v___x_2442_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2446_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2439_);
                    lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2440_);
                    v___x_2445_ = v_reuseFailAlloc_2446_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2445_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__8(
    mut v_toFunctor_2448_: *mut LeanObject,
    mut v_x_2449_: *mut LeanObject,
    mut v_toPure_2450_: *mut LeanObject,
    mut v_____do__lift_2451_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_map_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2451_) == 0 {
                    lean_dec(v_toPure_2450_);
                    v_a_2452_ = lean_ctor_get(v_____do__lift_2451_, 0);
                    lean_inc(v_a_2452_);
                    v_a_2453_ = lean_ctor_get(v_____do__lift_2451_, 1);
                    lean_inc(v_a_2453_);
                    lean_dec_ref_known(v_____do__lift_2451_, 2);
                    v_map_2454_ = lean_ctor_get(v_toFunctor_2448_, 0);
                    lean_inc(v_map_2454_);
                    lean_dec_ref(v_toFunctor_2448_);
                    v___f_2455_ = lean_alloc_closure(
                        l_Lake_EStateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    lean_closure_set(v___f_2455_, 0, v_a_2452_);
                    v___x_2456_ = lean_box(0);
                    v___x_2457_ = lean_apply_2(v_x_2449_, v___x_2456_, v_a_2453_);
                    v___x_2458_ = lean_apply_4(
                        v_map_2454_,
                        lean_box(0),
                        lean_box(0),
                        v___f_2455_,
                        v___x_2457_,
                    );
                    return v___x_2458_;
                } else {
                    lean_dec(v_x_2449_);
                    lean_dec_ref(v_toFunctor_2448_);
                    v_a_2459_ = lean_ctor_get(v_____do__lift_2451_, 0);
                    v_a_2460_ = lean_ctor_get(v_____do__lift_2451_, 1);
                    v_isSharedCheck_2468_ = (!lean_is_exclusive(v_____do__lift_2451_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2462_ = v_____do__lift_2451_;
                        v_isShared_2463_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2460_);
                        lean_inc(v_a_2459_);
                        lean_dec(v_____do__lift_2451_);
                        v___x_2462_ = lean_box(0);
                        v_isShared_2463_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2459_);
                    lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2466_ = lean_apply_2(v_toPure_2450_, lean_box(0), v___x_2465_);
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__9(
    mut v_toFunctor_2469_: *mut LeanObject,
    mut v_toPure_2470_: *mut LeanObject,
    mut v_toBind_2471_: *mut LeanObject,
    mut v_00_u03b1_2472_: *mut LeanObject,
    mut v_00_u03b2_2473_: *mut LeanObject,
    mut v_f_2474_: *mut LeanObject,
    mut v_x_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    v___f_2477_ = lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2477_, 0, v_toFunctor_2469_);
    lean_closure_set(v___f_2477_, 1, v_x_2475_);
    lean_closure_set(v___f_2477_, 2, v_toPure_2470_);
    v___x_2478_ = lean_apply_1(v_f_2474_, v___y_2476_);
    v___x_2479_ = lean_apply_4(
        v_toBind_2471_,
        lean_box(0),
        lean_box(0),
        v___x_2478_,
        v___f_2477_,
    );
    return v___x_2479_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg(
    mut v_inst_2480_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v_toFunctor_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___f_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_unused_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2481_ = lean_ctor_get(v_inst_2480_, 0);
                v_toBind_2482_ = lean_ctor_get(v_inst_2480_, 1);
                v_isSharedCheck_2507_ = (!lean_is_exclusive(v_inst_2480_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v___x_2484_ = v_inst_2480_;
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_2482_);
                    lean_inc(v_toApplicative_2481_);
                    lean_dec(v_inst_2480_);
                    v___x_2484_ = lean_box(0);
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2486_ = lean_ctor_get(v_toApplicative_2481_, 0);
                v_toPure_2487_ = lean_ctor_get(v_toApplicative_2481_, 1);
                v_isSharedCheck_2503_ = (!lean_is_exclusive(v_toApplicative_2481_)) as u8;
                if v_isSharedCheck_2503_ == 0 {
                    v_unused_2504_ = lean_ctor_get(v_toApplicative_2481_, 4);
                    lean_dec(v_unused_2504_);
                    v_unused_2505_ = lean_ctor_get(v_toApplicative_2481_, 3);
                    lean_dec(v_unused_2505_);
                    v_unused_2506_ = lean_ctor_get(v_toApplicative_2481_, 2);
                    lean_dec(v_unused_2506_);
                    v___x_2489_ = v_toApplicative_2481_;
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toPure_2487_);
                    lean_inc(v_toFunctor_2486_);
                    lean_dec(v_toApplicative_2481_);
                    v___x_2489_ = lean_box(0);
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_toBind_2482_, 2);
                lean_inc_n(v_toPure_2487_, 4);
                v___f_2491_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2491_, 0, v_toPure_2487_);
                lean_closure_set(v___f_2491_, 1, v_toBind_2482_);
                v___f_2492_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2492_, 0, v_toPure_2487_);
                lean_closure_set(v___f_2492_, 1, v_toBind_2482_);
                lean_inc_ref(v___f_2491_);
                v___f_2493_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2493_, 0, v_toPure_2487_);
                lean_closure_set(v___f_2493_, 1, v___f_2491_);
                lean_inc_ref(v_toFunctor_2486_);
                v___f_2494_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___f_2494_, 0, v_toFunctor_2486_);
                lean_closure_set(v___f_2494_, 1, v_toPure_2487_);
                lean_closure_set(v___f_2494_, 2, v_toBind_2482_);
                v___x_2495_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2486_);
                v___f_2496_ = lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_2496_, 0, v_toPure_2487_);
                if v_isShared_2490_ == 0 {
                    lean_ctor_set(v___x_2489_, 4, v___f_2492_);
                    lean_ctor_set(v___x_2489_, 3, v___f_2493_);
                    lean_ctor_set(v___x_2489_, 2, v___f_2494_);
                    lean_ctor_set(v___x_2489_, 1, v___f_2496_);
                    lean_ctor_set(v___x_2489_, 0, v___x_2495_);
                    v___x_2498_ = v___x_2489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2495_);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___f_2496_);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___f_2494_);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___f_2493_);
                    lean_ctor_set(v_reuseFailAlloc_2502_, 4, v___f_2492_);
                    v___x_2498_ = v_reuseFailAlloc_2502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2485_ == 0 {
                    lean_ctor_set(v___x_2484_, 1, v___f_2491_);
                    lean_ctor_set(v___x_2484_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
                    lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___f_2491_);
                    v___x_2500_ = v_reuseFailAlloc_2501_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2500_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad(
    mut v_00_u03b5_2508_: *mut LeanObject,
    mut v_00_u03c3_2509_: *mut LeanObject,
    mut v_m_2510_: *mut LeanObject,
    mut v_inst_2511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_toFunctor_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___f_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2512_ = lean_ctor_get(v_inst_2511_, 0);
                v_toBind_2513_ = lean_ctor_get(v_inst_2511_, 1);
                v_isSharedCheck_2538_ = (!lean_is_exclusive(v_inst_2511_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v___x_2515_ = v_inst_2511_;
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_2513_);
                    lean_inc(v_toApplicative_2512_);
                    lean_dec(v_inst_2511_);
                    v___x_2515_ = lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2517_ = lean_ctor_get(v_toApplicative_2512_, 0);
                v_toPure_2518_ = lean_ctor_get(v_toApplicative_2512_, 1);
                v_isSharedCheck_2534_ = (!lean_is_exclusive(v_toApplicative_2512_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v_unused_2535_ = lean_ctor_get(v_toApplicative_2512_, 4);
                    lean_dec(v_unused_2535_);
                    v_unused_2536_ = lean_ctor_get(v_toApplicative_2512_, 3);
                    lean_dec(v_unused_2536_);
                    v_unused_2537_ = lean_ctor_get(v_toApplicative_2512_, 2);
                    lean_dec(v_unused_2537_);
                    v___x_2520_ = v_toApplicative_2512_;
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_toPure_2518_);
                    lean_inc(v_toFunctor_2517_);
                    lean_dec(v_toApplicative_2512_);
                    v___x_2520_ = lean_box(0);
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc_n(v_toBind_2513_, 2);
                lean_inc_n(v_toPure_2518_, 4);
                v___f_2522_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2522_, 0, v_toPure_2518_);
                lean_closure_set(v___f_2522_, 1, v_toBind_2513_);
                v___f_2523_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2523_, 0, v_toPure_2518_);
                lean_closure_set(v___f_2523_, 1, v_toBind_2513_);
                lean_inc_ref(v___f_2522_);
                v___f_2524_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                lean_closure_set(v___f_2524_, 0, v_toPure_2518_);
                lean_closure_set(v___f_2524_, 1, v___f_2522_);
                lean_inc_ref(v_toFunctor_2517_);
                v___f_2525_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                lean_closure_set(v___f_2525_, 0, v_toFunctor_2517_);
                lean_closure_set(v___f_2525_, 1, v_toPure_2518_);
                lean_closure_set(v___f_2525_, 2, v_toBind_2513_);
                v___x_2526_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2517_);
                v___f_2527_ = lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_2527_, 0, v_toPure_2518_);
                if v_isShared_2521_ == 0 {
                    lean_ctor_set(v___x_2520_, 4, v___f_2523_);
                    lean_ctor_set(v___x_2520_, 3, v___f_2524_);
                    lean_ctor_set(v___x_2520_, 2, v___f_2525_);
                    lean_ctor_set(v___x_2520_, 1, v___f_2527_);
                    lean_ctor_set(v___x_2520_, 0, v___x_2526_);
                    v___x_2529_ = v___x_2520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = lean_alloc_ctor(0, 5, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2526_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___f_2527_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___f_2525_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___f_2524_);
                    lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___f_2523_);
                    v___x_2529_ = v_reuseFailAlloc_2533_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2516_ == 0 {
                    lean_ctor_set(v___x_2515_, 1, v___f_2522_);
                    lean_ctor_set(v___x_2515_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___f_2522_);
                    v___x_2531_ = v_reuseFailAlloc_2532_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2531_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_set___redArg(
    mut v_inst_2539_: *mut LeanObject,
    mut v_s_2540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    v___x_2541_ = lean_box(0);
    v___x_2542_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    lean_ctor_set(v___x_2542_, 1, v_s_2540_);
    v___x_2543_ = lean_apply_2(v_inst_2539_, lean_box(0), v___x_2542_);
    return v___x_2543_;
}
pub unsafe fn l_Lake_EStateT_set(
    mut v_00_u03b5_2544_: *mut LeanObject,
    mut v_00_u03c3_2545_: *mut LeanObject,
    mut v_m_2546_: *mut LeanObject,
    mut v_inst_2547_: *mut LeanObject,
    mut v_s_2548_: *mut LeanObject,
    mut v_x_2549_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2550_ = lean_box(0);
    v___x_2551_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    lean_ctor_set(v___x_2551_, 1, v_s_2548_);
    v___x_2552_ = lean_apply_2(v_inst_2547_, lean_box(0), v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lake_EStateT_set___boxed(
    mut v_00_u03b5_2553_: *mut LeanObject,
    mut v_00_u03c3_2554_: *mut LeanObject,
    mut v_m_2555_: *mut LeanObject,
    mut v_inst_2556_: *mut LeanObject,
    mut v_s_2557_: *mut LeanObject,
    mut v_x_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2559_: *mut LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lake_EStateT_set(
        v_00_u03b5_2553_,
        v_00_u03c3_2554_,
        v_m_2555_,
        v_inst_2556_,
        v_s_2557_,
        v_x_2558_,
    );
    lean_dec(v_x_2558_);
    return v_res_2559_;
}
pub unsafe fn l_Lake_EStateT_get___redArg(
    mut v_inst_2560_: *mut LeanObject,
    mut v_s_2561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_2561_);
    v___x_2562_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2562_, 0, v_s_2561_);
    lean_ctor_set(v___x_2562_, 1, v_s_2561_);
    v___x_2563_ = lean_apply_2(v_inst_2560_, lean_box(0), v___x_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Lake_EStateT_get(
    mut v_00_u03b5_2564_: *mut LeanObject,
    mut v_00_u03c3_2565_: *mut LeanObject,
    mut v_m_2566_: *mut LeanObject,
    mut v_inst_2567_: *mut LeanObject,
    mut v_s_2568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_s_2568_);
    v___x_2569_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2569_, 0, v_s_2568_);
    lean_ctor_set(v___x_2569_, 1, v_s_2568_);
    v___x_2570_ = lean_apply_2(v_inst_2567_, lean_box(0), v___x_2569_);
    return v___x_2570_;
}
pub unsafe fn l_Lake_EStateT_modifyGet___redArg(
    mut v_inst_2571_: *mut LeanObject,
    mut v_f_2572_: *mut LeanObject,
    mut v_s_2573_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2574_ = lean_apply_1(v_f_2572_, v_s_2573_);
                v_fst_2575_ = lean_ctor_get(v___x_2574_, 0);
                v_snd_2576_ = lean_ctor_get(v___x_2574_, 1);
                v_isSharedCheck_2584_ = (!lean_is_exclusive(v___x_2574_)) as u8;
                if v_isSharedCheck_2584_ == 0 {
                    v___x_2578_ = v___x_2574_;
                    v_isShared_2579_ = v_isSharedCheck_2584_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2576_);
                    lean_inc(v_fst_2575_);
                    lean_dec(v___x_2574_);
                    v___x_2578_ = lean_box(0);
                    v_isShared_2579_ = v_isSharedCheck_2584_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2579_ == 0 {
                    v___x_2581_ = v___x_2578_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_fst_2575_);
                    lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_snd_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2582_ = lean_apply_2(v_inst_2571_, lean_box(0), v___x_2581_);
                return v___x_2582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_modifyGet(
    mut v_00_u03b5_2585_: *mut LeanObject,
    mut v_00_u03c3_2586_: *mut LeanObject,
    mut v_00_u03b1_2587_: *mut LeanObject,
    mut v_m_2588_: *mut LeanObject,
    mut v_inst_2589_: *mut LeanObject,
    mut v_f_2590_: *mut LeanObject,
    mut v_s_2591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2592_ = lean_apply_1(v_f_2590_, v_s_2591_);
                v_fst_2593_ = lean_ctor_get(v___x_2592_, 0);
                v_snd_2594_ = lean_ctor_get(v___x_2592_, 1);
                v_isSharedCheck_2602_ = (!lean_is_exclusive(v___x_2592_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v___x_2596_ = v___x_2592_;
                    v_isShared_2597_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2594_);
                    lean_inc(v_fst_2593_);
                    lean_dec(v___x_2592_);
                    v___x_2596_ = lean_box(0);
                    v_isShared_2597_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2597_ == 0 {
                    v___x_2599_ = v___x_2596_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2601_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_fst_2593_);
                    lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_snd_2594_);
                    v___x_2599_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2600_ = lean_apply_2(v_inst_2589_, lean_box(0), v___x_2599_);
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(
    mut v_inst_2603_: *mut LeanObject,
    mut v_00_u03b1_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = lean_apply_1(v___y_2605_, v___y_2606_);
                v_fst_2608_ = lean_ctor_get(v___x_2607_, 0);
                v_snd_2609_ = lean_ctor_get(v___x_2607_, 1);
                v_isSharedCheck_2617_ = (!lean_is_exclusive(v___x_2607_)) as u8;
                if v_isSharedCheck_2617_ == 0 {
                    v___x_2611_ = v___x_2607_;
                    v_isShared_2612_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2609_);
                    lean_inc(v_fst_2608_);
                    lean_dec(v___x_2607_);
                    v___x_2611_ = lean_box(0);
                    v_isShared_2612_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_2612_ == 0 {
                    v___x_2614_ = v___x_2611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2616_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2608_);
                    lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_snd_2609_);
                    v___x_2614_ = v_reuseFailAlloc_2616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2615_ = lean_apply_2(v_inst_2603_, lean_box(0), v___x_2614_);
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg(
    mut v_inst_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_n(v_inst_2618_, 2);
    v___f_2619_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2619_, 0, v_inst_2618_);
    v___x_2620_ = lean_alloc_closure(l_Lake_EStateT_get as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___x_2620_, 0, lean_box(0));
    lean_closure_set(v___x_2620_, 1, lean_box(0));
    lean_closure_set(v___x_2620_, 2, lean_box(0));
    lean_closure_set(v___x_2620_, 3, v_inst_2618_);
    v___x_2621_ = lean_alloc_closure(l_Lake_EStateT_set___boxed as *mut core::ffi::c_void, 6, 4);
    lean_closure_set(v___x_2621_, 0, lean_box(0));
    lean_closure_set(v___x_2621_, 1, lean_box(0));
    lean_closure_set(v___x_2621_, 2, lean_box(0));
    lean_closure_set(v___x_2621_, 3, v_inst_2618_);
    v___x_2622_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_2622_, 0, v___x_2620_);
    lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    lean_ctor_set(v___x_2622_, 2, v___f_2619_);
    return v___x_2622_;
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure(
    mut v_00_u03b5_2623_: *mut LeanObject,
    mut v_00_u03c3_2624_: *mut LeanObject,
    mut v_m_2625_: *mut LeanObject,
    mut v_inst_2626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2627_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Lake_EStateT_throw___redArg(
    mut v_inst_2628_: *mut LeanObject,
    mut v_e_2629_: *mut LeanObject,
    mut v_s_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    v___x_2631_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2631_, 0, v_e_2629_);
    lean_ctor_set(v___x_2631_, 1, v_s_2630_);
    v___x_2632_ = lean_apply_2(v_inst_2628_, lean_box(0), v___x_2631_);
    return v___x_2632_;
}
pub unsafe fn l_Lake_EStateT_throw(
    mut v_00_u03b5_2633_: *mut LeanObject,
    mut v_00_u03c3_2634_: *mut LeanObject,
    mut v_00_u03b1_2635_: *mut LeanObject,
    mut v_m_2636_: *mut LeanObject,
    mut v_inst_2637_: *mut LeanObject,
    mut v_e_2638_: *mut LeanObject,
    mut v_s_2639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut LeanObject = core::ptr::null_mut();
    v___x_2640_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2640_, 0, v_e_2638_);
    lean_ctor_set(v___x_2640_, 1, v_s_2639_);
    v___x_2641_ = lean_apply_2(v_inst_2637_, lean_box(0), v___x_2640_);
    return v___x_2641_;
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg___lam__0(
    mut v_toPure_2642_: *mut LeanObject,
    mut v_handle_2643_: *mut LeanObject,
    mut v_____do__lift_2644_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2644_) == 0 {
        let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_handle_2643_);
        v___x_2645_ = lean_apply_2(v_toPure_2642_, lean_box(0), v_____do__lift_2644_);
        return v___x_2645_;
    } else {
        let mut v_a_2646_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2647_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2642_);
        v_a_2646_ = lean_ctor_get(v_____do__lift_2644_, 0);
        lean_inc(v_a_2646_);
        v_a_2647_ = lean_ctor_get(v_____do__lift_2644_, 1);
        lean_inc(v_a_2647_);
        lean_dec_ref_known(v_____do__lift_2644_, 2);
        v___x_2648_ = lean_apply_2(v_handle_2643_, v_a_2646_, v_a_2647_);
        return v___x_2648_;
    }
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg(
    mut v_inst_2649_: *mut LeanObject,
    mut v_x_2650_: *mut LeanObject,
    mut v_handle_2651_: *mut LeanObject,
    mut v_s_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2653_ = lean_ctor_get(v_inst_2649_, 0);
    lean_inc_ref(v_toApplicative_2653_);
    v_toBind_2654_ = lean_ctor_get(v_inst_2649_, 1);
    lean_inc(v_toBind_2654_);
    lean_dec_ref(v_inst_2649_);
    v_toPure_2655_ = lean_ctor_get(v_toApplicative_2653_, 1);
    lean_inc(v_toPure_2655_);
    lean_dec_ref(v_toApplicative_2653_);
    v___x_2656_ = lean_apply_1(v_x_2650_, v_s_2652_);
    v___f_2657_ = lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2657_, 0, v_toPure_2655_);
    lean_closure_set(v___f_2657_, 1, v_handle_2651_);
    v___x_2658_ = lean_apply_4(
        v_toBind_2654_,
        lean_box(0),
        lean_box(0),
        v___x_2656_,
        v___f_2657_,
    );
    return v___x_2658_;
}
pub unsafe fn l_Lake_EStateT_tryCatch(
    mut v_00_u03b5_2659_: *mut LeanObject,
    mut v_00_u03c3_2660_: *mut LeanObject,
    mut v_00_u03b1_2661_: *mut LeanObject,
    mut v_m_2662_: *mut LeanObject,
    mut v_inst_2663_: *mut LeanObject,
    mut v_x_2664_: *mut LeanObject,
    mut v_handle_2665_: *mut LeanObject,
    mut v_s_2666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2667_ = lean_ctor_get(v_inst_2663_, 0);
    lean_inc_ref(v_toApplicative_2667_);
    v_toBind_2668_ = lean_ctor_get(v_inst_2663_, 1);
    lean_inc(v_toBind_2668_);
    lean_dec_ref(v_inst_2663_);
    v_toPure_2669_ = lean_ctor_get(v_toApplicative_2667_, 1);
    lean_inc(v_toPure_2669_);
    lean_dec_ref(v_toApplicative_2667_);
    v___x_2670_ = lean_apply_1(v_x_2664_, v_s_2666_);
    v___f_2671_ = lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2671_, 0, v_toPure_2669_);
    lean_closure_set(v___f_2671_, 1, v_handle_2665_);
    v___x_2672_ = lean_apply_4(
        v_toBind_2668_,
        lean_box(0),
        lean_box(0),
        v___x_2670_,
        v___f_2671_,
    );
    return v___x_2672_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(
    mut v_toPure_2673_: *mut LeanObject,
    mut v___y_2674_: *mut LeanObject,
    mut v_____do__lift_2675_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2675_) == 0 {
        let mut v___x_2676_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___y_2674_);
        v___x_2676_ = lean_apply_2(v_toPure_2673_, lean_box(0), v_____do__lift_2675_);
        return v___x_2676_;
    } else {
        let mut v_a_2677_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2678_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2673_);
        v_a_2677_ = lean_ctor_get(v_____do__lift_2675_, 0);
        lean_inc(v_a_2677_);
        v_a_2678_ = lean_ctor_get(v_____do__lift_2675_, 1);
        lean_inc(v_a_2678_);
        lean_dec_ref_known(v_____do__lift_2675_, 2);
        v___x_2679_ = lean_apply_2(v___y_2674_, v_a_2677_, v_a_2678_);
        return v___x_2679_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(
    mut v_toPure_2680_: *mut LeanObject,
    mut v_toBind_2681_: *mut LeanObject,
    mut v_00_u03b1_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    v___x_2686_ = lean_apply_1(v___y_2683_, v___y_2685_);
    v___f_2687_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2687_, 0, v_toPure_2680_);
    lean_closure_set(v___f_2687_, 1, v___y_2684_);
    v___x_2688_ = lean_apply_4(
        v_toBind_2681_,
        lean_box(0),
        lean_box(0),
        v___x_2686_,
        v___f_2687_,
    );
    return v___x_2688_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(
    mut v_toPure_2689_: *mut LeanObject,
    mut v_00_u03b1_2690_: *mut LeanObject,
    mut v___y_2691_: *mut LeanObject,
    mut v___y_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v___x_2693_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_2693_, 0, v___y_2691_);
    lean_ctor_set(v___x_2693_, 1, v___y_2692_);
    v___x_2694_ = lean_apply_2(v_toPure_2689_, lean_box(0), v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(
    mut v_inst_2695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v_toPure_2701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2696_ = lean_ctor_get(v_inst_2695_, 0);
                v_toBind_2697_ = lean_ctor_get(v_inst_2695_, 1);
                v_isSharedCheck_2707_ = (!lean_is_exclusive(v_inst_2695_)) as u8;
                if v_isSharedCheck_2707_ == 0 {
                    v___x_2699_ = v_inst_2695_;
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_2697_);
                    lean_inc(v_toApplicative_2696_);
                    lean_dec(v_inst_2695_);
                    v___x_2699_ = lean_box(0);
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_2701_ = lean_ctor_get(v_toApplicative_2696_, 1);
                lean_inc_n(v_toPure_2701_, 2);
                lean_dec_ref(v_toApplicative_2696_);
                v___f_2702_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    2,
                );
                lean_closure_set(v___f_2702_, 0, v_toPure_2701_);
                lean_closure_set(v___f_2702_, 1, v_toBind_2697_);
                v___f_2703_ = lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                lean_closure_set(v___f_2703_, 0, v_toPure_2701_);
                if v_isShared_2700_ == 0 {
                    lean_ctor_set(v___x_2699_, 1, v___f_2702_);
                    lean_ctor_set(v___x_2699_, 0, v___f_2703_);
                    v___x_2705_ = v___x_2699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___f_2703_);
                    lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___f_2702_);
                    v___x_2705_ = v_reuseFailAlloc_2706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad(
    mut v_00_u03b5_2708_: *mut LeanObject,
    mut v_00_u03c3_2709_: *mut LeanObject,
    mut v_m_2710_: *mut LeanObject,
    mut v_inst_2711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    v___x_2712_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_2711_);
    return v___x_2712_;
}
pub unsafe fn l_Lake_EStateT_orElse___redArg___lam__0(
    mut v_toPure_2713_: *mut LeanObject,
    mut v_x_u2082_2714_: *mut LeanObject,
    mut v_____do__lift_2715_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2715_) == 0 {
        let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_u2082_2714_);
        v___x_2716_ = lean_apply_2(v_toPure_2713_, lean_box(0), v_____do__lift_2715_);
        return v___x_2716_;
    } else {
        let mut v_a_2717_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_2713_);
        v_a_2717_ = lean_ctor_get(v_____do__lift_2715_, 1);
        lean_inc(v_a_2717_);
        lean_dec_ref_known(v_____do__lift_2715_, 2);
        v___x_2718_ = lean_box(0);
        v___x_2719_ = lean_apply_2(v_x_u2082_2714_, v___x_2718_, v_a_2717_);
        return v___x_2719_;
    }
}
pub unsafe fn l_Lake_EStateT_orElse___redArg(
    mut v_inst_2720_: *mut LeanObject,
    mut v_x_u2081_2721_: *mut LeanObject,
    mut v_x_u2082_2722_: *mut LeanObject,
    mut v_s_2723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2724_ = lean_ctor_get(v_inst_2720_, 0);
    lean_inc_ref(v_toApplicative_2724_);
    v_toBind_2725_ = lean_ctor_get(v_inst_2720_, 1);
    lean_inc(v_toBind_2725_);
    lean_dec_ref(v_inst_2720_);
    v_toPure_2726_ = lean_ctor_get(v_toApplicative_2724_, 1);
    lean_inc(v_toPure_2726_);
    lean_dec_ref(v_toApplicative_2724_);
    v___x_2727_ = lean_apply_1(v_x_u2081_2721_, v_s_2723_);
    v___f_2728_ = lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2728_, 0, v_toPure_2726_);
    lean_closure_set(v___f_2728_, 1, v_x_u2082_2722_);
    v___x_2729_ = lean_apply_4(
        v_toBind_2725_,
        lean_box(0),
        lean_box(0),
        v___x_2727_,
        v___f_2728_,
    );
    return v___x_2729_;
}
pub unsafe fn l_Lake_EStateT_orElse(
    mut v_00_u03b5_2730_: *mut LeanObject,
    mut v_00_u03c3_2731_: *mut LeanObject,
    mut v_00_u03b1_2732_: *mut LeanObject,
    mut v_m_2733_: *mut LeanObject,
    mut v_inst_2734_: *mut LeanObject,
    mut v_x_u2081_2735_: *mut LeanObject,
    mut v_x_u2082_2736_: *mut LeanObject,
    mut v_s_2737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2738_ = lean_ctor_get(v_inst_2734_, 0);
    lean_inc_ref(v_toApplicative_2738_);
    v_toBind_2739_ = lean_ctor_get(v_inst_2734_, 1);
    lean_inc(v_toBind_2739_);
    lean_dec_ref(v_inst_2734_);
    v_toPure_2740_ = lean_ctor_get(v_toApplicative_2738_, 1);
    lean_inc(v_toPure_2740_);
    lean_dec_ref(v_toApplicative_2738_);
    v___x_2741_ = lean_apply_1(v_x_u2081_2735_, v_s_2737_);
    v___f_2742_ = lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2742_, 0, v_toPure_2740_);
    lean_closure_set(v___f_2742_, 1, v_x_u2082_2736_);
    v___x_2743_ = lean_apply_4(
        v_toBind_2739_,
        lean_box(0),
        lean_box(0),
        v___x_2741_,
        v___f_2742_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad___redArg(
    mut v_inst_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2745_: *mut LeanObject = core::ptr::null_mut();
    v___x_2745_ = lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___x_2745_, 0, lean_box(0));
    lean_closure_set(v___x_2745_, 1, lean_box(0));
    lean_closure_set(v___x_2745_, 2, lean_box(0));
    lean_closure_set(v___x_2745_, 3, lean_box(0));
    lean_closure_set(v___x_2745_, 4, v_inst_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad(
    mut v_00_u03b5_2746_: *mut LeanObject,
    mut v_00_u03c3_2747_: *mut LeanObject,
    mut v_00_u03b1_2748_: *mut LeanObject,
    mut v_m_2749_: *mut LeanObject,
    mut v_inst_2750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    v___x_2751_ = lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    lean_closure_set(v___x_2751_, 0, lean_box(0));
    lean_closure_set(v___x_2751_, 1, lean_box(0));
    lean_closure_set(v___x_2751_, 2, lean_box(0));
    lean_closure_set(v___x_2751_, 3, lean_box(0));
    lean_closure_set(v___x_2751_, 4, v_inst_2750_);
    return v___x_2751_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept___redArg___lam__0(
    mut v_f_2752_: *mut LeanObject,
    mut v_x_2753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2753_) == 0 {
                    lean_dec(v_f_2752_);
                    v_a_2754_ = lean_ctor_get(v_x_2753_, 0);
                    v_a_2755_ = lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2762_ = (!lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v_x_2753_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2755_);
                        lean_inc(v_a_2754_);
                        lean_dec(v_x_2753_);
                        v___x_2757_ = lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2763_ = lean_ctor_get(v_x_2753_, 0);
                    v_a_2764_ = lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2772_ = (!lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2772_ == 0 {
                        v___x_2766_ = v_x_2753_;
                        v_isShared_2767_ = v_isSharedCheck_2772_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2764_);
                        lean_inc(v_a_2763_);
                        lean_dec(v_x_2753_);
                        v___x_2766_ = lean_box(0);
                        v_isShared_2767_ = v_isSharedCheck_2772_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2758_ == 0 {
                    v___x_2760_ = v___x_2757_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2761_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
                    lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2760_;
            }
            3 => {
                v___x_2768_ = lean_apply_1(v_f_2752_, v_a_2763_);
                if v_isShared_2767_ == 0 {
                    lean_ctor_set(v___x_2766_, 0, v___x_2768_);
                    v___x_2770_ = v___x_2766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
                    lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_a_2764_);
                    v___x_2770_ = v_reuseFailAlloc_2771_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2770_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_adaptExcept___redArg(
    mut v_inst_2773_: *mut LeanObject,
    mut v_f_2774_: *mut LeanObject,
    mut v_x_2775_: *mut LeanObject,
    mut v_s_2776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut LeanObject = core::ptr::null_mut();
    v_map_2777_ = lean_ctor_get(v_inst_2773_, 0);
    lean_inc(v_map_2777_);
    lean_dec_ref(v_inst_2773_);
    v___f_2778_ = lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2778_, 0, v_f_2774_);
    v___x_2779_ = lean_apply_1(v_x_2775_, v_s_2776_);
    v___x_2780_ = lean_apply_4(
        v_map_2777_,
        lean_box(0),
        lean_box(0),
        v___f_2778_,
        v___x_2779_,
    );
    return v___x_2780_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept(
    mut v_00_u03b5_2781_: *mut LeanObject,
    mut v_00_u03b5_x27_2782_: *mut LeanObject,
    mut v_00_u03c3_2783_: *mut LeanObject,
    mut v_00_u03b1_2784_: *mut LeanObject,
    mut v_m_2785_: *mut LeanObject,
    mut v_inst_2786_: *mut LeanObject,
    mut v_f_2787_: *mut LeanObject,
    mut v_x_2788_: *mut LeanObject,
    mut v_s_2789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    v_map_2790_ = lean_ctor_get(v_inst_2786_, 0);
    lean_inc(v_map_2790_);
    lean_dec_ref(v_inst_2786_);
    v___f_2791_ = lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2791_, 0, v_f_2787_);
    v___x_2792_ = lean_apply_1(v_x_2788_, v_s_2789_);
    v___x_2793_ = lean_apply_4(
        v_map_2790_,
        lean_box(0),
        lean_box(0),
        v___f_2791_,
        v___x_2792_,
    );
    return v___x_2793_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__0(
    mut v_a_2794_: *mut LeanObject,
    mut v_toPure_2795_: *mut LeanObject,
    mut v_____do__lift_2796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_a_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2796_) == 0 {
                    v_a_2797_ = lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2798_ = lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2807_ = (!lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2807_ == 0 {
                        v___x_2800_ = v_____do__lift_2796_;
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2798_);
                        lean_inc(v_a_2797_);
                        lean_dec(v_____do__lift_2796_);
                        v___x_2800_ = lean_box(0);
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2794_);
                    v_a_2808_ = lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2809_ = lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2817_ = (!lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2811_ = v_____do__lift_2796_;
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2809_);
                        lean_inc(v_a_2808_);
                        lean_dec(v_____do__lift_2796_);
                        v___x_2811_ = lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2802_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2802_, 0, v_a_2794_);
                lean_ctor_set(v___x_2802_, 1, v_a_2797_);
                if v_isShared_2801_ == 0 {
                    lean_ctor_set(v___x_2800_, 0, v___x_2802_);
                    v___x_2804_ = v___x_2800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2802_);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2798_);
                    v___x_2804_ = v_reuseFailAlloc_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2805_ = lean_apply_2(v_toPure_2795_, lean_box(0), v___x_2804_);
                return v___x_2805_;
            }
            3 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2808_);
                    lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2815_ = lean_apply_2(v_toPure_2795_, lean_box(0), v___x_2814_);
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__1(
    mut v_a_2818_: *mut LeanObject,
    mut v_toPure_2819_: *mut LeanObject,
    mut v_____do__lift_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_____do__lift_2820_) == 0 {
                    v_a_2821_ = lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2829_ = (!lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v_unused_2830_ = lean_ctor_get(v_____do__lift_2820_, 0);
                        lean_dec(v_unused_2830_);
                        v___x_2823_ = v_____do__lift_2820_;
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2821_);
                        lean_dec(v_____do__lift_2820_);
                        v___x_2823_ = lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2818_);
                    v_a_2831_ = lean_ctor_get(v_____do__lift_2820_, 0);
                    v_a_2832_ = lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2840_ = (!lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2834_ = v_____do__lift_2820_;
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2832_);
                        lean_inc(v_a_2831_);
                        lean_dec(v_____do__lift_2820_);
                        v___x_2834_ = lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2824_ == 0 {
                    lean_ctor_set_tag(v___x_2823_, 1);
                    lean_ctor_set(v___x_2823_, 0, v_a_2818_);
                    v___x_2826_ = v___x_2823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2818_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_a_2821_);
                    v___x_2826_ = v_reuseFailAlloc_2828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2827_ = lean_apply_2(v_toPure_2819_, lean_box(0), v___x_2826_);
                return v___x_2827_;
            }
            3 => {
                if v_isShared_2835_ == 0 {
                    v___x_2837_ = v___x_2834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2831_);
                    lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_a_2832_);
                    v___x_2837_ = v_reuseFailAlloc_2839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2838_ = lean_apply_2(v_toPure_2819_, lean_box(0), v___x_2837_);
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__2(
    mut v_toPure_2841_: *mut LeanObject,
    mut v_f_2842_: *mut LeanObject,
    mut v_toBind_2843_: *mut LeanObject,
    mut v_r_2844_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_2844_) == 0 {
        let mut v_a_2845_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2846_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2847_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2850_: *mut LeanObject = core::ptr::null_mut();
        v_a_2845_ = lean_ctor_get(v_r_2844_, 0);
        lean_inc_n(v_a_2845_, 2);
        v_a_2846_ = lean_ctor_get(v_r_2844_, 1);
        lean_inc(v_a_2846_);
        lean_dec_ref_known(v_r_2844_, 2);
        v___f_2847_ = lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2847_, 0, v_a_2845_);
        lean_closure_set(v___f_2847_, 1, v_toPure_2841_);
        v___x_2848_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2848_, 0, v_a_2845_);
        v___x_2849_ = lean_apply_2(v_f_2842_, v___x_2848_, v_a_2846_);
        v___x_2850_ = lean_apply_4(
            v_toBind_2843_,
            lean_box(0),
            lean_box(0),
            v___x_2849_,
            v___f_2847_,
        );
        return v___x_2850_;
    } else {
        let mut v_a_2851_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2852_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2853_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
        v_a_2851_ = lean_ctor_get(v_r_2844_, 0);
        lean_inc(v_a_2851_);
        v_a_2852_ = lean_ctor_get(v_r_2844_, 1);
        lean_inc(v_a_2852_);
        lean_dec_ref_known(v_r_2844_, 2);
        v___f_2853_ = lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2853_, 0, v_a_2851_);
        lean_closure_set(v___f_2853_, 1, v_toPure_2841_);
        v___x_2854_ = lean_box(0);
        v___x_2855_ = lean_apply_2(v_f_2842_, v___x_2854_, v_a_2852_);
        v___x_2856_ = lean_apply_4(
            v_toBind_2843_,
            lean_box(0),
            lean_box(0),
            v___x_2855_,
            v___f_2853_,
        );
        return v___x_2856_;
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg(
    mut v_inst_2857_: *mut LeanObject,
    mut v_x_2858_: *mut LeanObject,
    mut v_f_2859_: *mut LeanObject,
    mut v_s_2860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2861_ = lean_ctor_get(v_inst_2857_, 0);
    lean_inc_ref(v_toApplicative_2861_);
    v_toBind_2862_ = lean_ctor_get(v_inst_2857_, 1);
    lean_inc_n(v_toBind_2862_, 2);
    lean_dec_ref(v_inst_2857_);
    v_toPure_2863_ = lean_ctor_get(v_toApplicative_2861_, 1);
    lean_inc(v_toPure_2863_);
    lean_dec_ref(v_toApplicative_2861_);
    v___x_2864_ = lean_apply_1(v_x_2858_, v_s_2860_);
    v___f_2865_ = lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2865_, 0, v_toPure_2863_);
    lean_closure_set(v___f_2865_, 1, v_f_2859_);
    lean_closure_set(v___f_2865_, 2, v_toBind_2862_);
    v___x_2866_ = lean_apply_4(
        v_toBind_2862_,
        lean_box(0),
        lean_box(0),
        v___x_2864_,
        v___f_2865_,
    );
    return v___x_2866_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27(
    mut v_00_u03b5_2867_: *mut LeanObject,
    mut v_00_u03c3_2868_: *mut LeanObject,
    mut v_00_u03b1_2869_: *mut LeanObject,
    mut v_00_u03b2_2870_: *mut LeanObject,
    mut v_m_2871_: *mut LeanObject,
    mut v_inst_2872_: *mut LeanObject,
    mut v_x_2873_: *mut LeanObject,
    mut v_f_2874_: *mut LeanObject,
    mut v_s_2875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2876_ = lean_ctor_get(v_inst_2872_, 0);
    lean_inc_ref(v_toApplicative_2876_);
    v_toBind_2877_ = lean_ctor_get(v_inst_2872_, 1);
    lean_inc_n(v_toBind_2877_, 2);
    lean_dec_ref(v_inst_2872_);
    v_toPure_2878_ = lean_ctor_get(v_toApplicative_2876_, 1);
    lean_inc(v_toPure_2878_);
    lean_dec_ref(v_toApplicative_2876_);
    v___x_2879_ = lean_apply_1(v_x_2873_, v_s_2875_);
    v___f_2880_ = lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2880_, 0, v_toPure_2878_);
    lean_closure_set(v___f_2880_, 1, v_f_2874_);
    lean_closure_set(v___f_2880_, 2, v_toBind_2877_);
    v___x_2881_ = lean_apply_4(
        v_toBind_2877_,
        lean_box(0),
        lean_box(0),
        v___x_2879_,
        v___f_2880_,
    );
    return v___x_2881_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(
    mut v_toPure_2882_: *mut LeanObject,
    mut v___y_2883_: *mut LeanObject,
    mut v_toBind_2884_: *mut LeanObject,
    mut v_r_2885_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_r_2885_) == 0 {
        let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2887_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2888_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
        v_a_2886_ = lean_ctor_get(v_r_2885_, 0);
        lean_inc_n(v_a_2886_, 2);
        v_a_2887_ = lean_ctor_get(v_r_2885_, 1);
        lean_inc(v_a_2887_);
        lean_dec_ref_known(v_r_2885_, 2);
        v___f_2888_ = lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2888_, 0, v_a_2886_);
        lean_closure_set(v___f_2888_, 1, v_toPure_2882_);
        v___x_2889_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2889_, 0, v_a_2886_);
        v___x_2890_ = lean_apply_2(v___y_2883_, v___x_2889_, v_a_2887_);
        v___x_2891_ = lean_apply_4(
            v_toBind_2884_,
            lean_box(0),
            lean_box(0),
            v___x_2890_,
            v___f_2888_,
        );
        return v___x_2891_;
    } else {
        let mut v_a_2892_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_2893_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_2894_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
        v_a_2892_ = lean_ctor_get(v_r_2885_, 0);
        lean_inc(v_a_2892_);
        v_a_2893_ = lean_ctor_get(v_r_2885_, 1);
        lean_inc(v_a_2893_);
        lean_dec_ref_known(v_r_2885_, 2);
        v___f_2894_ = lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_2894_, 0, v_a_2892_);
        lean_closure_set(v___f_2894_, 1, v_toPure_2882_);
        v___x_2895_ = lean_box(0);
        v___x_2896_ = lean_apply_2(v___y_2883_, v___x_2895_, v_a_2893_);
        v___x_2897_ = lean_apply_4(
            v_toBind_2884_,
            lean_box(0),
            lean_box(0),
            v___x_2896_,
            v___f_2894_,
        );
        return v___x_2897_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(
    mut v_inst_2898_: *mut LeanObject,
    mut v_00_u03b1_2899_: *mut LeanObject,
    mut v_00_u03b2_2900_: *mut LeanObject,
    mut v___y_2901_: *mut LeanObject,
    mut v___y_2902_: *mut LeanObject,
    mut v___y_2903_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2904_ = lean_ctor_get(v_inst_2898_, 0);
    lean_inc_ref(v_toApplicative_2904_);
    v_toBind_2905_ = lean_ctor_get(v_inst_2898_, 1);
    lean_inc_n(v_toBind_2905_, 2);
    lean_dec_ref(v_inst_2898_);
    v_toPure_2906_ = lean_ctor_get(v_toApplicative_2904_, 1);
    lean_inc(v_toPure_2906_);
    lean_dec_ref(v_toApplicative_2904_);
    v___x_2907_ = lean_apply_1(v___y_2901_, v___y_2903_);
    v___f_2908_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2908_, 0, v_toPure_2906_);
    lean_closure_set(v___f_2908_, 1, v___y_2902_);
    lean_closure_set(v___f_2908_, 2, v_toBind_2905_);
    v___x_2909_ = lean_apply_4(
        v_toBind_2905_,
        lean_box(0),
        lean_box(0),
        v___x_2907_,
        v___f_2908_,
    );
    return v___x_2909_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg(
    mut v_inst_2910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2911_: *mut LeanObject = core::ptr::null_mut();
    v___f_2911_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2911_, 0, v_inst_2910_);
    return v___f_2911_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad(
    mut v_00_u03b5_2912_: *mut LeanObject,
    mut v_00_u03c3_2913_: *mut LeanObject,
    mut v_m_2914_: *mut LeanObject,
    mut v_inst_2915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2916_: *mut LeanObject = core::ptr::null_mut();
    v___f_2916_ = lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_2916_, 0, v_inst_2915_);
    return v___f_2916_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM___redArg(
    mut v_f_2917_: *mut LeanObject,
    mut v_s_2918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut LeanObject = core::ptr::null_mut();
    v___x_2919_ = lean_apply_1(v_f_2917_, v_s_2918_);
    v___x_2920_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_2919_);
    return v___x_2920_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM(
    mut v_00_u03b5_2921_: *mut LeanObject,
    mut v_00_u03c3_2922_: *mut LeanObject,
    mut v_00_u03b1_2923_: *mut LeanObject,
    mut v_f_2924_: *mut LeanObject,
    mut v_s_2925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2926_: *mut LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lake_EStateT_ofEStateM___redArg(v_f_2924_, v_s_2925_);
    return v___x_2926_;
}
pub unsafe fn l_Lake_EStateT_toEStateM___redArg(
    mut v_f_2927_: *mut LeanObject,
    mut v_s_2928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    v___x_2929_ = lean_apply_1(v_f_2927_, v_s_2928_);
    v___x_2930_ = l_Lake_EResult_toEStateMResult___redArg(v___x_2929_);
    return v___x_2930_;
}
pub unsafe fn l_Lake_EStateT_toEStateM(
    mut v_00_u03b5_2931_: *mut LeanObject,
    mut v_00_u03c3_2932_: *mut LeanObject,
    mut v_00_u03b1_2933_: *mut LeanObject,
    mut v_f_2934_: *mut LeanObject,
    mut v_s_2935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Lake_EStateT_toEStateM___redArg(v_f_2934_, v_s_2935_);
    return v___x_2936_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_EStateT(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_EStateT(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_EStateT(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_State(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_EStateT(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_EStateT(builtin);
}

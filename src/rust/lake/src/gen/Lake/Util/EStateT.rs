// Lean compiler output
// Module: Lake.Util.EStateT
// Imports: Init.Control.State
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
pub static l_Lake_EResult_instFunctor___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_EResult_instFunctor___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EResult_instFunctor___closed__1_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_instFunctor___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_EResult_instFunctor___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EResult_instFunctor___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_EResult_instFunctor___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EStateT_run_x27___redArg___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toExcept___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_EStateT_run_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EStateT_toStateT___redArg___closed__0_value: leanh::LeanClosureObject<3> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_EStateT_toStateT___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value: leanh::LeanClosureObject<
    3,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_toProd_x3f as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_EStateT_toStateT_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value: leanh::LeanClosureObject<
    3,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_result_x3f___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_EStateT_run_x3f_x27___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_EResult_ctorIdx___redArg(
    mut v_x_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1469_) == 0 {
        let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1470_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1470_;
    } else {
        let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1471_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1471_;
    }
}
pub unsafe fn l_Lake_EResult_ctorIdx___redArg___boxed(
    mut v_x_1472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lake_EResult_ctorIdx___redArg(v_x_1472_);
    leanh::lean_dec_ref(v_x_1472_);
    return v_res_1473_;
}
pub unsafe fn l_Lake_EResult_ctorIdx(
    mut v_00_u03b5_1474_: *mut leanh::LeanObject,
    mut v_00_u03c3_1475_: *mut leanh::LeanObject,
    mut v_00_u03b1_1476_: *mut leanh::LeanObject,
    mut v_x_1477_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Lake_EResult_ctorIdx___redArg(v_x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lake_EResult_ctorIdx___boxed(
    mut v_00_u03b5_1479_: *mut leanh::LeanObject,
    mut v_00_u03c3_1480_: *mut leanh::LeanObject,
    mut v_00_u03b1_1481_: *mut leanh::LeanObject,
    mut v_x_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_Lake_EResult_ctorIdx(
        v_00_u03b5_1479_,
        v_00_u03c3_1480_,
        v_00_u03b1_1481_,
        v_x_1482_,
    );
    leanh::lean_dec_ref(v_x_1482_);
    return v_res_1483_;
}
pub unsafe fn l_Lake_EResult_ctorElim___redArg(
    mut v_t_1484_: *mut leanh::LeanObject,
    mut v_k_1485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1486_ = leanh::lean_ctor_get(v_t_1484_, 0);
    leanh::lean_inc(v_a_1486_);
    v_a_1487_ = leanh::lean_ctor_get(v_t_1484_, 1);
    leanh::lean_inc(v_a_1487_);
    leanh::lean_dec_ref(v_t_1484_);
    v___x_1488_ = leanh::lean_apply_2(v_k_1485_, v_a_1486_, v_a_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lake_EResult_ctorElim(
    mut v_00_u03b5_1489_: *mut leanh::LeanObject,
    mut v_00_u03c3_1490_: *mut leanh::LeanObject,
    mut v_00_u03b1_1491_: *mut leanh::LeanObject,
    mut v_motive_1492_: *mut leanh::LeanObject,
    mut v_ctorIdx_1493_: *mut leanh::LeanObject,
    mut v_t_1494_: *mut leanh::LeanObject,
    mut v_h_1495_: *mut leanh::LeanObject,
    mut v_k_1496_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lake_EResult_ctorElim___redArg(v_t_1494_, v_k_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_EResult_ctorElim___boxed(
    mut v_00_u03b5_1498_: *mut leanh::LeanObject,
    mut v_00_u03c3_1499_: *mut leanh::LeanObject,
    mut v_00_u03b1_1500_: *mut leanh::LeanObject,
    mut v_motive_1501_: *mut leanh::LeanObject,
    mut v_ctorIdx_1502_: *mut leanh::LeanObject,
    mut v_t_1503_: *mut leanh::LeanObject,
    mut v_h_1504_: *mut leanh::LeanObject,
    mut v_k_1505_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v_ctorIdx_1502_);
    return v_res_1506_;
}
pub unsafe fn l_Lake_EResult_ok_elim___redArg(
    mut v_t_1507_: *mut leanh::LeanObject,
    mut v_ok_1508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lake_EResult_ctorElim___redArg(v_t_1507_, v_ok_1508_);
    return v___x_1509_;
}
pub unsafe fn l_Lake_EResult_ok_elim(
    mut v_00_u03b5_1510_: *mut leanh::LeanObject,
    mut v_00_u03c3_1511_: *mut leanh::LeanObject,
    mut v_00_u03b1_1512_: *mut leanh::LeanObject,
    mut v_motive_1513_: *mut leanh::LeanObject,
    mut v_t_1514_: *mut leanh::LeanObject,
    mut v_h_1515_: *mut leanh::LeanObject,
    mut v_ok_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_Lake_EResult_ctorElim___redArg(v_t_1514_, v_ok_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Lake_EResult_error_elim___redArg(
    mut v_t_1518_: *mut leanh::LeanObject,
    mut v_error_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = l_Lake_EResult_ctorElim___redArg(v_t_1518_, v_error_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lake_EResult_error_elim(
    mut v_00_u03b5_1521_: *mut leanh::LeanObject,
    mut v_00_u03c3_1522_: *mut leanh::LeanObject,
    mut v_00_u03b1_1523_: *mut leanh::LeanObject,
    mut v_motive_1524_: *mut leanh::LeanObject,
    mut v_t_1525_: *mut leanh::LeanObject,
    mut v_h_1526_: *mut leanh::LeanObject,
    mut v_error_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lake_EResult_ctorElim___redArg(v_t_1525_, v_error_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Lake_EResult_instInhabited___redArg(
    mut v_inst_1529_: *mut leanh::LeanObject,
    mut v_inst_1530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1531_, 0, v_inst_1529_);
    leanh::lean_ctor_set(v___x_1531_, 1, v_inst_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lake_EResult_instInhabited(
    mut v_00_u03b1_1532_: *mut leanh::LeanObject,
    mut v_00_u03c3_1533_: *mut leanh::LeanObject,
    mut v_00_u03b5_1534_: *mut leanh::LeanObject,
    mut v_inst_1535_: *mut leanh::LeanObject,
    mut v_inst_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1537_, 0, v_inst_1535_);
    leanh::lean_ctor_set(v___x_1537_, 1, v_inst_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1___redArg(
    mut v_inst_1538_: *mut leanh::LeanObject,
    mut v_inst_1539_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1540_, 0, v_inst_1538_);
    leanh::lean_ctor_set(v___x_1540_, 1, v_inst_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1(
    mut v_00_u03b5_1541_: *mut leanh::LeanObject,
    mut v_00_u03c3_1542_: *mut leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut leanh::LeanObject,
    mut v_inst_1544_: *mut leanh::LeanObject,
    mut v_inst_1545_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1546_, 0, v_inst_1544_);
    leanh::lean_ctor_set(v___x_1546_, 1, v_inst_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lake_EResult_state___redArg(
    mut v_x_1547_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1548_ = leanh::lean_ctor_get(v_x_1547_, 1);
    leanh::lean_inc(v_a_1548_);
    return v_a_1548_;
}
pub unsafe fn l_Lake_EResult_state___redArg___boxed(
    mut v_x_1549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_EResult_state___redArg(v_x_1549_);
    leanh::lean_dec_ref(v_x_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_EResult_state(
    mut v_00_u03b5_1551_: *mut leanh::LeanObject,
    mut v_00_u03c3_1552_: *mut leanh::LeanObject,
    mut v_00_u03b1_1553_: *mut leanh::LeanObject,
    mut v_x_1554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_1555_ = leanh::lean_ctor_get(v_x_1554_, 1);
    leanh::lean_inc(v_a_1555_);
    return v_a_1555_;
}
pub unsafe fn l_Lake_EResult_state___boxed(
    mut v_00_u03b5_1556_: *mut leanh::LeanObject,
    mut v_00_u03c3_1557_: *mut leanh::LeanObject,
    mut v_00_u03b1_1558_: *mut leanh::LeanObject,
    mut v_x_1559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lake_EResult_state(
        v_00_u03b5_1556_,
        v_00_u03c3_1557_,
        v_00_u03b1_1558_,
        v_x_1559_,
    );
    leanh::lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lake_EResult_modifyState___redArg(
    mut v_f_1561_: *mut leanh::LeanObject,
    mut v_x_1562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_a_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1562_) == 0 {
                    v_a_1563_ = leanh::lean_ctor_get(v_x_1562_, 0);
                    v_a_1564_ = leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1572_ = (!leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1566_ = v_x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1564_);
                        leanh::lean_inc(v_a_1563_);
                        leanh::lean_dec(v_x_1562_);
                        v___x_1566_ = leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1573_ = leanh::lean_ctor_get(v_x_1562_, 0);
                    v_a_1574_ = leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1582_ = (!leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1582_ == 0 {
                        v___x_1576_ = v_x_1562_;
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1574_);
                        leanh::lean_inc(v_a_1573_);
                        leanh::lean_dec(v_x_1562_);
                        v___x_1576_ = leanh::lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1568_ = leanh::lean_apply_1(v_f_1561_, v_a_1564_);
                if v_isShared_1567_ == 0 {
                    leanh::lean_ctor_set(v___x_1566_, 1, v___x_1568_);
                    v___x_1570_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1563_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1570_;
            }
            3 => {
                v___x_1578_ = leanh::lean_apply_1(v_f_1561_, v_a_1574_);
                if v_isShared_1577_ == 0 {
                    leanh::lean_ctor_set(v___x_1576_, 1, v___x_1578_);
                    v___x_1580_ = v___x_1576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
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
    mut v_00_u03c3_1583_: *mut leanh::LeanObject,
    mut v_00_u03c3_x27_1584_: *mut leanh::LeanObject,
    mut v_00_u03b5_1585_: *mut leanh::LeanObject,
    mut v_00_u03b1_1586_: *mut leanh::LeanObject,
    mut v_f_1587_: *mut leanh::LeanObject,
    mut v_x_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_a_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1588_) == 0 {
                    v_a_1589_ = leanh::lean_ctor_get(v_x_1588_, 0);
                    v_a_1590_ = leanh::lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1598_ = (!leanh::lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1598_ == 0 {
                        v___x_1592_ = v_x_1588_;
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1590_);
                        leanh::lean_inc(v_a_1589_);
                        leanh::lean_dec(v_x_1588_);
                        v___x_1592_ = leanh::lean_box(0);
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1599_ = leanh::lean_ctor_get(v_x_1588_, 0);
                    v_a_1600_ = leanh::lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1608_ = (!leanh::lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v___x_1602_ = v_x_1588_;
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1600_);
                        leanh::lean_inc(v_a_1599_);
                        leanh::lean_dec(v_x_1588_);
                        v___x_1602_ = leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1594_ = leanh::lean_apply_1(v_f_1587_, v_a_1590_);
                if v_isShared_1593_ == 0 {
                    leanh::lean_ctor_set(v___x_1592_, 1, v___x_1594_);
                    v___x_1596_ = v___x_1592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1589_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1596_;
            }
            3 => {
                v___x_1604_ = leanh::lean_apply_1(v_f_1587_, v_a_1600_);
                if v_isShared_1603_ == 0 {
                    leanh::lean_ctor_set(v___x_1602_, 1, v___x_1604_);
                    v___x_1606_ = v___x_1602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1607_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1599_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
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
    mut v_s_1609_: *mut leanh::LeanObject,
    mut v_r_1610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut v_unused_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_unused_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_r_1610_) == 0 {
                    v_a_1611_ = leanh::lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1618_ = (!leanh::lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v_unused_1619_ = leanh::lean_ctor_get(v_r_1610_, 1);
                        leanh::lean_dec(v_unused_1619_);
                        v___x_1613_ = v_r_1610_;
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1611_);
                        leanh::lean_dec(v_r_1610_);
                        v___x_1613_ = leanh::lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1620_ = leanh::lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1627_ = (!leanh::lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v_unused_1628_ = leanh::lean_ctor_get(v_r_1610_, 1);
                        leanh::lean_dec(v_unused_1628_);
                        v___x_1622_ = v_r_1610_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1620_);
                        leanh::lean_dec(v_r_1610_);
                        v___x_1622_ = leanh::lean_box(0);
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1614_ == 0 {
                    leanh::lean_ctor_set(v___x_1613_, 1, v_s_1609_);
                    v___x_1616_ = v___x_1613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_s_1609_);
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
                    leanh::lean_ctor_set(v___x_1622_, 1, v_s_1609_);
                    v___x_1625_ = v___x_1622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_s_1609_);
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
    mut v_00_u03c3_x27_1629_: *mut leanh::LeanObject,
    mut v_00_u03b5_1630_: *mut leanh::LeanObject,
    mut v_00_u03c3_1631_: *mut leanh::LeanObject,
    mut v_00_u03b1_1632_: *mut leanh::LeanObject,
    mut v_s_1633_: *mut leanh::LeanObject,
    mut v_r_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_unused_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_r_1634_) == 0 {
                    v_a_1635_ = leanh::lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1642_ = (!leanh::lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1642_ == 0 {
                        v_unused_1643_ = leanh::lean_ctor_get(v_r_1634_, 1);
                        leanh::lean_dec(v_unused_1643_);
                        v___x_1637_ = v_r_1634_;
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1635_);
                        leanh::lean_dec(v_r_1634_);
                        v___x_1637_ = leanh::lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1644_ = leanh::lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1651_ = (!leanh::lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v_unused_1652_ = leanh::lean_ctor_get(v_r_1634_, 1);
                        leanh::lean_dec(v_unused_1652_);
                        v___x_1646_ = v_r_1634_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1644_);
                        leanh::lean_dec(v_r_1634_);
                        v___x_1646_ = leanh::lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1638_ == 0 {
                    leanh::lean_ctor_set(v___x_1637_, 1, v_s_1633_);
                    v___x_1640_ = v___x_1637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_s_1633_);
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
                    leanh::lean_ctor_set(v___x_1646_, 1, v_s_1633_);
                    v___x_1649_ = v___x_1646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_s_1633_);
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
pub unsafe fn l_Lake_EResult_toProd___redArg(
    mut v_x_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_a_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1668_: u8 = 0;
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1653_) == 0 {
                    v_a_1654_ = leanh::lean_ctor_get(v_x_1653_, 0);
                    v_a_1655_ = leanh::lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1663_ = (!leanh::lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1657_ = v_x_1653_;
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1655_);
                        leanh::lean_inc(v_a_1654_);
                        leanh::lean_dec(v_x_1653_);
                        v___x_1657_ = leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1664_ = leanh::lean_ctor_get(v_x_1653_, 0);
                    v_a_1665_ = leanh::lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1673_ = (!leanh::lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1673_ == 0 {
                        v___x_1667_ = v_x_1653_;
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1665_);
                        leanh::lean_inc(v_a_1664_);
                        leanh::lean_dec(v_x_1653_);
                        v___x_1667_ = leanh::lean_box(0);
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1659_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1659_, 0, v_a_1654_);
                if v_isShared_1658_ == 0 {
                    leanh::lean_ctor_set(v___x_1657_, 0, v___x_1659_);
                    v___x_1661_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1661_;
            }
            3 => {
                v___x_1669_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1669_, 0, v_a_1664_);
                if v_isShared_1668_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1667_, 0);
                    leanh::lean_ctor_set(v___x_1667_, 0, v___x_1669_);
                    v___x_1671_ = v___x_1667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1665_);
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
    mut v_00_u03b5_1674_: *mut leanh::LeanObject,
    mut v_00_u03c3_1675_: *mut leanh::LeanObject,
    mut v_00_u03b1_1676_: *mut leanh::LeanObject,
    mut v_x_1677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1677_) == 0 {
                    v_a_1678_ = leanh::lean_ctor_get(v_x_1677_, 0);
                    v_a_1679_ = leanh::lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1687_ = (!leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1681_ = v_x_1677_;
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1679_);
                        leanh::lean_inc(v_a_1678_);
                        leanh::lean_dec(v_x_1677_);
                        v___x_1681_ = leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1688_ = leanh::lean_ctor_get(v_x_1677_, 0);
                    v_a_1689_ = leanh::lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1697_ = (!leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1691_ = v_x_1677_;
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1689_);
                        leanh::lean_inc(v_a_1688_);
                        leanh::lean_dec(v_x_1677_);
                        v___x_1691_ = leanh::lean_box(0);
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1683_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1683_, 0, v_a_1678_);
                if v_isShared_1682_ == 0 {
                    leanh::lean_ctor_set(v___x_1681_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1679_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1685_;
            }
            3 => {
                v___x_1693_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1693_, 0, v_a_1688_);
                if v_isShared_1692_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1691_, 0);
                    leanh::lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                    v___x_1695_ = v___x_1691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1689_);
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
    mut v_x_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1698_) == 0 {
                    v_a_1699_ = leanh::lean_ctor_get(v_x_1698_, 0);
                    v_a_1700_ = leanh::lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1708_ = (!leanh::lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v_x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1700_);
                        leanh::lean_inc(v_a_1699_);
                        leanh::lean_dec(v_x_1698_);
                        v___x_1702_ = leanh::lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1709_ = leanh::lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1717_ = (!leanh::lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = leanh::lean_ctor_get(v_x_1698_, 0);
                        leanh::lean_dec(v_unused_1718_);
                        v___x_1711_ = v_x_1698_;
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1709_);
                        leanh::lean_dec(v_x_1698_);
                        v___x_1711_ = leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1704_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1704_, 0, v_a_1699_);
                if v_isShared_1703_ == 0 {
                    leanh::lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                v___x_1713_ = leanh::lean_box(0);
                if v_isShared_1712_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1711_, 0);
                    leanh::lean_ctor_set(v___x_1711_, 0, v___x_1713_);
                    v___x_1715_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1709_);
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
    mut v_00_u03b5_1719_: *mut leanh::LeanObject,
    mut v_00_u03c3_1720_: *mut leanh::LeanObject,
    mut v_00_u03b1_1721_: *mut leanh::LeanObject,
    mut v_x_1722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1722_) == 0 {
                    v_a_1723_ = leanh::lean_ctor_get(v_x_1722_, 0);
                    v_a_1724_ = leanh::lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1732_ = (!leanh::lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1726_ = v_x_1722_;
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1724_);
                        leanh::lean_inc(v_a_1723_);
                        leanh::lean_dec(v_x_1722_);
                        v___x_1726_ = leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1733_ = leanh::lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1741_ = (!leanh::lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1741_ == 0 {
                        v_unused_1742_ = leanh::lean_ctor_get(v_x_1722_, 0);
                        leanh::lean_dec(v_unused_1742_);
                        v___x_1735_ = v_x_1722_;
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1733_);
                        leanh::lean_dec(v_x_1722_);
                        v___x_1735_ = leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1728_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1728_, 0, v_a_1723_);
                if v_isShared_1727_ == 0 {
                    leanh::lean_ctor_set(v___x_1726_, 0, v___x_1728_);
                    v___x_1730_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1724_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1730_;
            }
            3 => {
                v___x_1737_ = leanh::lean_box(0);
                if v_isShared_1736_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1735_, 0);
                    leanh::lean_ctor_set(v___x_1735_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1733_);
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
    mut v_x_1743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1743_) == 0 {
        let mut v_a_1744_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1744_ = leanh::lean_ctor_get(v_x_1743_, 0);
        leanh::lean_inc(v_a_1744_);
        v___x_1745_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1745_, 0, v_a_1744_);
        return v___x_1745_;
    } else {
        let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1746_ = leanh::lean_box(0);
        return v___x_1746_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___redArg___boxed(
    mut v_x_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lake_EResult_result_x3f___redArg(v_x_1747_);
    leanh::lean_dec_ref(v_x_1747_);
    return v_res_1748_;
}
pub unsafe fn l_Lake_EResult_result_x3f(
    mut v_00_u03b5_1749_: *mut leanh::LeanObject,
    mut v_00_u03c3_1750_: *mut leanh::LeanObject,
    mut v_00_u03b1_1751_: *mut leanh::LeanObject,
    mut v_x_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1752_) == 0 {
        let mut v_a_1753_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1753_ = leanh::lean_ctor_get(v_x_1752_, 0);
        leanh::lean_inc(v_a_1753_);
        v___x_1754_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1754_, 0, v_a_1753_);
        return v___x_1754_;
    } else {
        let mut v___x_1755_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1755_ = leanh::lean_box(0);
        return v___x_1755_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___boxed(
    mut v_00_u03b5_1756_: *mut leanh::LeanObject,
    mut v_00_u03c3_1757_: *mut leanh::LeanObject,
    mut v_00_u03b1_1758_: *mut leanh::LeanObject,
    mut v_x_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lake_EResult_result_x3f(
        v_00_u03b5_1756_,
        v_00_u03c3_1757_,
        v_00_u03b1_1758_,
        v_x_1759_,
    );
    leanh::lean_dec_ref(v_x_1759_);
    return v_res_1760_;
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg(
    mut v_x_1761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1761_) == 0 {
        let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1762_ = leanh::lean_box(0);
        return v___x_1762_;
    } else {
        let mut v_a_1763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1763_ = leanh::lean_ctor_get(v_x_1761_, 0);
        leanh::lean_inc(v_a_1763_);
        v___x_1764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1764_, 0, v_a_1763_);
        return v___x_1764_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg___boxed(
    mut v_x_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lake_EResult_error_x3f___redArg(v_x_1765_);
    leanh::lean_dec_ref(v_x_1765_);
    return v_res_1766_;
}
pub unsafe fn l_Lake_EResult_error_x3f(
    mut v_00_u03b5_1767_: *mut leanh::LeanObject,
    mut v_00_u03c3_1768_: *mut leanh::LeanObject,
    mut v_00_u03b1_1769_: *mut leanh::LeanObject,
    mut v_x_1770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1770_) == 0 {
        let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1771_ = leanh::lean_box(0);
        return v___x_1771_;
    } else {
        let mut v_a_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1772_ = leanh::lean_ctor_get(v_x_1770_, 0);
        leanh::lean_inc(v_a_1772_);
        v___x_1773_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1773_, 0, v_a_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___boxed(
    mut v_00_u03b5_1774_: *mut leanh::LeanObject,
    mut v_00_u03c3_1775_: *mut leanh::LeanObject,
    mut v_00_u03b1_1776_: *mut leanh::LeanObject,
    mut v_x_1777_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lake_EResult_error_x3f(
        v_00_u03b5_1774_,
        v_00_u03c3_1775_,
        v_00_u03b1_1776_,
        v_x_1777_,
    );
    leanh::lean_dec_ref(v_x_1777_);
    return v_res_1778_;
}
pub unsafe fn l_Lake_EResult_toExcept___redArg(
    mut v_x_1779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1779_) == 0 {
        let mut v_a_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1780_ = leanh::lean_ctor_get(v_x_1779_, 0);
        leanh::lean_inc(v_a_1780_);
        v___x_1781_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1781_, 0, v_a_1780_);
        return v___x_1781_;
    } else {
        let mut v_a_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1782_ = leanh::lean_ctor_get(v_x_1779_, 0);
        leanh::lean_inc(v_a_1782_);
        v___x_1783_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1783_, 0, v_a_1782_);
        return v___x_1783_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___redArg___boxed(
    mut v_x_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lake_EResult_toExcept___redArg(v_x_1784_);
    leanh::lean_dec_ref(v_x_1784_);
    return v_res_1785_;
}
pub unsafe fn l_Lake_EResult_toExcept(
    mut v_00_u03b5_1786_: *mut leanh::LeanObject,
    mut v_00_u03c3_1787_: *mut leanh::LeanObject,
    mut v_00_u03b1_1788_: *mut leanh::LeanObject,
    mut v_x_1789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1789_) == 0 {
        let mut v_a_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1790_ = leanh::lean_ctor_get(v_x_1789_, 0);
        leanh::lean_inc(v_a_1790_);
        v___x_1791_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1791_, 0, v_a_1790_);
        return v___x_1791_;
    } else {
        let mut v_a_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_1792_ = leanh::lean_ctor_get(v_x_1789_, 0);
        leanh::lean_inc(v_a_1792_);
        v___x_1793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1793_, 0, v_a_1792_);
        return v___x_1793_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___boxed(
    mut v_00_u03b5_1794_: *mut leanh::LeanObject,
    mut v_00_u03c3_1795_: *mut leanh::LeanObject,
    mut v_00_u03b1_1796_: *mut leanh::LeanObject,
    mut v_x_1797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lake_EResult_toExcept(
        v_00_u03b5_1794_,
        v_00_u03c3_1795_,
        v_00_u03b1_1796_,
        v_x_1797_,
    );
    leanh::lean_dec_ref(v_x_1797_);
    return v_res_1798_;
}
pub unsafe fn l_Lake_EResult_map___redArg(
    mut v_f_1799_: *mut leanh::LeanObject,
    mut v_x_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_a_1811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1800_) == 0 {
                    v_a_1801_ = leanh::lean_ctor_get(v_x_1800_, 0);
                    v_a_1802_ = leanh::lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1810_ = (!leanh::lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1810_ == 0 {
                        v___x_1804_ = v_x_1800_;
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1802_);
                        leanh::lean_inc(v_a_1801_);
                        leanh::lean_dec(v_x_1800_);
                        v___x_1804_ = leanh::lean_box(0);
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_1799_);
                    v_a_1811_ = leanh::lean_ctor_get(v_x_1800_, 0);
                    v_a_1812_ = leanh::lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1819_ = (!leanh::lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1814_ = v_x_1800_;
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1812_);
                        leanh::lean_inc(v_a_1811_);
                        leanh::lean_dec(v_x_1800_);
                        v___x_1814_ = leanh::lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1806_ = leanh::lean_apply_1(v_f_1799_, v_a_1801_);
                if v_isShared_1805_ == 0 {
                    leanh::lean_ctor_set(v___x_1804_, 0, v___x_1806_);
                    v___x_1808_ = v___x_1804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1802_);
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
                    v_reuseFailAlloc_1818_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1812_);
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
    mut v_00_u03b1_1820_: *mut leanh::LeanObject,
    mut v_00_u03b2_1821_: *mut leanh::LeanObject,
    mut v_00_u03b5_1822_: *mut leanh::LeanObject,
    mut v_00_u03c3_1823_: *mut leanh::LeanObject,
    mut v_f_1824_: *mut leanh::LeanObject,
    mut v_x_1825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut v_a_1836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1825_) == 0 {
                    v_a_1826_ = leanh::lean_ctor_get(v_x_1825_, 0);
                    v_a_1827_ = leanh::lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1835_ = (!leanh::lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1829_ = v_x_1825_;
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1827_);
                        leanh::lean_inc(v_a_1826_);
                        leanh::lean_dec(v_x_1825_);
                        v___x_1829_ = leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_1824_);
                    v_a_1836_ = leanh::lean_ctor_get(v_x_1825_, 0);
                    v_a_1837_ = leanh::lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1844_ = (!leanh::lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1844_ == 0 {
                        v___x_1839_ = v_x_1825_;
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1837_);
                        leanh::lean_inc(v_a_1836_);
                        leanh::lean_dec(v_x_1825_);
                        v___x_1839_ = leanh::lean_box(0);
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1831_ = leanh::lean_apply_1(v_f_1824_, v_a_1826_);
                if v_isShared_1830_ == 0 {
                    leanh::lean_ctor_set(v___x_1829_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1827_);
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
                    v_reuseFailAlloc_1843_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1836_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1837_);
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
    mut v_00_u03b1_1845_: *mut leanh::LeanObject,
    mut v_00_u03b2_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_a_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v___y_1848_) == 0 {
                    v_a_1849_ = leanh::lean_ctor_get(v___y_1848_, 0);
                    v_a_1850_ = leanh::lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1858_ = (!leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1852_ = v___y_1848_;
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1850_);
                        leanh::lean_inc(v_a_1849_);
                        leanh::lean_dec(v___y_1848_);
                        v___x_1852_ = leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_1847_);
                    v_a_1859_ = leanh::lean_ctor_get(v___y_1848_, 0);
                    v_a_1860_ = leanh::lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1867_ = (!leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v___x_1862_ = v___y_1848_;
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1860_);
                        leanh::lean_inc(v_a_1859_);
                        leanh::lean_dec(v___y_1848_);
                        v___x_1862_ = leanh::lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1854_ = leanh::lean_apply_1(v___y_1847_, v_a_1849_);
                if v_isShared_1853_ == 0 {
                    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1850_);
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
                    v_reuseFailAlloc_1866_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1859_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_a_1860_);
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
    mut v___f_1868_: *mut leanh::LeanObject,
    mut v_00_u03b1_1869_: *mut leanh::LeanObject,
    mut v_00_u03b2_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
    mut v___y_1872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_1873_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1873_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1873_, 2, v___y_1871_);
    v___x_1874_ = leanh::lean_apply_4(
        v___f_1868_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1873_,
        v___y_1872_,
    );
    return v___x_1874_;
}
pub unsafe fn l_Lake_EResult_instFunctor(
    mut v_00_u03b5_1881_: *mut leanh::LeanObject,
    mut v_00_u03c3_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lake_EResult_instFunctor___closed__2;
    return v___x_1883_;
}
pub unsafe fn l_Lake_EResult_toEStateMResult___redArg(
    mut v_x_1884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_a_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1884_) == 0 {
                    v_a_1885_ = leanh::lean_ctor_get(v_x_1884_, 0);
                    v_a_1886_ = leanh::lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1893_ = (!leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1888_ = v_x_1884_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1886_);
                        leanh::lean_inc(v_a_1885_);
                        leanh::lean_dec(v_x_1884_);
                        v___x_1888_ = leanh::lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1894_ = leanh::lean_ctor_get(v_x_1884_, 0);
                    v_a_1895_ = leanh::lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1902_ = (!leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1902_ == 0 {
                        v___x_1897_ = v_x_1884_;
                        v_isShared_1898_ = v_isSharedCheck_1902_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1895_);
                        leanh::lean_inc(v_a_1894_);
                        leanh::lean_dec(v_x_1884_);
                        v___x_1897_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1892_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1885_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1886_);
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
                    v_reuseFailAlloc_1901_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1894_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1895_);
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
    mut v_00_u03b5_1903_: *mut leanh::LeanObject,
    mut v_00_u03c3_1904_: *mut leanh::LeanObject,
    mut v_00_u03b1_1905_: *mut leanh::LeanObject,
    mut v_x_1906_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lake_EResult_toEStateMResult___redArg(v_x_1906_);
    return v___x_1907_;
}
pub unsafe fn l_Lake_EResult_ofEStateMResult___redArg(
    mut v_x_1908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1908_) == 0 {
                    v_a_1909_ = leanh::lean_ctor_get(v_x_1908_, 0);
                    v_a_1910_ = leanh::lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1917_ = (!leanh::lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1917_ == 0 {
                        v___x_1912_ = v_x_1908_;
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1910_);
                        leanh::lean_inc(v_a_1909_);
                        leanh::lean_dec(v_x_1908_);
                        v___x_1912_ = leanh::lean_box(0);
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1918_ = leanh::lean_ctor_get(v_x_1908_, 0);
                    v_a_1919_ = leanh::lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1926_ = (!leanh::lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1921_ = v_x_1908_;
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1919_);
                        leanh::lean_inc(v_a_1918_);
                        leanh::lean_dec(v_x_1908_);
                        v___x_1921_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_1916_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1910_);
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
                    v_reuseFailAlloc_1925_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1919_);
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
    mut v_00_u03b5_1927_: *mut leanh::LeanObject,
    mut v_00_u03c3_1928_: *mut leanh::LeanObject,
    mut v_00_u03b1_1929_: *mut leanh::LeanObject,
    mut v_x_1930_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_1930_);
    return v___x_1931_;
}
pub unsafe fn l_Lake_EStateT_mk___redArg(
    mut v_x_1932_: *mut leanh::LeanObject,
    mut v_a_1933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = leanh::lean_apply_1(v_x_1932_, v_a_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lake_EStateT_mk(
    mut v_00_u03b5_1935_: *mut leanh::LeanObject,
    mut v_00_u03c3_1936_: *mut leanh::LeanObject,
    mut v_00_u03b1_1937_: *mut leanh::LeanObject,
    mut v_m_1938_: *mut leanh::LeanObject,
    mut v_x_1939_: *mut leanh::LeanObject,
    mut v_a_1940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = leanh::lean_apply_1(v_x_1939_, v_a_1940_);
    return v___x_1941_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(
    mut v_inst_1942_: *mut leanh::LeanObject,
    mut v_inst_1943_: *mut leanh::LeanObject,
    mut v_s_1944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1945_, 0, v_inst_1942_);
    leanh::lean_ctor_set(v___x_1945_, 1, v_s_1944_);
    v___x_1946_ = leanh::lean_apply_2(v_inst_1943_, leanh::lean_box(0), v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(
    mut v_inst_1947_: *mut leanh::LeanObject,
    mut v_inst_1948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1949_ = leanh::lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1949_, 0, v_inst_1947_);
    leanh::lean_closure_set(v___f_1949_, 1, v_inst_1948_);
    return v___f_1949_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(
    mut v_00_u03b5_1950_: *mut leanh::LeanObject,
    mut v_00_u03c3_1951_: *mut leanh::LeanObject,
    mut v_00_u03b1_1952_: *mut leanh::LeanObject,
    mut v_m_1953_: *mut leanh::LeanObject,
    mut v_inst_1954_: *mut leanh::LeanObject,
    mut v_inst_1955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1956_ = leanh::lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_1956_, 0, v_inst_1954_);
    leanh::lean_closure_set(v___f_1956_, 1, v_inst_1955_);
    return v___f_1956_;
}
pub unsafe fn l_Lake_EStateT_run___redArg(
    mut v_init_1957_: *mut leanh::LeanObject,
    mut v_self_1958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = leanh::lean_apply_1(v_self_1958_, v_init_1957_);
    return v___x_1959_;
}
pub unsafe fn l_Lake_EStateT_run(
    mut v_00_u03b5_1960_: *mut leanh::LeanObject,
    mut v_00_u03c3_1961_: *mut leanh::LeanObject,
    mut v_00_u03b1_1962_: *mut leanh::LeanObject,
    mut v_m_1963_: *mut leanh::LeanObject,
    mut v_init_1964_: *mut leanh::LeanObject,
    mut v_self_1965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1966_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = leanh::lean_apply_1(v_self_1965_, v_init_1964_);
    return v___x_1966_;
}
pub unsafe fn l_Lake_EStateT_run_x27___redArg(
    mut v_inst_1968_: *mut leanh::LeanObject,
    mut v_init_1969_: *mut leanh::LeanObject,
    mut v_x_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1971_ = leanh::lean_ctor_get(v_inst_1968_, 0);
    leanh::lean_inc(v_map_1971_);
    leanh::lean_dec_ref(v_inst_1968_);
    v___x_1972_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1973_ = leanh::lean_apply_1(v_x_1970_, v_init_1969_);
    v___x_1974_ = leanh::lean_apply_4(
        v_map_1971_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1972_,
        v___x_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn l_Lake_EStateT_run_x27(
    mut v_00_u03b5_1975_: *mut leanh::LeanObject,
    mut v_00_u03b1_1976_: *mut leanh::LeanObject,
    mut v_m_1977_: *mut leanh::LeanObject,
    mut v_00_u03c3_1978_: *mut leanh::LeanObject,
    mut v_inst_1979_: *mut leanh::LeanObject,
    mut v_init_1980_: *mut leanh::LeanObject,
    mut v_x_1981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1982_ = leanh::lean_ctor_get(v_inst_1979_, 0);
    leanh::lean_inc(v_map_1982_);
    leanh::lean_dec_ref(v_inst_1979_);
    v___x_1983_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1984_ = leanh::lean_apply_1(v_x_1981_, v_init_1980_);
    v___x_1985_ = leanh::lean_apply_4(
        v_map_1982_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1983_,
        v___x_1984_,
    );
    return v___x_1985_;
}
pub unsafe fn l_Lake_EStateT_toStateT___redArg(
    mut v_inst_1987_: *mut leanh::LeanObject,
    mut v_x_1988_: *mut leanh::LeanObject,
    mut v_s_1989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_1990_ = leanh::lean_ctor_get(v_inst_1987_, 0);
    leanh::lean_inc(v_map_1990_);
    leanh::lean_dec_ref(v_inst_1987_);
    v___x_1991_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_1992_ = leanh::lean_apply_1(v_x_1988_, v_s_1989_);
    v___x_1993_ = leanh::lean_apply_4(
        v_map_1990_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_1991_,
        v___x_1992_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_EStateT_toStateT(
    mut v_m_1994_: *mut leanh::LeanObject,
    mut v_00_u03b5_1995_: *mut leanh::LeanObject,
    mut v_00_u03c3_1996_: *mut leanh::LeanObject,
    mut v_00_u03b1_1997_: *mut leanh::LeanObject,
    mut v_inst_1998_: *mut leanh::LeanObject,
    mut v_x_1999_: *mut leanh::LeanObject,
    mut v_s_2000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2001_ = leanh::lean_ctor_get(v_inst_1998_, 0);
    leanh::lean_inc(v_map_2001_);
    leanh::lean_dec_ref(v_inst_1998_);
    v___x_2002_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_2003_ = leanh::lean_apply_1(v_x_1999_, v_s_2000_);
    v___x_2004_ = leanh::lean_apply_4(
        v_map_2001_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2002_,
        v___x_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f___redArg(
    mut v_inst_2006_: *mut leanh::LeanObject,
    mut v_x_2007_: *mut leanh::LeanObject,
    mut v_s_2008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2009_ = leanh::lean_ctor_get(v_inst_2006_, 0);
    leanh::lean_inc(v_map_2009_);
    leanh::lean_dec_ref(v_inst_2006_);
    v___x_2010_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2011_ = leanh::lean_apply_1(v_x_2007_, v_s_2008_);
    v___x_2012_ = leanh::lean_apply_4(
        v_map_2009_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2010_,
        v___x_2011_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f(
    mut v_m_2013_: *mut leanh::LeanObject,
    mut v_00_u03b5_2014_: *mut leanh::LeanObject,
    mut v_00_u03c3_2015_: *mut leanh::LeanObject,
    mut v_00_u03b1_2016_: *mut leanh::LeanObject,
    mut v_inst_2017_: *mut leanh::LeanObject,
    mut v_x_2018_: *mut leanh::LeanObject,
    mut v_s_2019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2020_ = leanh::lean_ctor_get(v_inst_2017_, 0);
    leanh::lean_inc(v_map_2020_);
    leanh::lean_dec_ref(v_inst_2017_);
    v___x_2021_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2022_ = leanh::lean_apply_1(v_x_2018_, v_s_2019_);
    v___x_2023_ = leanh::lean_apply_4(
        v_map_2020_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2021_,
        v___x_2022_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lake_EStateT_run_x3f___redArg(
    mut v_inst_2024_: *mut leanh::LeanObject,
    mut v_init_2025_: *mut leanh::LeanObject,
    mut v_x_2026_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2027_ = leanh::lean_ctor_get(v_inst_2024_, 0);
    leanh::lean_inc(v_map_2027_);
    leanh::lean_dec_ref(v_inst_2024_);
    v___x_2028_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2029_ = leanh::lean_apply_1(v_x_2026_, v_init_2025_);
    v___x_2030_ = leanh::lean_apply_4(
        v_map_2027_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2028_,
        v___x_2029_,
    );
    return v___x_2030_;
}
pub unsafe fn l_Lake_EStateT_run_x3f(
    mut v_00_u03c3_2031_: *mut leanh::LeanObject,
    mut v_00_u03b1_2032_: *mut leanh::LeanObject,
    mut v_m_2033_: *mut leanh::LeanObject,
    mut v_00_u03b5_2034_: *mut leanh::LeanObject,
    mut v_inst_2035_: *mut leanh::LeanObject,
    mut v_init_2036_: *mut leanh::LeanObject,
    mut v_x_2037_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2038_ = leanh::lean_ctor_get(v_inst_2035_, 0);
    leanh::lean_inc(v_map_2038_);
    leanh::lean_dec_ref(v_inst_2035_);
    v___x_2039_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2040_ = leanh::lean_apply_1(v_x_2037_, v_init_2036_);
    v___x_2041_ = leanh::lean_apply_4(
        v_map_2038_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2039_,
        v___x_2040_,
    );
    return v___x_2041_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27___redArg(
    mut v_inst_2043_: *mut leanh::LeanObject,
    mut v_init_2044_: *mut leanh::LeanObject,
    mut v_x_2045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2046_ = leanh::lean_ctor_get(v_inst_2043_, 0);
    leanh::lean_inc(v_map_2046_);
    leanh::lean_dec_ref(v_inst_2043_);
    v___x_2047_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2048_ = leanh::lean_apply_1(v_x_2045_, v_init_2044_);
    v___x_2049_ = leanh::lean_apply_4(
        v_map_2046_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2047_,
        v___x_2048_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27(
    mut v_m_2050_: *mut leanh::LeanObject,
    mut v_00_u03b5_2051_: *mut leanh::LeanObject,
    mut v_00_u03c3_2052_: *mut leanh::LeanObject,
    mut v_00_u03b1_2053_: *mut leanh::LeanObject,
    mut v_inst_2054_: *mut leanh::LeanObject,
    mut v_init_2055_: *mut leanh::LeanObject,
    mut v_x_2056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2057_ = leanh::lean_ctor_get(v_inst_2054_, 0);
    leanh::lean_inc(v_map_2057_);
    leanh::lean_dec_ref(v_inst_2054_);
    v___x_2058_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2059_ = leanh::lean_apply_1(v_x_2056_, v_init_2055_);
    v___x_2060_ = leanh::lean_apply_4(
        v_map_2057_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2058_,
        v___x_2059_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg___lam__0(
    mut v_toPure_2061_: *mut leanh::LeanObject,
    mut v_h_2062_: *mut leanh::LeanObject,
    mut v_____do__lift_2063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2063_) == 0 {
                    leanh::lean_dec(v_h_2062_);
                    v_a_2064_ = leanh::lean_ctor_get(v_____do__lift_2063_, 0);
                    v_a_2065_ = leanh::lean_ctor_get(v_____do__lift_2063_, 1);
                    v_isSharedCheck_2073_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2063_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2067_ = v_____do__lift_2063_;
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2065_);
                        leanh::lean_inc(v_a_2064_);
                        leanh::lean_dec(v_____do__lift_2063_);
                        v___x_2067_ = leanh::lean_box(0);
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toPure_2061_);
                    v_a_2074_ = leanh::lean_ctor_get(v_____do__lift_2063_, 0);
                    leanh::lean_inc(v_a_2074_);
                    v_a_2075_ = leanh::lean_ctor_get(v_____do__lift_2063_, 1);
                    leanh::lean_inc(v_a_2075_);
                    leanh::lean_dec_ref_known(v_____do__lift_2063_, 2);
                    v___x_2076_ = leanh::lean_apply_2(v_h_2062_, v_a_2074_, v_a_2075_);
                    return v___x_2076_;
                }
            }
            1 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2064_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2071_ = leanh::lean_apply_2(
                    v_toPure_2061_,
                    leanh::lean_box(0),
                    v___x_2070_,
                );
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg(
    mut v_inst_2077_: *mut leanh::LeanObject,
    mut v_x_2078_: *mut leanh::LeanObject,
    mut v_h_2079_: *mut leanh::LeanObject,
    mut v_s_2080_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2081_ = leanh::lean_ctor_get(v_inst_2077_, 0);
    leanh::lean_inc_ref(v_toApplicative_2081_);
    v_toBind_2082_ = leanh::lean_ctor_get(v_inst_2077_, 1);
    leanh::lean_inc(v_toBind_2082_);
    leanh::lean_dec_ref(v_inst_2077_);
    v_toPure_2083_ = leanh::lean_ctor_get(v_toApplicative_2081_, 1);
    leanh::lean_inc(v_toPure_2083_);
    leanh::lean_dec_ref(v_toApplicative_2081_);
    v___x_2084_ = leanh::lean_apply_1(v_x_2078_, v_s_2080_);
    v___f_2085_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2085_, 0, v_toPure_2083_);
    leanh::lean_closure_set(v___f_2085_, 1, v_h_2079_);
    v___x_2086_ = leanh::lean_apply_4(
        v_toBind_2082_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2084_,
        v___f_2085_,
    );
    return v___x_2086_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions(
    mut v_m_2087_: *mut leanh::LeanObject,
    mut v_00_u03b5_2088_: *mut leanh::LeanObject,
    mut v_00_u03c3_2089_: *mut leanh::LeanObject,
    mut v_00_u03b1_2090_: *mut leanh::LeanObject,
    mut v_inst_2091_: *mut leanh::LeanObject,
    mut v_x_2092_: *mut leanh::LeanObject,
    mut v_h_2093_: *mut leanh::LeanObject,
    mut v_s_2094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2095_ = leanh::lean_ctor_get(v_inst_2091_, 0);
    leanh::lean_inc_ref(v_toApplicative_2095_);
    v_toBind_2096_ = leanh::lean_ctor_get(v_inst_2091_, 1);
    leanh::lean_inc(v_toBind_2096_);
    leanh::lean_dec_ref(v_inst_2091_);
    v_toPure_2097_ = leanh::lean_ctor_get(v_toApplicative_2095_, 1);
    leanh::lean_inc(v_toPure_2097_);
    leanh::lean_dec_ref(v_toApplicative_2095_);
    v___x_2098_ = leanh::lean_apply_1(v_x_2092_, v_s_2094_);
    v___f_2099_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2099_, 0, v_toPure_2097_);
    leanh::lean_closure_set(v___f_2099_, 1, v_h_2093_);
    v___x_2100_ = leanh::lean_apply_4(
        v_toBind_2096_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2098_,
        v___f_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg___lam__0(
    mut v_s_2101_: *mut leanh::LeanObject,
    mut v_toPure_2102_: *mut leanh::LeanObject,
    mut v_a_2103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2104_, 0, v_a_2103_);
    leanh::lean_ctor_set(v___x_2104_, 1, v_s_2101_);
    v___x_2105_ =
        leanh::lean_apply_2(v_toPure_2102_, leanh::lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg(
    mut v_inst_2106_: *mut leanh::LeanObject,
    mut v_x_2107_: *mut leanh::LeanObject,
    mut v_s_2108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2109_ = leanh::lean_ctor_get(v_inst_2106_, 0);
    leanh::lean_inc_ref(v_toApplicative_2109_);
    v_toBind_2110_ = leanh::lean_ctor_get(v_inst_2106_, 1);
    leanh::lean_inc(v_toBind_2110_);
    leanh::lean_dec_ref(v_inst_2106_);
    v_toPure_2111_ = leanh::lean_ctor_get(v_toApplicative_2109_, 1);
    leanh::lean_inc(v_toPure_2111_);
    leanh::lean_dec_ref(v_toApplicative_2109_);
    v___f_2112_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2112_, 0, v_s_2108_);
    leanh::lean_closure_set(v___f_2112_, 1, v_toPure_2111_);
    v___x_2113_ = leanh::lean_apply_4(
        v_toBind_2110_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_2107_,
        v___f_2112_,
    );
    return v___x_2113_;
}
pub unsafe fn l_Lake_EStateT_lift(
    mut v_m_2114_: *mut leanh::LeanObject,
    mut v_00_u03b5_2115_: *mut leanh::LeanObject,
    mut v_00_u03c3_2116_: *mut leanh::LeanObject,
    mut v_00_u03b1_2117_: *mut leanh::LeanObject,
    mut v_inst_2118_: *mut leanh::LeanObject,
    mut v_x_2119_: *mut leanh::LeanObject,
    mut v_s_2120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2121_ = leanh::lean_ctor_get(v_inst_2118_, 0);
    leanh::lean_inc_ref(v_toApplicative_2121_);
    v_toBind_2122_ = leanh::lean_ctor_get(v_inst_2118_, 1);
    leanh::lean_inc(v_toBind_2122_);
    leanh::lean_dec_ref(v_inst_2118_);
    v_toPure_2123_ = leanh::lean_ctor_get(v_toApplicative_2121_, 1);
    leanh::lean_inc(v_toPure_2123_);
    leanh::lean_dec_ref(v_toApplicative_2121_);
    v___f_2124_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2124_, 0, v_s_2120_);
    leanh::lean_closure_set(v___f_2124_, 1, v_toPure_2123_);
    v___x_2125_ = leanh::lean_apply_4(
        v_toBind_2122_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_2119_,
        v___f_2124_,
    );
    return v___x_2125_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(
    mut v___y_2126_: *mut leanh::LeanObject,
    mut v_toPure_2127_: *mut leanh::LeanObject,
    mut v_a_2128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2129_, 0, v_a_2128_);
    leanh::lean_ctor_set(v___x_2129_, 1, v___y_2126_);
    v___x_2130_ =
        leanh::lean_apply_2(v_toPure_2127_, leanh::lean_box(0), v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(
    mut v_inst_2131_: *mut leanh::LeanObject,
    mut v_00_u03b1_2132_: *mut leanh::LeanObject,
    mut v___y_2133_: *mut leanh::LeanObject,
    mut v___y_2134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2135_ = leanh::lean_ctor_get(v_inst_2131_, 0);
    leanh::lean_inc_ref(v_toApplicative_2135_);
    v_toBind_2136_ = leanh::lean_ctor_get(v_inst_2131_, 1);
    leanh::lean_inc(v_toBind_2136_);
    leanh::lean_dec_ref(v_inst_2131_);
    v_toPure_2137_ = leanh::lean_ctor_get(v_toApplicative_2135_, 1);
    leanh::lean_inc(v_toPure_2137_);
    leanh::lean_dec_ref(v_toApplicative_2135_);
    v___f_2138_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2138_, 0, v___y_2134_);
    leanh::lean_closure_set(v___f_2138_, 1, v_toPure_2137_);
    v___x_2139_ = leanh::lean_apply_4(
        v_toBind_2136_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___y_2133_,
        v___f_2138_,
    );
    return v___x_2139_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg(
    mut v_inst_2140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2141_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2141_, 0, v_inst_2140_);
    return v___f_2141_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad(
    mut v_m_2142_: *mut leanh::LeanObject,
    mut v_00_u03b5_2143_: *mut leanh::LeanObject,
    mut v_00_u03c3_2144_: *mut leanh::LeanObject,
    mut v_inst_2145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2146_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2146_, 0, v_inst_2145_);
    return v___f_2146_;
}
pub unsafe fn l_Lake_EStateT_pure___redArg(
    mut v_inst_2147_: *mut leanh::LeanObject,
    mut v_a_2148_: *mut leanh::LeanObject,
    mut v_s_2149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2150_, 0, v_a_2148_);
    leanh::lean_ctor_set(v___x_2150_, 1, v_s_2149_);
    v___x_2151_ = leanh::lean_apply_2(v_inst_2147_, leanh::lean_box(0), v___x_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lake_EStateT_pure(
    mut v_00_u03b5_2152_: *mut leanh::LeanObject,
    mut v_00_u03c3_2153_: *mut leanh::LeanObject,
    mut v_00_u03b1_2154_: *mut leanh::LeanObject,
    mut v_m_2155_: *mut leanh::LeanObject,
    mut v_inst_2156_: *mut leanh::LeanObject,
    mut v_a_2157_: *mut leanh::LeanObject,
    mut v_s_2158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2159_, 0, v_a_2157_);
    leanh::lean_ctor_set(v___x_2159_, 1, v_s_2158_);
    v___x_2160_ = leanh::lean_apply_2(v_inst_2156_, leanh::lean_box(0), v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg___lam__0(
    mut v_inst_2161_: *mut leanh::LeanObject,
    mut v_00_u03b1_2162_: *mut leanh::LeanObject,
    mut v___y_2163_: *mut leanh::LeanObject,
    mut v___y_2164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2165_, 0, v___y_2163_);
    leanh::lean_ctor_set(v___x_2165_, 1, v___y_2164_);
    v___x_2166_ = leanh::lean_apply_2(v_inst_2161_, leanh::lean_box(0), v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg(
    mut v_inst_2167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2168_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2168_, 0, v_inst_2167_);
    return v___f_2168_;
}
pub unsafe fn l_Lake_EStateT_instPure(
    mut v_00_u03b5_2169_: *mut leanh::LeanObject,
    mut v_00_u03c3_2170_: *mut leanh::LeanObject,
    mut v_m_2171_: *mut leanh::LeanObject,
    mut v_inst_2172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2173_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2173_, 0, v_inst_2172_);
    return v___f_2173_;
}
pub unsafe fn l_Lake_EStateT_map___redArg___lam__0(
    mut v_f_2174_: *mut leanh::LeanObject,
    mut v_x_2175_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2175_) == 0 {
                    v_a_2176_ = leanh::lean_ctor_get(v_x_2175_, 0);
                    v_a_2177_ = leanh::lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2185_ = (!leanh::lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2185_ == 0 {
                        v___x_2179_ = v_x_2175_;
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2177_);
                        leanh::lean_inc(v_a_2176_);
                        leanh::lean_dec(v_x_2175_);
                        v___x_2179_ = leanh::lean_box(0);
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_f_2174_);
                    v_a_2186_ = leanh::lean_ctor_get(v_x_2175_, 0);
                    v_a_2187_ = leanh::lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2194_ = (!leanh::lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v_x_2175_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2187_);
                        leanh::lean_inc(v_a_2186_);
                        leanh::lean_dec(v_x_2175_);
                        v___x_2189_ = leanh::lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2181_ = leanh::lean_apply_1(v_f_2174_, v_a_2176_);
                if v_isShared_2180_ == 0 {
                    leanh::lean_ctor_set(v___x_2179_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_a_2177_);
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
                    v_reuseFailAlloc_2193_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2186_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2187_);
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
    mut v_inst_2195_: *mut leanh::LeanObject,
    mut v_f_2196_: *mut leanh::LeanObject,
    mut v_x_2197_: *mut leanh::LeanObject,
    mut v_s_2198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2199_ = leanh::lean_ctor_get(v_inst_2195_, 0);
    leanh::lean_inc(v_map_2199_);
    leanh::lean_dec_ref(v_inst_2195_);
    v___f_2200_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2200_, 0, v_f_2196_);
    v___x_2201_ = leanh::lean_apply_1(v_x_2197_, v_s_2198_);
    v___x_2202_ = leanh::lean_apply_4(
        v_map_2199_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2200_,
        v___x_2201_,
    );
    return v___x_2202_;
}
pub unsafe fn l_Lake_EStateT_map(
    mut v_00_u03b5_2203_: *mut leanh::LeanObject,
    mut v_00_u03c3_2204_: *mut leanh::LeanObject,
    mut v_00_u03b1_2205_: *mut leanh::LeanObject,
    mut v_00_u03b2_2206_: *mut leanh::LeanObject,
    mut v_m_2207_: *mut leanh::LeanObject,
    mut v_inst_2208_: *mut leanh::LeanObject,
    mut v_f_2209_: *mut leanh::LeanObject,
    mut v_x_2210_: *mut leanh::LeanObject,
    mut v_s_2211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2212_ = leanh::lean_ctor_get(v_inst_2208_, 0);
    leanh::lean_inc(v_map_2212_);
    leanh::lean_dec_ref(v_inst_2208_);
    v___f_2213_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2213_, 0, v_f_2209_);
    v___x_2214_ = leanh::lean_apply_1(v_x_2210_, v_s_2211_);
    v___x_2215_ = leanh::lean_apply_4(
        v_map_2212_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2213_,
        v___x_2214_,
    );
    return v___x_2215_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__0(
    mut v___y_2216_: *mut leanh::LeanObject,
    mut v_x_2217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2217_) == 0 {
                    v_a_2218_ = leanh::lean_ctor_get(v_x_2217_, 0);
                    v_a_2219_ = leanh::lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2227_ = (!leanh::lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2227_ == 0 {
                        v___x_2221_ = v_x_2217_;
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2219_);
                        leanh::lean_inc(v_a_2218_);
                        leanh::lean_dec(v_x_2217_);
                        v___x_2221_ = leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___y_2216_);
                    v_a_2228_ = leanh::lean_ctor_get(v_x_2217_, 0);
                    v_a_2229_ = leanh::lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2236_ = (!leanh::lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v_x_2217_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2229_);
                        leanh::lean_inc(v_a_2228_);
                        leanh::lean_dec(v_x_2217_);
                        v___x_2231_ = leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2223_ = leanh::lean_apply_1(v___y_2216_, v_a_2218_);
                if v_isShared_2222_ == 0 {
                    leanh::lean_ctor_set(v___x_2221_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_a_2219_);
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
                    v_reuseFailAlloc_2235_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2228_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2229_);
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
    mut v_inst_2237_: *mut leanh::LeanObject,
    mut v_00_u03b1_2238_: *mut leanh::LeanObject,
    mut v_00_u03b2_2239_: *mut leanh::LeanObject,
    mut v___y_2240_: *mut leanh::LeanObject,
    mut v___y_2241_: *mut leanh::LeanObject,
    mut v___y_2242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2243_ = leanh::lean_ctor_get(v_inst_2237_, 0);
    leanh::lean_inc(v_map_2243_);
    leanh::lean_dec_ref(v_inst_2237_);
    v___f_2244_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2244_, 0, v___y_2240_);
    v___x_2245_ = leanh::lean_apply_1(v___y_2241_, v___y_2242_);
    v___x_2246_ = leanh::lean_apply_4(
        v_map_2243_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2244_,
        v___x_2245_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__2(
    mut v___f_2247_: *mut leanh::LeanObject,
    mut v_00_u03b1_2248_: *mut leanh::LeanObject,
    mut v_00_u03b2_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2253_ =
        leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_2253_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2253_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2253_, 2, v___y_2250_);
    v___x_2254_ = leanh::lean_apply_5(
        v___f_2247_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2253_,
        v___y_2251_,
        v___y_2252_,
    );
    return v___x_2254_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg(
    mut v_inst_2255_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2256_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2256_, 0, v_inst_2255_);
    leanh::lean_inc_ref(v___f_2256_);
    v___f_2257_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2257_, 0, v___f_2256_);
    v___x_2258_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2258_, 0, v___f_2256_);
    leanh::lean_ctor_set(v___x_2258_, 1, v___f_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lake_EStateT_instFunctor(
    mut v_00_u03b5_2259_: *mut leanh::LeanObject,
    mut v_00_u03c3_2260_: *mut leanh::LeanObject,
    mut v_m_2261_: *mut leanh::LeanObject,
    mut v_inst_2262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lake_EStateT_instFunctor___redArg(v_inst_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lake_EStateT_bind___redArg___lam__0(
    mut v_f_2264_: *mut leanh::LeanObject,
    mut v_toPure_2265_: *mut leanh::LeanObject,
    mut v_____do__lift_2266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2266_) == 0 {
                    leanh::lean_dec(v_toPure_2265_);
                    v_a_2267_ = leanh::lean_ctor_get(v_____do__lift_2266_, 0);
                    leanh::lean_inc(v_a_2267_);
                    v_a_2268_ = leanh::lean_ctor_get(v_____do__lift_2266_, 1);
                    leanh::lean_inc(v_a_2268_);
                    leanh::lean_dec_ref_known(v_____do__lift_2266_, 2);
                    v___x_2269_ = leanh::lean_apply_2(v_f_2264_, v_a_2267_, v_a_2268_);
                    return v___x_2269_;
                } else {
                    leanh::lean_dec(v_f_2264_);
                    v_a_2270_ = leanh::lean_ctor_get(v_____do__lift_2266_, 0);
                    v_a_2271_ = leanh::lean_ctor_get(v_____do__lift_2266_, 1);
                    v_isSharedCheck_2279_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2266_)) as u8;
                    if v_isSharedCheck_2279_ == 0 {
                        v___x_2273_ = v_____do__lift_2266_;
                        v_isShared_2274_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2271_);
                        leanh::lean_inc(v_a_2270_);
                        leanh::lean_dec(v_____do__lift_2266_);
                        v___x_2273_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2278_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2277_ = leanh::lean_apply_2(
                    v_toPure_2265_,
                    leanh::lean_box(0),
                    v___x_2276_,
                );
                return v___x_2277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_bind___redArg(
    mut v_inst_2280_: *mut leanh::LeanObject,
    mut v_x_2281_: *mut leanh::LeanObject,
    mut v_f_2282_: *mut leanh::LeanObject,
    mut v_s_2283_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2284_ = leanh::lean_ctor_get(v_inst_2280_, 0);
    leanh::lean_inc_ref(v_toApplicative_2284_);
    v_toBind_2285_ = leanh::lean_ctor_get(v_inst_2280_, 1);
    leanh::lean_inc(v_toBind_2285_);
    leanh::lean_dec_ref(v_inst_2280_);
    v_toPure_2286_ = leanh::lean_ctor_get(v_toApplicative_2284_, 1);
    leanh::lean_inc(v_toPure_2286_);
    leanh::lean_dec_ref(v_toApplicative_2284_);
    v___x_2287_ = leanh::lean_apply_1(v_x_2281_, v_s_2283_);
    v___f_2288_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2288_, 0, v_f_2282_);
    leanh::lean_closure_set(v___f_2288_, 1, v_toPure_2286_);
    v___x_2289_ = leanh::lean_apply_4(
        v_toBind_2285_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2287_,
        v___f_2288_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Lake_EStateT_bind(
    mut v_00_u03b5_2290_: *mut leanh::LeanObject,
    mut v_00_u03c3_2291_: *mut leanh::LeanObject,
    mut v_00_u03b1_2292_: *mut leanh::LeanObject,
    mut v_00_u03b2_2293_: *mut leanh::LeanObject,
    mut v_m_2294_: *mut leanh::LeanObject,
    mut v_inst_2295_: *mut leanh::LeanObject,
    mut v_x_2296_: *mut leanh::LeanObject,
    mut v_f_2297_: *mut leanh::LeanObject,
    mut v_s_2298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2299_ = leanh::lean_ctor_get(v_inst_2295_, 0);
    leanh::lean_inc_ref(v_toApplicative_2299_);
    v_toBind_2300_ = leanh::lean_ctor_get(v_inst_2295_, 1);
    leanh::lean_inc(v_toBind_2300_);
    leanh::lean_dec_ref(v_inst_2295_);
    v_toPure_2301_ = leanh::lean_ctor_get(v_toApplicative_2299_, 1);
    leanh::lean_inc(v_toPure_2301_);
    leanh::lean_dec_ref(v_toApplicative_2299_);
    v___x_2302_ = leanh::lean_apply_1(v_x_2296_, v_s_2298_);
    v___f_2303_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2303_, 0, v_f_2297_);
    leanh::lean_closure_set(v___f_2303_, 1, v_toPure_2301_);
    v___x_2304_ = leanh::lean_apply_4(
        v_toBind_2300_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2302_,
        v___f_2303_,
    );
    return v___x_2304_;
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg___lam__0(
    mut v_y_2305_: *mut leanh::LeanObject,
    mut v_toPure_2306_: *mut leanh::LeanObject,
    mut v_____do__lift_2307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2307_) == 0 {
                    leanh::lean_dec(v_toPure_2306_);
                    v_a_2308_ = leanh::lean_ctor_get(v_____do__lift_2307_, 1);
                    leanh::lean_inc(v_a_2308_);
                    leanh::lean_dec_ref_known(v_____do__lift_2307_, 2);
                    v___x_2309_ = leanh::lean_box(0);
                    v___x_2310_ = leanh::lean_apply_2(v_y_2305_, v___x_2309_, v_a_2308_);
                    return v___x_2310_;
                } else {
                    leanh::lean_dec(v_y_2305_);
                    v_a_2311_ = leanh::lean_ctor_get(v_____do__lift_2307_, 0);
                    v_a_2312_ = leanh::lean_ctor_get(v_____do__lift_2307_, 1);
                    v_isSharedCheck_2320_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2307_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2314_ = v_____do__lift_2307_;
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2312_);
                        leanh::lean_inc(v_a_2311_);
                        leanh::lean_dec(v_____do__lift_2307_);
                        v___x_2314_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2318_ = leanh::lean_apply_2(
                    v_toPure_2306_,
                    leanh::lean_box(0),
                    v___x_2317_,
                );
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg(
    mut v_inst_2321_: *mut leanh::LeanObject,
    mut v_x_2322_: *mut leanh::LeanObject,
    mut v_y_2323_: *mut leanh::LeanObject,
    mut v_s_2324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2325_ = leanh::lean_ctor_get(v_inst_2321_, 0);
    leanh::lean_inc_ref(v_toApplicative_2325_);
    v_toBind_2326_ = leanh::lean_ctor_get(v_inst_2321_, 1);
    leanh::lean_inc(v_toBind_2326_);
    leanh::lean_dec_ref(v_inst_2321_);
    v_toPure_2327_ = leanh::lean_ctor_get(v_toApplicative_2325_, 1);
    leanh::lean_inc(v_toPure_2327_);
    leanh::lean_dec_ref(v_toApplicative_2325_);
    v___x_2328_ = leanh::lean_apply_1(v_x_2322_, v_s_2324_);
    v___f_2329_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2329_, 0, v_y_2323_);
    leanh::lean_closure_set(v___f_2329_, 1, v_toPure_2327_);
    v___x_2330_ = leanh::lean_apply_4(
        v_toBind_2326_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2328_,
        v___f_2329_,
    );
    return v___x_2330_;
}
pub unsafe fn l_Lake_EStateT_seqRight(
    mut v_00_u03b5_2331_: *mut leanh::LeanObject,
    mut v_00_u03c3_2332_: *mut leanh::LeanObject,
    mut v_00_u03b1_2333_: *mut leanh::LeanObject,
    mut v_00_u03b2_2334_: *mut leanh::LeanObject,
    mut v_m_2335_: *mut leanh::LeanObject,
    mut v_inst_2336_: *mut leanh::LeanObject,
    mut v_x_2337_: *mut leanh::LeanObject,
    mut v_y_2338_: *mut leanh::LeanObject,
    mut v_s_2339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2340_ = leanh::lean_ctor_get(v_inst_2336_, 0);
    leanh::lean_inc_ref(v_toApplicative_2340_);
    v_toBind_2341_ = leanh::lean_ctor_get(v_inst_2336_, 1);
    leanh::lean_inc(v_toBind_2341_);
    leanh::lean_dec_ref(v_inst_2336_);
    v_toPure_2342_ = leanh::lean_ctor_get(v_toApplicative_2340_, 1);
    leanh::lean_inc(v_toPure_2342_);
    leanh::lean_dec_ref(v_toApplicative_2340_);
    v___x_2343_ = leanh::lean_apply_1(v_x_2337_, v_s_2339_);
    v___f_2344_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2344_, 0, v_y_2338_);
    leanh::lean_closure_set(v___f_2344_, 1, v_toPure_2342_);
    v___x_2345_ = leanh::lean_apply_4(
        v_toBind_2341_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2343_,
        v___f_2344_,
    );
    return v___x_2345_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__0(
    mut v___y_2346_: *mut leanh::LeanObject,
    mut v_toPure_2347_: *mut leanh::LeanObject,
    mut v_____do__lift_2348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2348_) == 0 {
                    leanh::lean_dec(v_toPure_2347_);
                    v_a_2349_ = leanh::lean_ctor_get(v_____do__lift_2348_, 0);
                    leanh::lean_inc(v_a_2349_);
                    v_a_2350_ = leanh::lean_ctor_get(v_____do__lift_2348_, 1);
                    leanh::lean_inc(v_a_2350_);
                    leanh::lean_dec_ref_known(v_____do__lift_2348_, 2);
                    v___x_2351_ = leanh::lean_apply_2(v___y_2346_, v_a_2349_, v_a_2350_);
                    return v___x_2351_;
                } else {
                    leanh::lean_dec(v___y_2346_);
                    v_a_2352_ = leanh::lean_ctor_get(v_____do__lift_2348_, 0);
                    v_a_2353_ = leanh::lean_ctor_get(v_____do__lift_2348_, 1);
                    v_isSharedCheck_2361_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2348_)) as u8;
                    if v_isSharedCheck_2361_ == 0 {
                        v___x_2355_ = v_____do__lift_2348_;
                        v_isShared_2356_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2353_);
                        leanh::lean_inc(v_a_2352_);
                        leanh::lean_dec(v_____do__lift_2348_);
                        v___x_2355_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2360_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2352_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = leanh::lean_apply_2(
                    v_toPure_2347_,
                    leanh::lean_box(0),
                    v___x_2358_,
                );
                return v___x_2359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__1(
    mut v_toPure_2362_: *mut leanh::LeanObject,
    mut v_toBind_2363_: *mut leanh::LeanObject,
    mut v_00_u03b1_2364_: *mut leanh::LeanObject,
    mut v_00_u03b2_2365_: *mut leanh::LeanObject,
    mut v___y_2366_: *mut leanh::LeanObject,
    mut v___y_2367_: *mut leanh::LeanObject,
    mut v___y_2368_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = leanh::lean_apply_1(v___y_2366_, v___y_2368_);
    v___f_2370_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2370_, 0, v___y_2367_);
    leanh::lean_closure_set(v___f_2370_, 1, v_toPure_2362_);
    v___x_2371_ = leanh::lean_apply_4(
        v_toBind_2363_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2369_,
        v___f_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__2(
    mut v___y_2372_: *mut leanh::LeanObject,
    mut v_toPure_2373_: *mut leanh::LeanObject,
    mut v_____do__lift_2374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2374_) == 0 {
                    leanh::lean_dec(v_toPure_2373_);
                    v_a_2375_ = leanh::lean_ctor_get(v_____do__lift_2374_, 1);
                    leanh::lean_inc(v_a_2375_);
                    leanh::lean_dec_ref_known(v_____do__lift_2374_, 2);
                    v___x_2376_ = leanh::lean_box(0);
                    v___x_2377_ = leanh::lean_apply_2(v___y_2372_, v___x_2376_, v_a_2375_);
                    return v___x_2377_;
                } else {
                    leanh::lean_dec(v___y_2372_);
                    v_a_2378_ = leanh::lean_ctor_get(v_____do__lift_2374_, 0);
                    v_a_2379_ = leanh::lean_ctor_get(v_____do__lift_2374_, 1);
                    v_isSharedCheck_2387_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2381_ = v_____do__lift_2374_;
                        v_isShared_2382_ = v_isSharedCheck_2387_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2379_);
                        leanh::lean_inc(v_a_2378_);
                        leanh::lean_dec(v_____do__lift_2374_);
                        v___x_2381_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2386_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2385_ = leanh::lean_apply_2(
                    v_toPure_2373_,
                    leanh::lean_box(0),
                    v___x_2384_,
                );
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__3(
    mut v_toPure_2388_: *mut leanh::LeanObject,
    mut v_toBind_2389_: *mut leanh::LeanObject,
    mut v_00_u03b1_2390_: *mut leanh::LeanObject,
    mut v_00_u03b2_2391_: *mut leanh::LeanObject,
    mut v___y_2392_: *mut leanh::LeanObject,
    mut v___y_2393_: *mut leanh::LeanObject,
    mut v___y_2394_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = leanh::lean_apply_1(v___y_2392_, v___y_2394_);
    v___f_2396_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2396_, 0, v___y_2393_);
    leanh::lean_closure_set(v___f_2396_, 1, v_toPure_2388_);
    v___x_2397_ = leanh::lean_apply_4(
        v_toBind_2389_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2395_,
        v___f_2396_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6(
    mut v_a_2398_: *mut leanh::LeanObject,
    mut v_toPure_2399_: *mut leanh::LeanObject,
    mut v_x_2400_: *mut leanh::LeanObject,
    mut v___y_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2402_, 0, v_a_2398_);
    leanh::lean_ctor_set(v___x_2402_, 1, v___y_2401_);
    v___x_2403_ =
        leanh::lean_apply_2(v_toPure_2399_, leanh::lean_box(0), v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6___boxed(
    mut v_a_2404_: *mut leanh::LeanObject,
    mut v_toPure_2405_: *mut leanh::LeanObject,
    mut v_x_2406_: *mut leanh::LeanObject,
    mut v___y_2407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l_Lake_EStateT_instMonad___redArg___lam__6(
        v_a_2404_,
        v_toPure_2405_,
        v_x_2406_,
        v___y_2407_,
    );
    leanh::lean_dec(v_x_2406_);
    return v_res_2408_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__4(
    mut v_toPure_2409_: *mut leanh::LeanObject,
    mut v_y_2410_: *mut leanh::LeanObject,
    mut v___f_2411_: *mut leanh::LeanObject,
    mut v_a_2412_: *mut leanh::LeanObject,
    mut v___y_2413_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2414_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_2414_, 0, v_a_2412_);
    leanh::lean_closure_set(v___f_2414_, 1, v_toPure_2409_);
    v___x_2415_ = leanh::lean_box(0);
    v___x_2416_ = leanh::lean_apply_1(v_y_2410_, v___x_2415_);
    v___x_2417_ = leanh::lean_apply_5(
        v___f_2411_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2416_,
        v___f_2414_,
        v___y_2413_,
    );
    return v___x_2417_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__5(
    mut v_toPure_2418_: *mut leanh::LeanObject,
    mut v___f_2419_: *mut leanh::LeanObject,
    mut v_00_u03b1_2420_: *mut leanh::LeanObject,
    mut v_00_u03b2_2421_: *mut leanh::LeanObject,
    mut v_x_2422_: *mut leanh::LeanObject,
    mut v_y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___f_2419_);
    v___f_2425_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_2425_, 0, v_toPure_2418_);
    leanh::lean_closure_set(v___f_2425_, 1, v_y_2423_);
    leanh::lean_closure_set(v___f_2425_, 2, v___f_2419_);
    v___x_2426_ = leanh::lean_apply_5(
        v___f_2419_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_x_2422_,
        v___f_2425_,
        v___y_2424_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__7(
    mut v_a_2427_: *mut leanh::LeanObject,
    mut v_x_2428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut v_a_2439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2428_) == 0 {
                    v_a_2429_ = leanh::lean_ctor_get(v_x_2428_, 0);
                    v_a_2430_ = leanh::lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2438_ = (!leanh::lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2438_ == 0 {
                        v___x_2432_ = v_x_2428_;
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2430_);
                        leanh::lean_inc(v_a_2429_);
                        leanh::lean_dec(v_x_2428_);
                        v___x_2432_ = leanh::lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2427_);
                    v_a_2439_ = leanh::lean_ctor_get(v_x_2428_, 0);
                    v_a_2440_ = leanh::lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2447_ = (!leanh::lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2447_ == 0 {
                        v___x_2442_ = v_x_2428_;
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2440_);
                        leanh::lean_inc(v_a_2439_);
                        leanh::lean_dec(v_x_2428_);
                        v___x_2442_ = leanh::lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2434_ = leanh::lean_apply_1(v_a_2427_, v_a_2429_);
                if v_isShared_2433_ == 0 {
                    leanh::lean_ctor_set(v___x_2432_, 0, v___x_2434_);
                    v___x_2436_ = v___x_2432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2430_);
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
                    v_reuseFailAlloc_2446_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2440_);
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
    mut v_toFunctor_2448_: *mut leanh::LeanObject,
    mut v_x_2449_: *mut leanh::LeanObject,
    mut v_toPure_2450_: *mut leanh::LeanObject,
    mut v_____do__lift_2451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2451_) == 0 {
                    leanh::lean_dec(v_toPure_2450_);
                    v_a_2452_ = leanh::lean_ctor_get(v_____do__lift_2451_, 0);
                    leanh::lean_inc(v_a_2452_);
                    v_a_2453_ = leanh::lean_ctor_get(v_____do__lift_2451_, 1);
                    leanh::lean_inc(v_a_2453_);
                    leanh::lean_dec_ref_known(v_____do__lift_2451_, 2);
                    v_map_2454_ = leanh::lean_ctor_get(v_toFunctor_2448_, 0);
                    leanh::lean_inc(v_map_2454_);
                    leanh::lean_dec_ref(v_toFunctor_2448_);
                    v___f_2455_ = leanh::lean_alloc_closure(
                        l_Lake_EStateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    leanh::lean_closure_set(v___f_2455_, 0, v_a_2452_);
                    v___x_2456_ = leanh::lean_box(0);
                    v___x_2457_ = leanh::lean_apply_2(v_x_2449_, v___x_2456_, v_a_2453_);
                    v___x_2458_ = leanh::lean_apply_4(
                        v_map_2454_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_2455_,
                        v___x_2457_,
                    );
                    return v___x_2458_;
                } else {
                    leanh::lean_dec(v_x_2449_);
                    leanh::lean_dec_ref(v_toFunctor_2448_);
                    v_a_2459_ = leanh::lean_ctor_get(v_____do__lift_2451_, 0);
                    v_a_2460_ = leanh::lean_ctor_get(v_____do__lift_2451_, 1);
                    v_isSharedCheck_2468_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2451_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2462_ = v_____do__lift_2451_;
                        v_isShared_2463_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2460_);
                        leanh::lean_inc(v_a_2459_);
                        leanh::lean_dec(v_____do__lift_2451_);
                        v___x_2462_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2467_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2459_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2466_ = leanh::lean_apply_2(
                    v_toPure_2450_,
                    leanh::lean_box(0),
                    v___x_2465_,
                );
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__9(
    mut v_toFunctor_2469_: *mut leanh::LeanObject,
    mut v_toPure_2470_: *mut leanh::LeanObject,
    mut v_toBind_2471_: *mut leanh::LeanObject,
    mut v_00_u03b1_2472_: *mut leanh::LeanObject,
    mut v_00_u03b2_2473_: *mut leanh::LeanObject,
    mut v_f_2474_: *mut leanh::LeanObject,
    mut v_x_2475_: *mut leanh::LeanObject,
    mut v___y_2476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2477_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2477_, 0, v_toFunctor_2469_);
    leanh::lean_closure_set(v___f_2477_, 1, v_x_2475_);
    leanh::lean_closure_set(v___f_2477_, 2, v_toPure_2470_);
    v___x_2478_ = leanh::lean_apply_1(v_f_2474_, v___y_2476_);
    v___x_2479_ = leanh::lean_apply_4(
        v_toBind_2471_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2478_,
        v___f_2477_,
    );
    return v___x_2479_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg(
    mut v_inst_2480_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v_toFunctor_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___f_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_unused_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2481_ = leanh::lean_ctor_get(v_inst_2480_, 0);
                v_toBind_2482_ = leanh::lean_ctor_get(v_inst_2480_, 1);
                v_isSharedCheck_2507_ = (!leanh::lean_is_exclusive(v_inst_2480_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v___x_2484_ = v_inst_2480_;
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_2482_);
                    leanh::lean_inc(v_toApplicative_2481_);
                    leanh::lean_dec(v_inst_2480_);
                    v___x_2484_ = leanh::lean_box(0);
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2486_ = leanh::lean_ctor_get(v_toApplicative_2481_, 0);
                v_toPure_2487_ = leanh::lean_ctor_get(v_toApplicative_2481_, 1);
                v_isSharedCheck_2503_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2481_)) as u8;
                if v_isSharedCheck_2503_ == 0 {
                    v_unused_2504_ = leanh::lean_ctor_get(v_toApplicative_2481_, 4);
                    leanh::lean_dec(v_unused_2504_);
                    v_unused_2505_ = leanh::lean_ctor_get(v_toApplicative_2481_, 3);
                    leanh::lean_dec(v_unused_2505_);
                    v_unused_2506_ = leanh::lean_ctor_get(v_toApplicative_2481_, 2);
                    leanh::lean_dec(v_unused_2506_);
                    v___x_2489_ = v_toApplicative_2481_;
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toPure_2487_);
                    leanh::lean_inc(v_toFunctor_2486_);
                    leanh::lean_dec(v_toApplicative_2481_);
                    v___x_2489_ = leanh::lean_box(0);
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_toBind_2482_, 2);
                leanh::lean_inc_n(v_toPure_2487_, 4);
                v___f_2491_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2491_, 0, v_toPure_2487_);
                leanh::lean_closure_set(v___f_2491_, 1, v_toBind_2482_);
                v___f_2492_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2492_, 0, v_toPure_2487_);
                leanh::lean_closure_set(v___f_2492_, 1, v_toBind_2482_);
                leanh::lean_inc_ref(v___f_2491_);
                v___f_2493_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2493_, 0, v_toPure_2487_);
                leanh::lean_closure_set(v___f_2493_, 1, v___f_2491_);
                leanh::lean_inc_ref(v_toFunctor_2486_);
                v___f_2494_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                leanh::lean_closure_set(v___f_2494_, 0, v_toFunctor_2486_);
                leanh::lean_closure_set(v___f_2494_, 1, v_toPure_2487_);
                leanh::lean_closure_set(v___f_2494_, 2, v_toBind_2482_);
                v___x_2495_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2486_);
                v___f_2496_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_2496_, 0, v_toPure_2487_);
                if v_isShared_2490_ == 0 {
                    leanh::lean_ctor_set(v___x_2489_, 4, v___f_2492_);
                    leanh::lean_ctor_set(v___x_2489_, 3, v___f_2493_);
                    leanh::lean_ctor_set(v___x_2489_, 2, v___f_2494_);
                    leanh::lean_ctor_set(v___x_2489_, 1, v___f_2496_);
                    leanh::lean_ctor_set(v___x_2489_, 0, v___x_2495_);
                    v___x_2498_ = v___x_2489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2495_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___f_2496_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___f_2494_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___f_2493_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 4, v___f_2492_);
                    v___x_2498_ = v_reuseFailAlloc_2502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2485_ == 0 {
                    leanh::lean_ctor_set(v___x_2484_, 1, v___f_2491_);
                    leanh::lean_ctor_set(v___x_2484_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___f_2491_);
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
    mut v_00_u03b5_2508_: *mut leanh::LeanObject,
    mut v_00_u03c3_2509_: *mut leanh::LeanObject,
    mut v_m_2510_: *mut leanh::LeanObject,
    mut v_inst_2511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_toFunctor_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___f_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2512_ = leanh::lean_ctor_get(v_inst_2511_, 0);
                v_toBind_2513_ = leanh::lean_ctor_get(v_inst_2511_, 1);
                v_isSharedCheck_2538_ = (!leanh::lean_is_exclusive(v_inst_2511_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v___x_2515_ = v_inst_2511_;
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_2513_);
                    leanh::lean_inc(v_toApplicative_2512_);
                    leanh::lean_dec(v_inst_2511_);
                    v___x_2515_ = leanh::lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2517_ = leanh::lean_ctor_get(v_toApplicative_2512_, 0);
                v_toPure_2518_ = leanh::lean_ctor_get(v_toApplicative_2512_, 1);
                v_isSharedCheck_2534_ =
                    (!leanh::lean_is_exclusive(v_toApplicative_2512_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v_unused_2535_ = leanh::lean_ctor_get(v_toApplicative_2512_, 4);
                    leanh::lean_dec(v_unused_2535_);
                    v_unused_2536_ = leanh::lean_ctor_get(v_toApplicative_2512_, 3);
                    leanh::lean_dec(v_unused_2536_);
                    v_unused_2537_ = leanh::lean_ctor_get(v_toApplicative_2512_, 2);
                    leanh::lean_dec(v_unused_2537_);
                    v___x_2520_ = v_toApplicative_2512_;
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_toPure_2518_);
                    leanh::lean_inc(v_toFunctor_2517_);
                    leanh::lean_dec(v_toApplicative_2512_);
                    v___x_2520_ = leanh::lean_box(0);
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc_n(v_toBind_2513_, 2);
                leanh::lean_inc_n(v_toPure_2518_, 4);
                v___f_2522_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2522_, 0, v_toPure_2518_);
                leanh::lean_closure_set(v___f_2522_, 1, v_toBind_2513_);
                v___f_2523_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2523_, 0, v_toPure_2518_);
                leanh::lean_closure_set(v___f_2523_, 1, v_toBind_2513_);
                leanh::lean_inc_ref(v___f_2522_);
                v___f_2524_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                leanh::lean_closure_set(v___f_2524_, 0, v_toPure_2518_);
                leanh::lean_closure_set(v___f_2524_, 1, v___f_2522_);
                leanh::lean_inc_ref(v_toFunctor_2517_);
                v___f_2525_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                leanh::lean_closure_set(v___f_2525_, 0, v_toFunctor_2517_);
                leanh::lean_closure_set(v___f_2525_, 1, v_toPure_2518_);
                leanh::lean_closure_set(v___f_2525_, 2, v_toBind_2513_);
                v___x_2526_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2517_);
                v___f_2527_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_2527_, 0, v_toPure_2518_);
                if v_isShared_2521_ == 0 {
                    leanh::lean_ctor_set(v___x_2520_, 4, v___f_2523_);
                    leanh::lean_ctor_set(v___x_2520_, 3, v___f_2524_);
                    leanh::lean_ctor_set(v___x_2520_, 2, v___f_2525_);
                    leanh::lean_ctor_set(v___x_2520_, 1, v___f_2527_);
                    leanh::lean_ctor_set(v___x_2520_, 0, v___x_2526_);
                    v___x_2529_ = v___x_2520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2526_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___f_2527_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___f_2525_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___f_2524_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___f_2523_);
                    v___x_2529_ = v_reuseFailAlloc_2533_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2516_ == 0 {
                    leanh::lean_ctor_set(v___x_2515_, 1, v___f_2522_);
                    leanh::lean_ctor_set(v___x_2515_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___f_2522_);
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
    mut v_inst_2539_: *mut leanh::LeanObject,
    mut v_s_2540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = leanh::lean_box(0);
    v___x_2542_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    leanh::lean_ctor_set(v___x_2542_, 1, v_s_2540_);
    v___x_2543_ = leanh::lean_apply_2(v_inst_2539_, leanh::lean_box(0), v___x_2542_);
    return v___x_2543_;
}
pub unsafe fn l_Lake_EStateT_set(
    mut v_00_u03b5_2544_: *mut leanh::LeanObject,
    mut v_00_u03c3_2545_: *mut leanh::LeanObject,
    mut v_m_2546_: *mut leanh::LeanObject,
    mut v_inst_2547_: *mut leanh::LeanObject,
    mut v_s_2548_: *mut leanh::LeanObject,
    mut v_x_2549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = leanh::lean_box(0);
    v___x_2551_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    leanh::lean_ctor_set(v___x_2551_, 1, v_s_2548_);
    v___x_2552_ = leanh::lean_apply_2(v_inst_2547_, leanh::lean_box(0), v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lake_EStateT_set___boxed(
    mut v_00_u03b5_2553_: *mut leanh::LeanObject,
    mut v_00_u03c3_2554_: *mut leanh::LeanObject,
    mut v_m_2555_: *mut leanh::LeanObject,
    mut v_inst_2556_: *mut leanh::LeanObject,
    mut v_s_2557_: *mut leanh::LeanObject,
    mut v_x_2558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lake_EStateT_set(
        v_00_u03b5_2553_,
        v_00_u03c3_2554_,
        v_m_2555_,
        v_inst_2556_,
        v_s_2557_,
        v_x_2558_,
    );
    leanh::lean_dec(v_x_2558_);
    return v_res_2559_;
}
pub unsafe fn l_Lake_EStateT_get___redArg(
    mut v_inst_2560_: *mut leanh::LeanObject,
    mut v_s_2561_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_2561_);
    v___x_2562_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2562_, 0, v_s_2561_);
    leanh::lean_ctor_set(v___x_2562_, 1, v_s_2561_);
    v___x_2563_ = leanh::lean_apply_2(v_inst_2560_, leanh::lean_box(0), v___x_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Lake_EStateT_get(
    mut v_00_u03b5_2564_: *mut leanh::LeanObject,
    mut v_00_u03c3_2565_: *mut leanh::LeanObject,
    mut v_m_2566_: *mut leanh::LeanObject,
    mut v_inst_2567_: *mut leanh::LeanObject,
    mut v_s_2568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_s_2568_);
    v___x_2569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2569_, 0, v_s_2568_);
    leanh::lean_ctor_set(v___x_2569_, 1, v_s_2568_);
    v___x_2570_ = leanh::lean_apply_2(v_inst_2567_, leanh::lean_box(0), v___x_2569_);
    return v___x_2570_;
}
pub unsafe fn l_Lake_EStateT_modifyGet___redArg(
    mut v_inst_2571_: *mut leanh::LeanObject,
    mut v_f_2572_: *mut leanh::LeanObject,
    mut v_s_2573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2574_ = leanh::lean_apply_1(v_f_2572_, v_s_2573_);
                v_fst_2575_ = leanh::lean_ctor_get(v___x_2574_, 0);
                v_snd_2576_ = leanh::lean_ctor_get(v___x_2574_, 1);
                v_isSharedCheck_2584_ = (!leanh::lean_is_exclusive(v___x_2574_)) as u8;
                if v_isSharedCheck_2584_ == 0 {
                    v___x_2578_ = v___x_2574_;
                    v_isShared_2579_ = v_isSharedCheck_2584_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2576_);
                    leanh::lean_inc(v_fst_2575_);
                    leanh::lean_dec(v___x_2574_);
                    v___x_2578_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2583_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_fst_2575_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_snd_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2582_ = leanh::lean_apply_2(
                    v_inst_2571_,
                    leanh::lean_box(0),
                    v___x_2581_,
                );
                return v___x_2582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_modifyGet(
    mut v_00_u03b5_2585_: *mut leanh::LeanObject,
    mut v_00_u03c3_2586_: *mut leanh::LeanObject,
    mut v_00_u03b1_2587_: *mut leanh::LeanObject,
    mut v_m_2588_: *mut leanh::LeanObject,
    mut v_inst_2589_: *mut leanh::LeanObject,
    mut v_f_2590_: *mut leanh::LeanObject,
    mut v_s_2591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2592_ = leanh::lean_apply_1(v_f_2590_, v_s_2591_);
                v_fst_2593_ = leanh::lean_ctor_get(v___x_2592_, 0);
                v_snd_2594_ = leanh::lean_ctor_get(v___x_2592_, 1);
                v_isSharedCheck_2602_ = (!leanh::lean_is_exclusive(v___x_2592_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v___x_2596_ = v___x_2592_;
                    v_isShared_2597_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2594_);
                    leanh::lean_inc(v_fst_2593_);
                    leanh::lean_dec(v___x_2592_);
                    v___x_2596_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2601_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_fst_2593_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_snd_2594_);
                    v___x_2599_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2600_ = leanh::lean_apply_2(
                    v_inst_2589_,
                    leanh::lean_box(0),
                    v___x_2599_,
                );
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(
    mut v_inst_2603_: *mut leanh::LeanObject,
    mut v_00_u03b1_2604_: *mut leanh::LeanObject,
    mut v___y_2605_: *mut leanh::LeanObject,
    mut v___y_2606_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = leanh::lean_apply_1(v___y_2605_, v___y_2606_);
                v_fst_2608_ = leanh::lean_ctor_get(v___x_2607_, 0);
                v_snd_2609_ = leanh::lean_ctor_get(v___x_2607_, 1);
                v_isSharedCheck_2617_ = (!leanh::lean_is_exclusive(v___x_2607_)) as u8;
                if v_isSharedCheck_2617_ == 0 {
                    v___x_2611_ = v___x_2607_;
                    v_isShared_2612_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2609_);
                    leanh::lean_inc(v_fst_2608_);
                    leanh::lean_dec(v___x_2607_);
                    v___x_2611_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2616_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_snd_2609_);
                    v___x_2614_ = v_reuseFailAlloc_2616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2615_ = leanh::lean_apply_2(
                    v_inst_2603_,
                    leanh::lean_box(0),
                    v___x_2614_,
                );
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg(
    mut v_inst_2618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_n(v_inst_2618_, 2);
    v___f_2619_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    leanh::lean_closure_set(v___f_2619_, 0, v_inst_2618_);
    v___x_2620_ =
        leanh::lean_alloc_closure(l_Lake_EStateT_get as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___x_2620_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2620_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2620_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2620_, 3, v_inst_2618_);
    v___x_2621_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_set___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    leanh::lean_closure_set(v___x_2621_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2621_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2621_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2621_, 3, v_inst_2618_);
    v___x_2622_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2622_, 0, v___x_2620_);
    leanh::lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    leanh::lean_ctor_set(v___x_2622_, 2, v___f_2619_);
    return v___x_2622_;
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure(
    mut v_00_u03b5_2623_: *mut leanh::LeanObject,
    mut v_00_u03c3_2624_: *mut leanh::LeanObject,
    mut v_m_2625_: *mut leanh::LeanObject,
    mut v_inst_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2627_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Lake_EStateT_throw___redArg(
    mut v_inst_2628_: *mut leanh::LeanObject,
    mut v_e_2629_: *mut leanh::LeanObject,
    mut v_s_2630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2631_, 0, v_e_2629_);
    leanh::lean_ctor_set(v___x_2631_, 1, v_s_2630_);
    v___x_2632_ = leanh::lean_apply_2(v_inst_2628_, leanh::lean_box(0), v___x_2631_);
    return v___x_2632_;
}
pub unsafe fn l_Lake_EStateT_throw(
    mut v_00_u03b5_2633_: *mut leanh::LeanObject,
    mut v_00_u03c3_2634_: *mut leanh::LeanObject,
    mut v_00_u03b1_2635_: *mut leanh::LeanObject,
    mut v_m_2636_: *mut leanh::LeanObject,
    mut v_inst_2637_: *mut leanh::LeanObject,
    mut v_e_2638_: *mut leanh::LeanObject,
    mut v_s_2639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2640_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2640_, 0, v_e_2638_);
    leanh::lean_ctor_set(v___x_2640_, 1, v_s_2639_);
    v___x_2641_ = leanh::lean_apply_2(v_inst_2637_, leanh::lean_box(0), v___x_2640_);
    return v___x_2641_;
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg___lam__0(
    mut v_toPure_2642_: *mut leanh::LeanObject,
    mut v_handle_2643_: *mut leanh::LeanObject,
    mut v_____do__lift_2644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2644_) == 0 {
        let mut v___x_2645_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_handle_2643_);
        v___x_2645_ = leanh::lean_apply_2(
            v_toPure_2642_,
            leanh::lean_box(0),
            v_____do__lift_2644_,
        );
        return v___x_2645_;
    } else {
        let mut v_a_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2647_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2642_);
        v_a_2646_ = leanh::lean_ctor_get(v_____do__lift_2644_, 0);
        leanh::lean_inc(v_a_2646_);
        v_a_2647_ = leanh::lean_ctor_get(v_____do__lift_2644_, 1);
        leanh::lean_inc(v_a_2647_);
        leanh::lean_dec_ref_known(v_____do__lift_2644_, 2);
        v___x_2648_ = leanh::lean_apply_2(v_handle_2643_, v_a_2646_, v_a_2647_);
        return v___x_2648_;
    }
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg(
    mut v_inst_2649_: *mut leanh::LeanObject,
    mut v_x_2650_: *mut leanh::LeanObject,
    mut v_handle_2651_: *mut leanh::LeanObject,
    mut v_s_2652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2653_ = leanh::lean_ctor_get(v_inst_2649_, 0);
    leanh::lean_inc_ref(v_toApplicative_2653_);
    v_toBind_2654_ = leanh::lean_ctor_get(v_inst_2649_, 1);
    leanh::lean_inc(v_toBind_2654_);
    leanh::lean_dec_ref(v_inst_2649_);
    v_toPure_2655_ = leanh::lean_ctor_get(v_toApplicative_2653_, 1);
    leanh::lean_inc(v_toPure_2655_);
    leanh::lean_dec_ref(v_toApplicative_2653_);
    v___x_2656_ = leanh::lean_apply_1(v_x_2650_, v_s_2652_);
    v___f_2657_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2657_, 0, v_toPure_2655_);
    leanh::lean_closure_set(v___f_2657_, 1, v_handle_2651_);
    v___x_2658_ = leanh::lean_apply_4(
        v_toBind_2654_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2656_,
        v___f_2657_,
    );
    return v___x_2658_;
}
pub unsafe fn l_Lake_EStateT_tryCatch(
    mut v_00_u03b5_2659_: *mut leanh::LeanObject,
    mut v_00_u03c3_2660_: *mut leanh::LeanObject,
    mut v_00_u03b1_2661_: *mut leanh::LeanObject,
    mut v_m_2662_: *mut leanh::LeanObject,
    mut v_inst_2663_: *mut leanh::LeanObject,
    mut v_x_2664_: *mut leanh::LeanObject,
    mut v_handle_2665_: *mut leanh::LeanObject,
    mut v_s_2666_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2667_ = leanh::lean_ctor_get(v_inst_2663_, 0);
    leanh::lean_inc_ref(v_toApplicative_2667_);
    v_toBind_2668_ = leanh::lean_ctor_get(v_inst_2663_, 1);
    leanh::lean_inc(v_toBind_2668_);
    leanh::lean_dec_ref(v_inst_2663_);
    v_toPure_2669_ = leanh::lean_ctor_get(v_toApplicative_2667_, 1);
    leanh::lean_inc(v_toPure_2669_);
    leanh::lean_dec_ref(v_toApplicative_2667_);
    v___x_2670_ = leanh::lean_apply_1(v_x_2664_, v_s_2666_);
    v___f_2671_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2671_, 0, v_toPure_2669_);
    leanh::lean_closure_set(v___f_2671_, 1, v_handle_2665_);
    v___x_2672_ = leanh::lean_apply_4(
        v_toBind_2668_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2670_,
        v___f_2671_,
    );
    return v___x_2672_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(
    mut v_toPure_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v_____do__lift_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2675_) == 0 {
        let mut v___x_2676_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___y_2674_);
        v___x_2676_ = leanh::lean_apply_2(
            v_toPure_2673_,
            leanh::lean_box(0),
            v_____do__lift_2675_,
        );
        return v___x_2676_;
    } else {
        let mut v_a_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2678_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2673_);
        v_a_2677_ = leanh::lean_ctor_get(v_____do__lift_2675_, 0);
        leanh::lean_inc(v_a_2677_);
        v_a_2678_ = leanh::lean_ctor_get(v_____do__lift_2675_, 1);
        leanh::lean_inc(v_a_2678_);
        leanh::lean_dec_ref_known(v_____do__lift_2675_, 2);
        v___x_2679_ = leanh::lean_apply_2(v___y_2674_, v_a_2677_, v_a_2678_);
        return v___x_2679_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(
    mut v_toPure_2680_: *mut leanh::LeanObject,
    mut v_toBind_2681_: *mut leanh::LeanObject,
    mut v_00_u03b1_2682_: *mut leanh::LeanObject,
    mut v___y_2683_: *mut leanh::LeanObject,
    mut v___y_2684_: *mut leanh::LeanObject,
    mut v___y_2685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2686_ = leanh::lean_apply_1(v___y_2683_, v___y_2685_);
    v___f_2687_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2687_, 0, v_toPure_2680_);
    leanh::lean_closure_set(v___f_2687_, 1, v___y_2684_);
    v___x_2688_ = leanh::lean_apply_4(
        v_toBind_2681_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2686_,
        v___f_2687_,
    );
    return v___x_2688_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(
    mut v_toPure_2689_: *mut leanh::LeanObject,
    mut v_00_u03b1_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2693_, 0, v___y_2691_);
    leanh::lean_ctor_set(v___x_2693_, 1, v___y_2692_);
    v___x_2694_ =
        leanh::lean_apply_2(v_toPure_2689_, leanh::lean_box(0), v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(
    mut v_inst_2695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v_toPure_2701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2696_ = leanh::lean_ctor_get(v_inst_2695_, 0);
                v_toBind_2697_ = leanh::lean_ctor_get(v_inst_2695_, 1);
                v_isSharedCheck_2707_ = (!leanh::lean_is_exclusive(v_inst_2695_)) as u8;
                if v_isSharedCheck_2707_ == 0 {
                    v___x_2699_ = v_inst_2695_;
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_2697_);
                    leanh::lean_inc(v_toApplicative_2696_);
                    leanh::lean_dec(v_inst_2695_);
                    v___x_2699_ = leanh::lean_box(0);
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_2701_ = leanh::lean_ctor_get(v_toApplicative_2696_, 1);
                leanh::lean_inc_n(v_toPure_2701_, 2);
                leanh::lean_dec_ref(v_toApplicative_2696_);
                v___f_2702_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    2,
                );
                leanh::lean_closure_set(v___f_2702_, 0, v_toPure_2701_);
                leanh::lean_closure_set(v___f_2702_, 1, v_toBind_2697_);
                v___f_2703_ = leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___f_2703_, 0, v_toPure_2701_);
                if v_isShared_2700_ == 0 {
                    leanh::lean_ctor_set(v___x_2699_, 1, v___f_2702_);
                    leanh::lean_ctor_set(v___x_2699_, 0, v___f_2703_);
                    v___x_2705_ = v___x_2699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___f_2703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___f_2702_);
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
    mut v_00_u03b5_2708_: *mut leanh::LeanObject,
    mut v_00_u03c3_2709_: *mut leanh::LeanObject,
    mut v_m_2710_: *mut leanh::LeanObject,
    mut v_inst_2711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_2711_);
    return v___x_2712_;
}
pub unsafe fn l_Lake_EStateT_orElse___redArg___lam__0(
    mut v_toPure_2713_: *mut leanh::LeanObject,
    mut v_x_u2082_2714_: *mut leanh::LeanObject,
    mut v_____do__lift_2715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_____do__lift_2715_) == 0 {
        let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_x_u2082_2714_);
        v___x_2716_ = leanh::lean_apply_2(
            v_toPure_2713_,
            leanh::lean_box(0),
            v_____do__lift_2715_,
        );
        return v___x_2716_;
    } else {
        let mut v_a_2717_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_toPure_2713_);
        v_a_2717_ = leanh::lean_ctor_get(v_____do__lift_2715_, 1);
        leanh::lean_inc(v_a_2717_);
        leanh::lean_dec_ref_known(v_____do__lift_2715_, 2);
        v___x_2718_ = leanh::lean_box(0);
        v___x_2719_ = leanh::lean_apply_2(v_x_u2082_2714_, v___x_2718_, v_a_2717_);
        return v___x_2719_;
    }
}
pub unsafe fn l_Lake_EStateT_orElse___redArg(
    mut v_inst_2720_: *mut leanh::LeanObject,
    mut v_x_u2081_2721_: *mut leanh::LeanObject,
    mut v_x_u2082_2722_: *mut leanh::LeanObject,
    mut v_s_2723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2724_ = leanh::lean_ctor_get(v_inst_2720_, 0);
    leanh::lean_inc_ref(v_toApplicative_2724_);
    v_toBind_2725_ = leanh::lean_ctor_get(v_inst_2720_, 1);
    leanh::lean_inc(v_toBind_2725_);
    leanh::lean_dec_ref(v_inst_2720_);
    v_toPure_2726_ = leanh::lean_ctor_get(v_toApplicative_2724_, 1);
    leanh::lean_inc(v_toPure_2726_);
    leanh::lean_dec_ref(v_toApplicative_2724_);
    v___x_2727_ = leanh::lean_apply_1(v_x_u2081_2721_, v_s_2723_);
    v___f_2728_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2728_, 0, v_toPure_2726_);
    leanh::lean_closure_set(v___f_2728_, 1, v_x_u2082_2722_);
    v___x_2729_ = leanh::lean_apply_4(
        v_toBind_2725_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2727_,
        v___f_2728_,
    );
    return v___x_2729_;
}
pub unsafe fn l_Lake_EStateT_orElse(
    mut v_00_u03b5_2730_: *mut leanh::LeanObject,
    mut v_00_u03c3_2731_: *mut leanh::LeanObject,
    mut v_00_u03b1_2732_: *mut leanh::LeanObject,
    mut v_m_2733_: *mut leanh::LeanObject,
    mut v_inst_2734_: *mut leanh::LeanObject,
    mut v_x_u2081_2735_: *mut leanh::LeanObject,
    mut v_x_u2082_2736_: *mut leanh::LeanObject,
    mut v_s_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2738_ = leanh::lean_ctor_get(v_inst_2734_, 0);
    leanh::lean_inc_ref(v_toApplicative_2738_);
    v_toBind_2739_ = leanh::lean_ctor_get(v_inst_2734_, 1);
    leanh::lean_inc(v_toBind_2739_);
    leanh::lean_dec_ref(v_inst_2734_);
    v_toPure_2740_ = leanh::lean_ctor_get(v_toApplicative_2738_, 1);
    leanh::lean_inc(v_toPure_2740_);
    leanh::lean_dec_ref(v_toApplicative_2738_);
    v___x_2741_ = leanh::lean_apply_1(v_x_u2081_2735_, v_s_2737_);
    v___f_2742_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_2742_, 0, v_toPure_2740_);
    leanh::lean_closure_set(v___f_2742_, 1, v_x_u2082_2736_);
    v___x_2743_ = leanh::lean_apply_4(
        v_toBind_2739_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2741_,
        v___f_2742_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad___redArg(
    mut v_inst_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ =
        leanh::lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    leanh::lean_closure_set(v___x_2745_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2745_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2745_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2745_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2745_, 4, v_inst_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad(
    mut v_00_u03b5_2746_: *mut leanh::LeanObject,
    mut v_00_u03c3_2747_: *mut leanh::LeanObject,
    mut v_00_u03b1_2748_: *mut leanh::LeanObject,
    mut v_m_2749_: *mut leanh::LeanObject,
    mut v_inst_2750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ =
        leanh::lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    leanh::lean_closure_set(v___x_2751_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2751_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2751_, 2, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2751_, 3, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_2751_, 4, v_inst_2750_);
    return v___x_2751_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept___redArg___lam__0(
    mut v_f_2752_: *mut leanh::LeanObject,
    mut v_x_2753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_2753_) == 0 {
                    leanh::lean_dec(v_f_2752_);
                    v_a_2754_ = leanh::lean_ctor_get(v_x_2753_, 0);
                    v_a_2755_ = leanh::lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2762_ = (!leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v_x_2753_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2755_);
                        leanh::lean_inc(v_a_2754_);
                        leanh::lean_dec(v_x_2753_);
                        v___x_2757_ = leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2763_ = leanh::lean_ctor_get(v_x_2753_, 0);
                    v_a_2764_ = leanh::lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2772_ = (!leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2772_ == 0 {
                        v___x_2766_ = v_x_2753_;
                        v_isShared_2767_ = v_isSharedCheck_2772_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2764_);
                        leanh::lean_inc(v_a_2763_);
                        leanh::lean_dec(v_x_2753_);
                        v___x_2766_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_2761_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2760_;
            }
            3 => {
                v___x_2768_ = leanh::lean_apply_1(v_f_2752_, v_a_2763_);
                if v_isShared_2767_ == 0 {
                    leanh::lean_ctor_set(v___x_2766_, 0, v___x_2768_);
                    v___x_2770_ = v___x_2766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_a_2764_);
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
    mut v_inst_2773_: *mut leanh::LeanObject,
    mut v_f_2774_: *mut leanh::LeanObject,
    mut v_x_2775_: *mut leanh::LeanObject,
    mut v_s_2776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2777_ = leanh::lean_ctor_get(v_inst_2773_, 0);
    leanh::lean_inc(v_map_2777_);
    leanh::lean_dec_ref(v_inst_2773_);
    v___f_2778_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2778_, 0, v_f_2774_);
    v___x_2779_ = leanh::lean_apply_1(v_x_2775_, v_s_2776_);
    v___x_2780_ = leanh::lean_apply_4(
        v_map_2777_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2778_,
        v___x_2779_,
    );
    return v___x_2780_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept(
    mut v_00_u03b5_2781_: *mut leanh::LeanObject,
    mut v_00_u03b5_x27_2782_: *mut leanh::LeanObject,
    mut v_00_u03c3_2783_: *mut leanh::LeanObject,
    mut v_00_u03b1_2784_: *mut leanh::LeanObject,
    mut v_m_2785_: *mut leanh::LeanObject,
    mut v_inst_2786_: *mut leanh::LeanObject,
    mut v_f_2787_: *mut leanh::LeanObject,
    mut v_x_2788_: *mut leanh::LeanObject,
    mut v_s_2789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_map_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_map_2790_ = leanh::lean_ctor_get(v_inst_2786_, 0);
    leanh::lean_inc(v_map_2790_);
    leanh::lean_dec_ref(v_inst_2786_);
    v___f_2791_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2791_, 0, v_f_2787_);
    v___x_2792_ = leanh::lean_apply_1(v_x_2788_, v_s_2789_);
    v___x_2793_ = leanh::lean_apply_4(
        v_map_2790_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_2791_,
        v___x_2792_,
    );
    return v___x_2793_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__0(
    mut v_a_2794_: *mut leanh::LeanObject,
    mut v_toPure_2795_: *mut leanh::LeanObject,
    mut v_____do__lift_2796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_a_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2796_) == 0 {
                    v_a_2797_ = leanh::lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2798_ = leanh::lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2807_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2807_ == 0 {
                        v___x_2800_ = v_____do__lift_2796_;
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2798_);
                        leanh::lean_inc(v_a_2797_);
                        leanh::lean_dec(v_____do__lift_2796_);
                        v___x_2800_ = leanh::lean_box(0);
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2794_);
                    v_a_2808_ = leanh::lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2809_ = leanh::lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2817_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2811_ = v_____do__lift_2796_;
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2809_);
                        leanh::lean_inc(v_a_2808_);
                        leanh::lean_dec(v_____do__lift_2796_);
                        v___x_2811_ = leanh::lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2802_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2802_, 0, v_a_2794_);
                leanh::lean_ctor_set(v___x_2802_, 1, v_a_2797_);
                if v_isShared_2801_ == 0 {
                    leanh::lean_ctor_set(v___x_2800_, 0, v___x_2802_);
                    v___x_2804_ = v___x_2800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2802_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2798_);
                    v___x_2804_ = v_reuseFailAlloc_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2805_ = leanh::lean_apply_2(
                    v_toPure_2795_,
                    leanh::lean_box(0),
                    v___x_2804_,
                );
                return v___x_2805_;
            }
            3 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2808_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2815_ = leanh::lean_apply_2(
                    v_toPure_2795_,
                    leanh::lean_box(0),
                    v___x_2814_,
                );
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__1(
    mut v_a_2818_: *mut leanh::LeanObject,
    mut v_toPure_2819_: *mut leanh::LeanObject,
    mut v_____do__lift_2820_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_____do__lift_2820_) == 0 {
                    v_a_2821_ = leanh::lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2829_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v_unused_2830_ = leanh::lean_ctor_get(v_____do__lift_2820_, 0);
                        leanh::lean_dec(v_unused_2830_);
                        v___x_2823_ = v_____do__lift_2820_;
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2821_);
                        leanh::lean_dec(v_____do__lift_2820_);
                        v___x_2823_ = leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_2818_);
                    v_a_2831_ = leanh::lean_ctor_get(v_____do__lift_2820_, 0);
                    v_a_2832_ = leanh::lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2840_ =
                        (!leanh::lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2834_ = v_____do__lift_2820_;
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2832_);
                        leanh::lean_inc(v_a_2831_);
                        leanh::lean_dec(v_____do__lift_2820_);
                        v___x_2834_ = leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2824_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2823_, 1);
                    leanh::lean_ctor_set(v___x_2823_, 0, v_a_2818_);
                    v___x_2826_ = v___x_2823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2818_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_a_2821_);
                    v___x_2826_ = v_reuseFailAlloc_2828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2827_ = leanh::lean_apply_2(
                    v_toPure_2819_,
                    leanh::lean_box(0),
                    v___x_2826_,
                );
                return v___x_2827_;
            }
            3 => {
                if v_isShared_2835_ == 0 {
                    v___x_2837_ = v___x_2834_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2839_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2831_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_a_2832_);
                    v___x_2837_ = v_reuseFailAlloc_2839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2838_ = leanh::lean_apply_2(
                    v_toPure_2819_,
                    leanh::lean_box(0),
                    v___x_2837_,
                );
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__2(
    mut v_toPure_2841_: *mut leanh::LeanObject,
    mut v_f_2842_: *mut leanh::LeanObject,
    mut v_toBind_2843_: *mut leanh::LeanObject,
    mut v_r_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_2844_) == 0 {
        let mut v_a_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2850_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2845_ = leanh::lean_ctor_get(v_r_2844_, 0);
        leanh::lean_inc_n(v_a_2845_, 2);
        v_a_2846_ = leanh::lean_ctor_get(v_r_2844_, 1);
        leanh::lean_inc(v_a_2846_);
        leanh::lean_dec_ref_known(v_r_2844_, 2);
        v___f_2847_ = leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_2847_, 0, v_a_2845_);
        leanh::lean_closure_set(v___f_2847_, 1, v_toPure_2841_);
        v___x_2848_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2848_, 0, v_a_2845_);
        v___x_2849_ = leanh::lean_apply_2(v_f_2842_, v___x_2848_, v_a_2846_);
        v___x_2850_ = leanh::lean_apply_4(
            v_toBind_2843_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2849_,
            v___f_2847_,
        );
        return v___x_2850_;
    } else {
        let mut v_a_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2853_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2851_ = leanh::lean_ctor_get(v_r_2844_, 0);
        leanh::lean_inc(v_a_2851_);
        v_a_2852_ = leanh::lean_ctor_get(v_r_2844_, 1);
        leanh::lean_inc(v_a_2852_);
        leanh::lean_dec_ref_known(v_r_2844_, 2);
        v___f_2853_ = leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_2853_, 0, v_a_2851_);
        leanh::lean_closure_set(v___f_2853_, 1, v_toPure_2841_);
        v___x_2854_ = leanh::lean_box(0);
        v___x_2855_ = leanh::lean_apply_2(v_f_2842_, v___x_2854_, v_a_2852_);
        v___x_2856_ = leanh::lean_apply_4(
            v_toBind_2843_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2855_,
            v___f_2853_,
        );
        return v___x_2856_;
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg(
    mut v_inst_2857_: *mut leanh::LeanObject,
    mut v_x_2858_: *mut leanh::LeanObject,
    mut v_f_2859_: *mut leanh::LeanObject,
    mut v_s_2860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2861_ = leanh::lean_ctor_get(v_inst_2857_, 0);
    leanh::lean_inc_ref(v_toApplicative_2861_);
    v_toBind_2862_ = leanh::lean_ctor_get(v_inst_2857_, 1);
    leanh::lean_inc_n(v_toBind_2862_, 2);
    leanh::lean_dec_ref(v_inst_2857_);
    v_toPure_2863_ = leanh::lean_ctor_get(v_toApplicative_2861_, 1);
    leanh::lean_inc(v_toPure_2863_);
    leanh::lean_dec_ref(v_toApplicative_2861_);
    v___x_2864_ = leanh::lean_apply_1(v_x_2858_, v_s_2860_);
    v___f_2865_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2865_, 0, v_toPure_2863_);
    leanh::lean_closure_set(v___f_2865_, 1, v_f_2859_);
    leanh::lean_closure_set(v___f_2865_, 2, v_toBind_2862_);
    v___x_2866_ = leanh::lean_apply_4(
        v_toBind_2862_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2864_,
        v___f_2865_,
    );
    return v___x_2866_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27(
    mut v_00_u03b5_2867_: *mut leanh::LeanObject,
    mut v_00_u03c3_2868_: *mut leanh::LeanObject,
    mut v_00_u03b1_2869_: *mut leanh::LeanObject,
    mut v_00_u03b2_2870_: *mut leanh::LeanObject,
    mut v_m_2871_: *mut leanh::LeanObject,
    mut v_inst_2872_: *mut leanh::LeanObject,
    mut v_x_2873_: *mut leanh::LeanObject,
    mut v_f_2874_: *mut leanh::LeanObject,
    mut v_s_2875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2876_ = leanh::lean_ctor_get(v_inst_2872_, 0);
    leanh::lean_inc_ref(v_toApplicative_2876_);
    v_toBind_2877_ = leanh::lean_ctor_get(v_inst_2872_, 1);
    leanh::lean_inc_n(v_toBind_2877_, 2);
    leanh::lean_dec_ref(v_inst_2872_);
    v_toPure_2878_ = leanh::lean_ctor_get(v_toApplicative_2876_, 1);
    leanh::lean_inc(v_toPure_2878_);
    leanh::lean_dec_ref(v_toApplicative_2876_);
    v___x_2879_ = leanh::lean_apply_1(v_x_2873_, v_s_2875_);
    v___f_2880_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2880_, 0, v_toPure_2878_);
    leanh::lean_closure_set(v___f_2880_, 1, v_f_2874_);
    leanh::lean_closure_set(v___f_2880_, 2, v_toBind_2877_);
    v___x_2881_ = leanh::lean_apply_4(
        v_toBind_2877_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2879_,
        v___f_2880_,
    );
    return v___x_2881_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(
    mut v_toPure_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v_toBind_2884_: *mut leanh::LeanObject,
    mut v_r_2885_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_r_2885_) == 0 {
        let mut v_a_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2887_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2889_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2886_ = leanh::lean_ctor_get(v_r_2885_, 0);
        leanh::lean_inc_n(v_a_2886_, 2);
        v_a_2887_ = leanh::lean_ctor_get(v_r_2885_, 1);
        leanh::lean_inc(v_a_2887_);
        leanh::lean_dec_ref_known(v_r_2885_, 2);
        v___f_2888_ = leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_2888_, 0, v_a_2886_);
        leanh::lean_closure_set(v___f_2888_, 1, v_toPure_2882_);
        v___x_2889_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2889_, 0, v_a_2886_);
        v___x_2890_ = leanh::lean_apply_2(v___y_2883_, v___x_2889_, v_a_2887_);
        v___x_2891_ = leanh::lean_apply_4(
            v_toBind_2884_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2890_,
            v___f_2888_,
        );
        return v___x_2891_;
    } else {
        let mut v_a_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_2892_ = leanh::lean_ctor_get(v_r_2885_, 0);
        leanh::lean_inc(v_a_2892_);
        v_a_2893_ = leanh::lean_ctor_get(v_r_2885_, 1);
        leanh::lean_inc(v_a_2893_);
        leanh::lean_dec_ref_known(v_r_2885_, 2);
        v___f_2894_ = leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_2894_, 0, v_a_2892_);
        leanh::lean_closure_set(v___f_2894_, 1, v_toPure_2882_);
        v___x_2895_ = leanh::lean_box(0);
        v___x_2896_ = leanh::lean_apply_2(v___y_2883_, v___x_2895_, v_a_2893_);
        v___x_2897_ = leanh::lean_apply_4(
            v_toBind_2884_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_2896_,
            v___f_2894_,
        );
        return v___x_2897_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(
    mut v_inst_2898_: *mut leanh::LeanObject,
    mut v_00_u03b1_2899_: *mut leanh::LeanObject,
    mut v_00_u03b2_2900_: *mut leanh::LeanObject,
    mut v___y_2901_: *mut leanh::LeanObject,
    mut v___y_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2904_ = leanh::lean_ctor_get(v_inst_2898_, 0);
    leanh::lean_inc_ref(v_toApplicative_2904_);
    v_toBind_2905_ = leanh::lean_ctor_get(v_inst_2898_, 1);
    leanh::lean_inc_n(v_toBind_2905_, 2);
    leanh::lean_dec_ref(v_inst_2898_);
    v_toPure_2906_ = leanh::lean_ctor_get(v_toApplicative_2904_, 1);
    leanh::lean_inc(v_toPure_2906_);
    leanh::lean_dec_ref(v_toApplicative_2904_);
    v___x_2907_ = leanh::lean_apply_1(v___y_2901_, v___y_2903_);
    v___f_2908_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_2908_, 0, v_toPure_2906_);
    leanh::lean_closure_set(v___f_2908_, 1, v___y_2902_);
    leanh::lean_closure_set(v___f_2908_, 2, v_toBind_2905_);
    v___x_2909_ = leanh::lean_apply_4(
        v_toBind_2905_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2907_,
        v___f_2908_,
    );
    return v___x_2909_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg(
    mut v_inst_2910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2911_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2911_, 0, v_inst_2910_);
    return v___f_2911_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad(
    mut v_00_u03b5_2912_: *mut leanh::LeanObject,
    mut v_00_u03c3_2913_: *mut leanh::LeanObject,
    mut v_m_2914_: *mut leanh::LeanObject,
    mut v_inst_2915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2916_ = leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_2916_, 0, v_inst_2915_);
    return v___f_2916_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM___redArg(
    mut v_f_2917_: *mut leanh::LeanObject,
    mut v_s_2918_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = leanh::lean_apply_1(v_f_2917_, v_s_2918_);
    v___x_2920_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_2919_);
    return v___x_2920_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM(
    mut v_00_u03b5_2921_: *mut leanh::LeanObject,
    mut v_00_u03c3_2922_: *mut leanh::LeanObject,
    mut v_00_u03b1_2923_: *mut leanh::LeanObject,
    mut v_f_2924_: *mut leanh::LeanObject,
    mut v_s_2925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lake_EStateT_ofEStateM___redArg(v_f_2924_, v_s_2925_);
    return v___x_2926_;
}
pub unsafe fn l_Lake_EStateT_toEStateM___redArg(
    mut v_f_2927_: *mut leanh::LeanObject,
    mut v_s_2928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = leanh::lean_apply_1(v_f_2927_, v_s_2928_);
    v___x_2930_ = l_Lake_EResult_toEStateMResult___redArg(v___x_2929_);
    return v___x_2930_;
}
pub unsafe fn l_Lake_EStateT_toEStateM(
    mut v_00_u03b5_2931_: *mut leanh::LeanObject,
    mut v_00_u03c3_2932_: *mut leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut leanh::LeanObject,
    mut v_f_2934_: *mut leanh::LeanObject,
    mut v_s_2935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Lake_EStateT_toEStateM___redArg(v_f_2934_, v_s_2935_);
    return v___x_2936_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_EStateT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_EStateT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_EStateT(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_State(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_EStateT(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_EStateT(builtin);
}
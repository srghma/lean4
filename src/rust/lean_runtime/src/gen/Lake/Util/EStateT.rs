// Lean compiler output
// Module: Lake.Util.EStateT
// Imports: Init.Control.State
use crate::r#gen::Init::Control::State::{
    initialize_Init_Control_State, runtime_initialize_Init_Control_State,
};
use crate::r#gen::Init::Prelude::l_Function_const___boxed;
pub static l_Lake_EResult_instFunctor___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_instFunctor___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_EResult_instFunctor___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EResult_instFunctor___closed__1_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_instFunctor___lam__1 as *const core::ffi::c_void,
        m_arity: 5,
        m_num_fixed: 1,
        m_objs: [
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_EResult_instFunctor___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EResult_instFunctor___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_EResult_instFunctor___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EResult_instFunctor___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EStateT_run_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toExcept___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_EStateT_run_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EStateT_toStateT___redArg___closed__0_value: crate::leanh::LeanClosureObject<3> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_EResult_toProd as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 3,
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lake_EStateT_toStateT___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_toProd_x3f as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_EStateT_toStateT_x3f___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_toStateT_x3f___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value: crate::leanh::LeanClosureObject<
    3,
> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_EResult_result_x3f___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 3,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lake_EStateT_run_x3f_x27___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_EStateT_run_x3f_x27___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_EResult_ctorIdx___redArg(
    mut v_x_1469_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1469_) == 0 {
        let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1470_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_1470_;
    } else {
        let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1471_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1471_;
    }
}
pub unsafe fn l_Lake_EResult_ctorIdx___redArg___boxed(
    mut v_x_1472_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1473_ = l_Lake_EResult_ctorIdx___redArg(v_x_1472_);
    crate::leanh::lean_dec_ref(v_x_1472_);
    return v_res_1473_;
}
pub unsafe fn l_Lake_EResult_ctorIdx(
    mut v_00_u03b5_1474_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1475_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1476_: *mut crate::leanh::LeanObject,
    mut v_x_1477_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1478_ = l_Lake_EResult_ctorIdx___redArg(v_x_1477_);
    return v___x_1478_;
}
pub unsafe fn l_Lake_EResult_ctorIdx___boxed(
    mut v_00_u03b5_1479_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1480_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1481_: *mut crate::leanh::LeanObject,
    mut v_x_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1483_ = l_Lake_EResult_ctorIdx(
        v_00_u03b5_1479_,
        v_00_u03c3_1480_,
        v_00_u03b1_1481_,
        v_x_1482_,
    );
    crate::leanh::lean_dec_ref(v_x_1482_);
    return v_res_1483_;
}
pub unsafe fn l_Lake_EResult_ctorElim___redArg(
    mut v_t_1484_: *mut crate::leanh::LeanObject,
    mut v_k_1485_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1486_ = crate::leanh::lean_ctor_get(v_t_1484_, 0);
    crate::leanh::lean_inc(v_a_1486_);
    v_a_1487_ = crate::leanh::lean_ctor_get(v_t_1484_, 1);
    crate::leanh::lean_inc(v_a_1487_);
    crate::leanh::lean_dec_ref(v_t_1484_);
    v___x_1488_ = crate::leanh::lean_apply_2(v_k_1485_, v_a_1486_, v_a_1487_);
    return v___x_1488_;
}
pub unsafe fn l_Lake_EResult_ctorElim(
    mut v_00_u03b5_1489_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1490_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1491_: *mut crate::leanh::LeanObject,
    mut v_motive_1492_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1493_: *mut crate::leanh::LeanObject,
    mut v_t_1494_: *mut crate::leanh::LeanObject,
    mut v_h_1495_: *mut crate::leanh::LeanObject,
    mut v_k_1496_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1497_ = l_Lake_EResult_ctorElim___redArg(v_t_1494_, v_k_1496_);
    return v___x_1497_;
}
pub unsafe fn l_Lake_EResult_ctorElim___boxed(
    mut v_00_u03b5_1498_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1499_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1500_: *mut crate::leanh::LeanObject,
    mut v_motive_1501_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_1502_: *mut crate::leanh::LeanObject,
    mut v_t_1503_: *mut crate::leanh::LeanObject,
    mut v_h_1504_: *mut crate::leanh::LeanObject,
    mut v_k_1505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_ctorIdx_1502_);
    return v_res_1506_;
}
pub unsafe fn l_Lake_EResult_ok_elim___redArg(
    mut v_t_1507_: *mut crate::leanh::LeanObject,
    mut v_ok_1508_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1509_ = l_Lake_EResult_ctorElim___redArg(v_t_1507_, v_ok_1508_);
    return v___x_1509_;
}
pub unsafe fn l_Lake_EResult_ok_elim(
    mut v_00_u03b5_1510_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1511_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1512_: *mut crate::leanh::LeanObject,
    mut v_motive_1513_: *mut crate::leanh::LeanObject,
    mut v_t_1514_: *mut crate::leanh::LeanObject,
    mut v_h_1515_: *mut crate::leanh::LeanObject,
    mut v_ok_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_Lake_EResult_ctorElim___redArg(v_t_1514_, v_ok_1516_);
    return v___x_1517_;
}
pub unsafe fn l_Lake_EResult_error_elim___redArg(
    mut v_t_1518_: *mut crate::leanh::LeanObject,
    mut v_error_1519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = l_Lake_EResult_ctorElim___redArg(v_t_1518_, v_error_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Lake_EResult_error_elim(
    mut v_00_u03b5_1521_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1522_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1523_: *mut crate::leanh::LeanObject,
    mut v_motive_1524_: *mut crate::leanh::LeanObject,
    mut v_t_1525_: *mut crate::leanh::LeanObject,
    mut v_h_1526_: *mut crate::leanh::LeanObject,
    mut v_error_1527_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1528_ = l_Lake_EResult_ctorElim___redArg(v_t_1525_, v_error_1527_);
    return v___x_1528_;
}
pub unsafe fn l_Lake_EResult_instInhabited___redArg(
    mut v_inst_1529_: *mut crate::leanh::LeanObject,
    mut v_inst_1530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1531_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1531_, 0, v_inst_1529_);
    crate::leanh::lean_ctor_set(v___x_1531_, 1, v_inst_1530_);
    return v___x_1531_;
}
pub unsafe fn l_Lake_EResult_instInhabited(
    mut v_00_u03b1_1532_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1533_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1534_: *mut crate::leanh::LeanObject,
    mut v_inst_1535_: *mut crate::leanh::LeanObject,
    mut v_inst_1536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1537_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1537_, 0, v_inst_1535_);
    crate::leanh::lean_ctor_set(v___x_1537_, 1, v_inst_1536_);
    return v___x_1537_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1___redArg(
    mut v_inst_1538_: *mut crate::leanh::LeanObject,
    mut v_inst_1539_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1540_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1540_, 0, v_inst_1538_);
    crate::leanh::lean_ctor_set(v___x_1540_, 1, v_inst_1539_);
    return v___x_1540_;
}
pub unsafe fn l_Lake_EResult_instInhabited__1(
    mut v_00_u03b5_1541_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1542_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1543_: *mut crate::leanh::LeanObject,
    mut v_inst_1544_: *mut crate::leanh::LeanObject,
    mut v_inst_1545_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1546_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1546_, 0, v_inst_1544_);
    crate::leanh::lean_ctor_set(v___x_1546_, 1, v_inst_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lake_EResult_state___redArg(
    mut v_x_1547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1548_ = crate::leanh::lean_ctor_get(v_x_1547_, 1);
    crate::leanh::lean_inc(v_a_1548_);
    return v_a_1548_;
}
pub unsafe fn l_Lake_EResult_state___redArg___boxed(
    mut v_x_1549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1550_ = l_Lake_EResult_state___redArg(v_x_1549_);
    crate::leanh::lean_dec_ref(v_x_1549_);
    return v_res_1550_;
}
pub unsafe fn l_Lake_EResult_state(
    mut v_00_u03b5_1551_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1552_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1553_: *mut crate::leanh::LeanObject,
    mut v_x_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_a_1555_ = crate::leanh::lean_ctor_get(v_x_1554_, 1);
    crate::leanh::lean_inc(v_a_1555_);
    return v_a_1555_;
}
pub unsafe fn l_Lake_EResult_state___boxed(
    mut v_00_u03b5_1556_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1557_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1558_: *mut crate::leanh::LeanObject,
    mut v_x_1559_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1560_ = l_Lake_EResult_state(
        v_00_u03b5_1556_,
        v_00_u03c3_1557_,
        v_00_u03b1_1558_,
        v_x_1559_,
    );
    crate::leanh::lean_dec_ref(v_x_1559_);
    return v_res_1560_;
}
pub unsafe fn l_Lake_EResult_modifyState___redArg(
    mut v_f_1561_: *mut crate::leanh::LeanObject,
    mut v_x_1562_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1572_: u8 = 0;
    let mut v_a_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1577_: u8 = 0;
    let mut v___x_1578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1582_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1562_) == 0 {
                    v_a_1563_ = crate::leanh::lean_ctor_get(v_x_1562_, 0);
                    v_a_1564_ = crate::leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1572_ = (!crate::leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1572_ == 0 {
                        v___x_1566_ = v_x_1562_;
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1564_);
                        crate::leanh::lean_inc(v_a_1563_);
                        crate::leanh::lean_dec(v_x_1562_);
                        v___x_1566_ = crate::leanh::lean_box(0);
                        v_isShared_1567_ = v_isSharedCheck_1572_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1573_ = crate::leanh::lean_ctor_get(v_x_1562_, 0);
                    v_a_1574_ = crate::leanh::lean_ctor_get(v_x_1562_, 1);
                    v_isSharedCheck_1582_ = (!crate::leanh::lean_is_exclusive(v_x_1562_)) as u8;
                    if v_isSharedCheck_1582_ == 0 {
                        v___x_1576_ = v_x_1562_;
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1574_);
                        crate::leanh::lean_inc(v_a_1573_);
                        crate::leanh::lean_dec(v_x_1562_);
                        v___x_1576_ = crate::leanh::lean_box(0);
                        v_isShared_1577_ = v_isSharedCheck_1582_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1568_ = crate::leanh::lean_apply_1(v_f_1561_, v_a_1564_);
                if v_isShared_1567_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1566_, 1, v___x_1568_);
                    v___x_1570_ = v___x_1566_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1571_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 0, v_a_1563_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1571_, 1, v___x_1568_);
                    v___x_1570_ = v_reuseFailAlloc_1571_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1570_;
            }
            3 => {
                v___x_1578_ = crate::leanh::lean_apply_1(v_f_1561_, v_a_1574_);
                if v_isShared_1577_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1576_, 1, v___x_1578_);
                    v___x_1580_ = v___x_1576_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1581_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_a_1573_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
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
    mut v_00_u03c3_1583_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_x27_1584_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1585_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1586_: *mut crate::leanh::LeanObject,
    mut v_f_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1593_: u8 = 0;
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1598_: u8 = 0;
    let mut v_a_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1603_: u8 = 0;
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1608_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1588_) == 0 {
                    v_a_1589_ = crate::leanh::lean_ctor_get(v_x_1588_, 0);
                    v_a_1590_ = crate::leanh::lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1598_ = (!crate::leanh::lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1598_ == 0 {
                        v___x_1592_ = v_x_1588_;
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1590_);
                        crate::leanh::lean_inc(v_a_1589_);
                        crate::leanh::lean_dec(v_x_1588_);
                        v___x_1592_ = crate::leanh::lean_box(0);
                        v_isShared_1593_ = v_isSharedCheck_1598_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1599_ = crate::leanh::lean_ctor_get(v_x_1588_, 0);
                    v_a_1600_ = crate::leanh::lean_ctor_get(v_x_1588_, 1);
                    v_isSharedCheck_1608_ = (!crate::leanh::lean_is_exclusive(v_x_1588_)) as u8;
                    if v_isSharedCheck_1608_ == 0 {
                        v___x_1602_ = v_x_1588_;
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1600_);
                        crate::leanh::lean_inc(v_a_1599_);
                        crate::leanh::lean_dec(v_x_1588_);
                        v___x_1602_ = crate::leanh::lean_box(0);
                        v_isShared_1603_ = v_isSharedCheck_1608_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1594_ = crate::leanh::lean_apply_1(v_f_1587_, v_a_1590_);
                if v_isShared_1593_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1592_, 1, v___x_1594_);
                    v___x_1596_ = v___x_1592_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1597_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 0, v_a_1589_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1597_, 1, v___x_1594_);
                    v___x_1596_ = v_reuseFailAlloc_1597_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1596_;
            }
            3 => {
                v___x_1604_ = crate::leanh::lean_apply_1(v_f_1587_, v_a_1600_);
                if v_isShared_1603_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1602_, 1, v___x_1604_);
                    v___x_1606_ = v___x_1602_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1607_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_a_1599_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
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
    mut v_s_1609_: *mut crate::leanh::LeanObject,
    mut v_r_1610_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1614_: u8 = 0;
    let mut v___x_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1618_: u8 = 0;
    let mut v_unused_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1623_: u8 = 0;
    let mut v___x_1625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1627_: u8 = 0;
    let mut v_unused_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_r_1610_) == 0 {
                    v_a_1611_ = crate::leanh::lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1618_ = (!crate::leanh::lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1618_ == 0 {
                        v_unused_1619_ = crate::leanh::lean_ctor_get(v_r_1610_, 1);
                        crate::leanh::lean_dec(v_unused_1619_);
                        v___x_1613_ = v_r_1610_;
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1611_);
                        crate::leanh::lean_dec(v_r_1610_);
                        v___x_1613_ = crate::leanh::lean_box(0);
                        v_isShared_1614_ = v_isSharedCheck_1618_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1620_ = crate::leanh::lean_ctor_get(v_r_1610_, 0);
                    v_isSharedCheck_1627_ = (!crate::leanh::lean_is_exclusive(v_r_1610_)) as u8;
                    if v_isSharedCheck_1627_ == 0 {
                        v_unused_1628_ = crate::leanh::lean_ctor_get(v_r_1610_, 1);
                        crate::leanh::lean_dec(v_unused_1628_);
                        v___x_1622_ = v_r_1610_;
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1620_);
                        crate::leanh::lean_dec(v_r_1610_);
                        v___x_1622_ = crate::leanh::lean_box(0);
                        v_isShared_1623_ = v_isSharedCheck_1627_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1613_, 1, v_s_1609_);
                    v___x_1616_ = v___x_1613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1617_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 0, v_a_1611_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1617_, 1, v_s_1609_);
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
                    crate::leanh::lean_ctor_set(v___x_1622_, 1, v_s_1609_);
                    v___x_1625_ = v___x_1622_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1626_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 0, v_a_1620_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1626_, 1, v_s_1609_);
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
    mut v_00_u03c3_x27_1629_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1630_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1631_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1632_: *mut crate::leanh::LeanObject,
    mut v_s_1633_: *mut crate::leanh::LeanObject,
    mut v_r_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1638_: u8 = 0;
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1642_: u8 = 0;
    let mut v_unused_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v___x_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1651_: u8 = 0;
    let mut v_unused_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_r_1634_) == 0 {
                    v_a_1635_ = crate::leanh::lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1642_ = (!crate::leanh::lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1642_ == 0 {
                        v_unused_1643_ = crate::leanh::lean_ctor_get(v_r_1634_, 1);
                        crate::leanh::lean_dec(v_unused_1643_);
                        v___x_1637_ = v_r_1634_;
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1635_);
                        crate::leanh::lean_dec(v_r_1634_);
                        v___x_1637_ = crate::leanh::lean_box(0);
                        v_isShared_1638_ = v_isSharedCheck_1642_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1644_ = crate::leanh::lean_ctor_get(v_r_1634_, 0);
                    v_isSharedCheck_1651_ = (!crate::leanh::lean_is_exclusive(v_r_1634_)) as u8;
                    if v_isSharedCheck_1651_ == 0 {
                        v_unused_1652_ = crate::leanh::lean_ctor_get(v_r_1634_, 1);
                        crate::leanh::lean_dec(v_unused_1652_);
                        v___x_1646_ = v_r_1634_;
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1644_);
                        crate::leanh::lean_dec(v_r_1634_);
                        v___x_1646_ = crate::leanh::lean_box(0);
                        v_isShared_1647_ = v_isSharedCheck_1651_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1637_, 1, v_s_1633_);
                    v___x_1640_ = v___x_1637_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1641_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_a_1635_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_s_1633_);
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
                    crate::leanh::lean_ctor_set(v___x_1646_, 1, v_s_1633_);
                    v___x_1649_ = v___x_1646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1650_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 0, v_a_1644_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1650_, 1, v_s_1633_);
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
    mut v_x_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1663_: u8 = 0;
    let mut v_a_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1668_: u8 = 0;
    let mut v___x_1669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1653_) == 0 {
                    v_a_1654_ = crate::leanh::lean_ctor_get(v_x_1653_, 0);
                    v_a_1655_ = crate::leanh::lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1663_ = (!crate::leanh::lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1663_ == 0 {
                        v___x_1657_ = v_x_1653_;
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1655_);
                        crate::leanh::lean_inc(v_a_1654_);
                        crate::leanh::lean_dec(v_x_1653_);
                        v___x_1657_ = crate::leanh::lean_box(0);
                        v_isShared_1658_ = v_isSharedCheck_1663_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1664_ = crate::leanh::lean_ctor_get(v_x_1653_, 0);
                    v_a_1665_ = crate::leanh::lean_ctor_get(v_x_1653_, 1);
                    v_isSharedCheck_1673_ = (!crate::leanh::lean_is_exclusive(v_x_1653_)) as u8;
                    if v_isSharedCheck_1673_ == 0 {
                        v___x_1667_ = v_x_1653_;
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1665_);
                        crate::leanh::lean_inc(v_a_1664_);
                        crate::leanh::lean_dec(v_x_1653_);
                        v___x_1667_ = crate::leanh::lean_box(0);
                        v_isShared_1668_ = v_isSharedCheck_1673_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1659_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1659_, 0, v_a_1654_);
                if v_isShared_1658_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1657_, 0, v___x_1659_);
                    v___x_1661_ = v___x_1657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1662_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1655_);
                    v___x_1661_ = v_reuseFailAlloc_1662_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1661_;
            }
            3 => {
                v___x_1669_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1669_, 0, v_a_1664_);
                if v_isShared_1668_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1667_, 0);
                    crate::leanh::lean_ctor_set(v___x_1667_, 0, v___x_1669_);
                    v___x_1671_ = v___x_1667_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1672_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 0, v___x_1669_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_a_1665_);
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
    mut v_00_u03b5_1674_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1675_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1676_: *mut crate::leanh::LeanObject,
    mut v_x_1677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1687_: u8 = 0;
    let mut v_a_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1692_: u8 = 0;
    let mut v___x_1693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1677_) == 0 {
                    v_a_1678_ = crate::leanh::lean_ctor_get(v_x_1677_, 0);
                    v_a_1679_ = crate::leanh::lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1687_ = (!crate::leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1687_ == 0 {
                        v___x_1681_ = v_x_1677_;
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1679_);
                        crate::leanh::lean_inc(v_a_1678_);
                        crate::leanh::lean_dec(v_x_1677_);
                        v___x_1681_ = crate::leanh::lean_box(0);
                        v_isShared_1682_ = v_isSharedCheck_1687_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1688_ = crate::leanh::lean_ctor_get(v_x_1677_, 0);
                    v_a_1689_ = crate::leanh::lean_ctor_get(v_x_1677_, 1);
                    v_isSharedCheck_1697_ = (!crate::leanh::lean_is_exclusive(v_x_1677_)) as u8;
                    if v_isSharedCheck_1697_ == 0 {
                        v___x_1691_ = v_x_1677_;
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1689_);
                        crate::leanh::lean_inc(v_a_1688_);
                        crate::leanh::lean_dec(v_x_1677_);
                        v___x_1691_ = crate::leanh::lean_box(0);
                        v_isShared_1692_ = v_isSharedCheck_1697_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1683_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1683_, 0, v_a_1678_);
                if v_isShared_1682_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1681_, 0, v___x_1683_);
                    v___x_1685_ = v___x_1681_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1686_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 0, v___x_1683_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1686_, 1, v_a_1679_);
                    v___x_1685_ = v_reuseFailAlloc_1686_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1685_;
            }
            3 => {
                v___x_1693_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1693_, 0, v_a_1688_);
                if v_isShared_1692_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1691_, 0);
                    crate::leanh::lean_ctor_set(v___x_1691_, 0, v___x_1693_);
                    v___x_1695_ = v___x_1691_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1696_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 0, v___x_1693_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_a_1689_);
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
    mut v_x_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1703_: u8 = 0;
    let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1708_: u8 = 0;
    let mut v_a_1709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1712_: u8 = 0;
    let mut v___x_1713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1717_: u8 = 0;
    let mut v_unused_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1698_) == 0 {
                    v_a_1699_ = crate::leanh::lean_ctor_get(v_x_1698_, 0);
                    v_a_1700_ = crate::leanh::lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1708_ = (!crate::leanh::lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1708_ == 0 {
                        v___x_1702_ = v_x_1698_;
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1700_);
                        crate::leanh::lean_inc(v_a_1699_);
                        crate::leanh::lean_dec(v_x_1698_);
                        v___x_1702_ = crate::leanh::lean_box(0);
                        v_isShared_1703_ = v_isSharedCheck_1708_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1709_ = crate::leanh::lean_ctor_get(v_x_1698_, 1);
                    v_isSharedCheck_1717_ = (!crate::leanh::lean_is_exclusive(v_x_1698_)) as u8;
                    if v_isSharedCheck_1717_ == 0 {
                        v_unused_1718_ = crate::leanh::lean_ctor_get(v_x_1698_, 0);
                        crate::leanh::lean_dec(v_unused_1718_);
                        v___x_1711_ = v_x_1698_;
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1709_);
                        crate::leanh::lean_dec(v_x_1698_);
                        v___x_1711_ = crate::leanh::lean_box(0);
                        v_isShared_1712_ = v_isSharedCheck_1717_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1704_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1704_, 0, v_a_1699_);
                if v_isShared_1703_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1702_, 0, v___x_1704_);
                    v___x_1706_ = v___x_1702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1707_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 0, v___x_1704_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1707_, 1, v_a_1700_);
                    v___x_1706_ = v_reuseFailAlloc_1707_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1706_;
            }
            3 => {
                v___x_1713_ = crate::leanh::lean_box(0);
                if v_isShared_1712_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1711_, 0);
                    crate::leanh::lean_ctor_set(v___x_1711_, 0, v___x_1713_);
                    v___x_1715_ = v___x_1711_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1716_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 0, v___x_1713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1716_, 1, v_a_1709_);
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
    mut v_00_u03b5_1719_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1720_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1721_: *mut crate::leanh::LeanObject,
    mut v_x_1722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1727_: u8 = 0;
    let mut v___x_1728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1736_: u8 = 0;
    let mut v___x_1737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut v_unused_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1722_) == 0 {
                    v_a_1723_ = crate::leanh::lean_ctor_get(v_x_1722_, 0);
                    v_a_1724_ = crate::leanh::lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1732_ = (!crate::leanh::lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1732_ == 0 {
                        v___x_1726_ = v_x_1722_;
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1724_);
                        crate::leanh::lean_inc(v_a_1723_);
                        crate::leanh::lean_dec(v_x_1722_);
                        v___x_1726_ = crate::leanh::lean_box(0);
                        v_isShared_1727_ = v_isSharedCheck_1732_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1733_ = crate::leanh::lean_ctor_get(v_x_1722_, 1);
                    v_isSharedCheck_1741_ = (!crate::leanh::lean_is_exclusive(v_x_1722_)) as u8;
                    if v_isSharedCheck_1741_ == 0 {
                        v_unused_1742_ = crate::leanh::lean_ctor_get(v_x_1722_, 0);
                        crate::leanh::lean_dec(v_unused_1742_);
                        v___x_1735_ = v_x_1722_;
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1733_);
                        crate::leanh::lean_dec(v_x_1722_);
                        v___x_1735_ = crate::leanh::lean_box(0);
                        v_isShared_1736_ = v_isSharedCheck_1741_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1728_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1728_, 0, v_a_1723_);
                if v_isShared_1727_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1726_, 0, v___x_1728_);
                    v___x_1730_ = v___x_1726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v___x_1728_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 1, v_a_1724_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1730_;
            }
            3 => {
                v___x_1737_ = crate::leanh::lean_box(0);
                if v_isShared_1736_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1735_, 0);
                    crate::leanh::lean_ctor_set(v___x_1735_, 0, v___x_1737_);
                    v___x_1739_ = v___x_1735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_a_1733_);
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
    mut v_x_1743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1743_) == 0 {
        let mut v_a_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1744_ = crate::leanh::lean_ctor_get(v_x_1743_, 0);
        crate::leanh::lean_inc(v_a_1744_);
        v___x_1745_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1745_, 0, v_a_1744_);
        return v___x_1745_;
    } else {
        let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1746_ = crate::leanh::lean_box(0);
        return v___x_1746_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___redArg___boxed(
    mut v_x_1747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1748_ = l_Lake_EResult_result_x3f___redArg(v_x_1747_);
    crate::leanh::lean_dec_ref(v_x_1747_);
    return v_res_1748_;
}
pub unsafe fn l_Lake_EResult_result_x3f(
    mut v_00_u03b5_1749_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1750_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1751_: *mut crate::leanh::LeanObject,
    mut v_x_1752_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1752_) == 0 {
        let mut v_a_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1753_ = crate::leanh::lean_ctor_get(v_x_1752_, 0);
        crate::leanh::lean_inc(v_a_1753_);
        v___x_1754_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1754_, 0, v_a_1753_);
        return v___x_1754_;
    } else {
        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1755_ = crate::leanh::lean_box(0);
        return v___x_1755_;
    }
}
pub unsafe fn l_Lake_EResult_result_x3f___boxed(
    mut v_00_u03b5_1756_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1757_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1758_: *mut crate::leanh::LeanObject,
    mut v_x_1759_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lake_EResult_result_x3f(
        v_00_u03b5_1756_,
        v_00_u03c3_1757_,
        v_00_u03b1_1758_,
        v_x_1759_,
    );
    crate::leanh::lean_dec_ref(v_x_1759_);
    return v_res_1760_;
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg(
    mut v_x_1761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1761_) == 0 {
        let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1762_ = crate::leanh::lean_box(0);
        return v___x_1762_;
    } else {
        let mut v_a_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1763_ = crate::leanh::lean_ctor_get(v_x_1761_, 0);
        crate::leanh::lean_inc(v_a_1763_);
        v___x_1764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1764_, 0, v_a_1763_);
        return v___x_1764_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___redArg___boxed(
    mut v_x_1765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lake_EResult_error_x3f___redArg(v_x_1765_);
    crate::leanh::lean_dec_ref(v_x_1765_);
    return v_res_1766_;
}
pub unsafe fn l_Lake_EResult_error_x3f(
    mut v_00_u03b5_1767_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1768_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1769_: *mut crate::leanh::LeanObject,
    mut v_x_1770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1770_) == 0 {
        let mut v___x_1771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1771_ = crate::leanh::lean_box(0);
        return v___x_1771_;
    } else {
        let mut v_a_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1772_ = crate::leanh::lean_ctor_get(v_x_1770_, 0);
        crate::leanh::lean_inc(v_a_1772_);
        v___x_1773_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1773_, 0, v_a_1772_);
        return v___x_1773_;
    }
}
pub unsafe fn l_Lake_EResult_error_x3f___boxed(
    mut v_00_u03b5_1774_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1775_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1776_: *mut crate::leanh::LeanObject,
    mut v_x_1777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1778_ = l_Lake_EResult_error_x3f(
        v_00_u03b5_1774_,
        v_00_u03c3_1775_,
        v_00_u03b1_1776_,
        v_x_1777_,
    );
    crate::leanh::lean_dec_ref(v_x_1777_);
    return v_res_1778_;
}
pub unsafe fn l_Lake_EResult_toExcept___redArg(
    mut v_x_1779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1779_) == 0 {
        let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1780_ = crate::leanh::lean_ctor_get(v_x_1779_, 0);
        crate::leanh::lean_inc(v_a_1780_);
        v___x_1781_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1781_, 0, v_a_1780_);
        return v___x_1781_;
    } else {
        let mut v_a_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1782_ = crate::leanh::lean_ctor_get(v_x_1779_, 0);
        crate::leanh::lean_inc(v_a_1782_);
        v___x_1783_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1783_, 0, v_a_1782_);
        return v___x_1783_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___redArg___boxed(
    mut v_x_1784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1785_ = l_Lake_EResult_toExcept___redArg(v_x_1784_);
    crate::leanh::lean_dec_ref(v_x_1784_);
    return v_res_1785_;
}
pub unsafe fn l_Lake_EResult_toExcept(
    mut v_00_u03b5_1786_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1787_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1788_: *mut crate::leanh::LeanObject,
    mut v_x_1789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1789_) == 0 {
        let mut v_a_1790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1790_ = crate::leanh::lean_ctor_get(v_x_1789_, 0);
        crate::leanh::lean_inc(v_a_1790_);
        v___x_1791_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1791_, 0, v_a_1790_);
        return v___x_1791_;
    } else {
        let mut v_a_1792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_1792_ = crate::leanh::lean_ctor_get(v_x_1789_, 0);
        crate::leanh::lean_inc(v_a_1792_);
        v___x_1793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1793_, 0, v_a_1792_);
        return v___x_1793_;
    }
}
pub unsafe fn l_Lake_EResult_toExcept___boxed(
    mut v_00_u03b5_1794_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1795_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1796_: *mut crate::leanh::LeanObject,
    mut v_x_1797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1798_ = l_Lake_EResult_toExcept(
        v_00_u03b5_1794_,
        v_00_u03c3_1795_,
        v_00_u03b1_1796_,
        v_x_1797_,
    );
    crate::leanh::lean_dec_ref(v_x_1797_);
    return v_res_1798_;
}
pub unsafe fn l_Lake_EResult_map___redArg(
    mut v_f_1799_: *mut crate::leanh::LeanObject,
    mut v_x_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1805_: u8 = 0;
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1810_: u8 = 0;
    let mut v_a_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1815_: u8 = 0;
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1800_) == 0 {
                    v_a_1801_ = crate::leanh::lean_ctor_get(v_x_1800_, 0);
                    v_a_1802_ = crate::leanh::lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1810_ = (!crate::leanh::lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1810_ == 0 {
                        v___x_1804_ = v_x_1800_;
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1802_);
                        crate::leanh::lean_inc(v_a_1801_);
                        crate::leanh::lean_dec(v_x_1800_);
                        v___x_1804_ = crate::leanh::lean_box(0);
                        v_isShared_1805_ = v_isSharedCheck_1810_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1799_);
                    v_a_1811_ = crate::leanh::lean_ctor_get(v_x_1800_, 0);
                    v_a_1812_ = crate::leanh::lean_ctor_get(v_x_1800_, 1);
                    v_isSharedCheck_1819_ = (!crate::leanh::lean_is_exclusive(v_x_1800_)) as u8;
                    if v_isSharedCheck_1819_ == 0 {
                        v___x_1814_ = v_x_1800_;
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1812_);
                        crate::leanh::lean_inc(v_a_1811_);
                        crate::leanh::lean_dec(v_x_1800_);
                        v___x_1814_ = crate::leanh::lean_box(0);
                        v_isShared_1815_ = v_isSharedCheck_1819_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1806_ = crate::leanh::lean_apply_1(v_f_1799_, v_a_1801_);
                if v_isShared_1805_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1804_, 0, v___x_1806_);
                    v___x_1808_ = v___x_1804_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1809_, 1, v_a_1802_);
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
                    v_reuseFailAlloc_1818_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1811_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1818_, 1, v_a_1812_);
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
    mut v_00_u03b1_1820_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1821_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1822_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1823_: *mut crate::leanh::LeanObject,
    mut v_f_1824_: *mut crate::leanh::LeanObject,
    mut v_x_1825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1830_: u8 = 0;
    let mut v___x_1831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut v_a_1836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1825_) == 0 {
                    v_a_1826_ = crate::leanh::lean_ctor_get(v_x_1825_, 0);
                    v_a_1827_ = crate::leanh::lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1835_ = (!crate::leanh::lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1835_ == 0 {
                        v___x_1829_ = v_x_1825_;
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1827_);
                        crate::leanh::lean_inc(v_a_1826_);
                        crate::leanh::lean_dec(v_x_1825_);
                        v___x_1829_ = crate::leanh::lean_box(0);
                        v_isShared_1830_ = v_isSharedCheck_1835_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_1824_);
                    v_a_1836_ = crate::leanh::lean_ctor_get(v_x_1825_, 0);
                    v_a_1837_ = crate::leanh::lean_ctor_get(v_x_1825_, 1);
                    v_isSharedCheck_1844_ = (!crate::leanh::lean_is_exclusive(v_x_1825_)) as u8;
                    if v_isSharedCheck_1844_ == 0 {
                        v___x_1839_ = v_x_1825_;
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1837_);
                        crate::leanh::lean_inc(v_a_1836_);
                        crate::leanh::lean_dec(v_x_1825_);
                        v___x_1839_ = crate::leanh::lean_box(0);
                        v_isShared_1840_ = v_isSharedCheck_1844_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1831_ = crate::leanh::lean_apply_1(v_f_1824_, v_a_1826_);
                if v_isShared_1830_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1829_, 0, v___x_1831_);
                    v___x_1833_ = v___x_1829_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v___x_1831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 1, v_a_1827_);
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
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1836_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 1, v_a_1837_);
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
    mut v_00_u03b1_1845_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1846_: *mut crate::leanh::LeanObject,
    mut v___y_1847_: *mut crate::leanh::LeanObject,
    mut v___y_1848_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1863_: u8 = 0;
    let mut v___x_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v___y_1848_) == 0 {
                    v_a_1849_ = crate::leanh::lean_ctor_get(v___y_1848_, 0);
                    v_a_1850_ = crate::leanh::lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1858_ = (!crate::leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1858_ == 0 {
                        v___x_1852_ = v___y_1848_;
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1850_);
                        crate::leanh::lean_inc(v_a_1849_);
                        crate::leanh::lean_dec(v___y_1848_);
                        v___x_1852_ = crate::leanh::lean_box(0);
                        v_isShared_1853_ = v_isSharedCheck_1858_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_1847_);
                    v_a_1859_ = crate::leanh::lean_ctor_get(v___y_1848_, 0);
                    v_a_1860_ = crate::leanh::lean_ctor_get(v___y_1848_, 1);
                    v_isSharedCheck_1867_ = (!crate::leanh::lean_is_exclusive(v___y_1848_)) as u8;
                    if v_isSharedCheck_1867_ == 0 {
                        v___x_1862_ = v___y_1848_;
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1860_);
                        crate::leanh::lean_inc(v_a_1859_);
                        crate::leanh::lean_dec(v___y_1848_);
                        v___x_1862_ = crate::leanh::lean_box(0);
                        v_isShared_1863_ = v_isSharedCheck_1867_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1854_ = crate::leanh::lean_apply_1(v___y_1847_, v_a_1849_);
                if v_isShared_1853_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1852_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_a_1850_);
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
                    v_reuseFailAlloc_1866_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_a_1859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_a_1860_);
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
    mut v___f_1868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1869_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1870_: *mut crate::leanh::LeanObject,
    mut v___y_1871_: *mut crate::leanh::LeanObject,
    mut v___y_1872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1873_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_1873_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1873_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1873_, 2, v___y_1871_);
    v___x_1874_ = crate::leanh::lean_apply_4(
        v___f_1868_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1873_,
        v___y_1872_,
    );
    return v___x_1874_;
}
pub unsafe fn l_Lake_EResult_instFunctor(
    mut v_00_u03b5_1881_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l_Lake_EResult_instFunctor___closed__2;
    return v___x_1883_;
}
pub unsafe fn l_Lake_EResult_toEStateMResult___redArg(
    mut v_x_1884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1889_: u8 = 0;
    let mut v___x_1891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1893_: u8 = 0;
    let mut v_a_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1902_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1884_) == 0 {
                    v_a_1885_ = crate::leanh::lean_ctor_get(v_x_1884_, 0);
                    v_a_1886_ = crate::leanh::lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1893_ = (!crate::leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1893_ == 0 {
                        v___x_1888_ = v_x_1884_;
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1886_);
                        crate::leanh::lean_inc(v_a_1885_);
                        crate::leanh::lean_dec(v_x_1884_);
                        v___x_1888_ = crate::leanh::lean_box(0);
                        v_isShared_1889_ = v_isSharedCheck_1893_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1894_ = crate::leanh::lean_ctor_get(v_x_1884_, 0);
                    v_a_1895_ = crate::leanh::lean_ctor_get(v_x_1884_, 1);
                    v_isSharedCheck_1902_ = (!crate::leanh::lean_is_exclusive(v_x_1884_)) as u8;
                    if v_isSharedCheck_1902_ == 0 {
                        v___x_1897_ = v_x_1884_;
                        v_isShared_1898_ = v_isSharedCheck_1902_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1895_);
                        crate::leanh::lean_inc(v_a_1894_);
                        crate::leanh::lean_dec(v_x_1884_);
                        v___x_1897_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1892_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 0, v_a_1885_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1892_, 1, v_a_1886_);
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
                    v_reuseFailAlloc_1901_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 0, v_a_1894_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1901_, 1, v_a_1895_);
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
    mut v_00_u03b5_1903_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1904_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1905_: *mut crate::leanh::LeanObject,
    mut v_x_1906_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lake_EResult_toEStateMResult___redArg(v_x_1906_);
    return v___x_1907_;
}
pub unsafe fn l_Lake_EResult_ofEStateMResult___redArg(
    mut v_x_1908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_1909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1913_: u8 = 0;
    let mut v___x_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1917_: u8 = 0;
    let mut v_a_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1922_: u8 = 0;
    let mut v___x_1924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1926_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1908_) == 0 {
                    v_a_1909_ = crate::leanh::lean_ctor_get(v_x_1908_, 0);
                    v_a_1910_ = crate::leanh::lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1917_ = (!crate::leanh::lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1917_ == 0 {
                        v___x_1912_ = v_x_1908_;
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1910_);
                        crate::leanh::lean_inc(v_a_1909_);
                        crate::leanh::lean_dec(v_x_1908_);
                        v___x_1912_ = crate::leanh::lean_box(0);
                        v_isShared_1913_ = v_isSharedCheck_1917_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1918_ = crate::leanh::lean_ctor_get(v_x_1908_, 0);
                    v_a_1919_ = crate::leanh::lean_ctor_get(v_x_1908_, 1);
                    v_isSharedCheck_1926_ = (!crate::leanh::lean_is_exclusive(v_x_1908_)) as u8;
                    if v_isSharedCheck_1926_ == 0 {
                        v___x_1921_ = v_x_1908_;
                        v_isShared_1922_ = v_isSharedCheck_1926_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1919_);
                        crate::leanh::lean_inc(v_a_1918_);
                        crate::leanh::lean_dec(v_x_1908_);
                        v___x_1921_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_1916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 0, v_a_1909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1916_, 1, v_a_1910_);
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
                    v_reuseFailAlloc_1925_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 0, v_a_1918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1925_, 1, v_a_1919_);
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
    mut v_00_u03b5_1927_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1928_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1929_: *mut crate::leanh::LeanObject,
    mut v_x_1930_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1931_ = l_Lake_EResult_ofEStateMResult___redArg(v_x_1930_);
    return v___x_1931_;
}
pub unsafe fn l_Lake_EStateT_mk___redArg(
    mut v_x_1932_: *mut crate::leanh::LeanObject,
    mut v_a_1933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1934_ = crate::leanh::lean_apply_1(v_x_1932_, v_a_1933_);
    return v___x_1934_;
}
pub unsafe fn l_Lake_EStateT_mk(
    mut v_00_u03b5_1935_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1936_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1937_: *mut crate::leanh::LeanObject,
    mut v_m_1938_: *mut crate::leanh::LeanObject,
    mut v_x_1939_: *mut crate::leanh::LeanObject,
    mut v_a_1940_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1941_ = crate::leanh::lean_apply_1(v_x_1939_, v_a_1940_);
    return v___x_1941_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0(
    mut v_inst_1942_: *mut crate::leanh::LeanObject,
    mut v_inst_1943_: *mut crate::leanh::LeanObject,
    mut v_s_1944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1945_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1945_, 0, v_inst_1942_);
    crate::leanh::lean_ctor_set(v___x_1945_, 1, v_s_1944_);
    v___x_1946_ = crate::leanh::lean_apply_2(v_inst_1943_, crate::leanh::lean_box(0), v___x_1945_);
    return v___x_1946_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg(
    mut v_inst_1947_: *mut crate::leanh::LeanObject,
    mut v_inst_1948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1949_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1949_, 0, v_inst_1947_);
    crate::leanh::lean_closure_set(v___f_1949_, 1, v_inst_1948_);
    return v___f_1949_;
}
pub unsafe fn l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure(
    mut v_00_u03b5_1950_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1951_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1952_: *mut crate::leanh::LeanObject,
    mut v_m_1953_: *mut crate::leanh::LeanObject,
    mut v_inst_1954_: *mut crate::leanh::LeanObject,
    mut v_inst_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1956_ = crate::leanh::lean_alloc_closure(
        l___private_Lake_Util_EStateT_0__Lake_EStateT_instInhabitedOfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1956_, 0, v_inst_1954_);
    crate::leanh::lean_closure_set(v___f_1956_, 1, v_inst_1955_);
    return v___f_1956_;
}
pub unsafe fn l_Lake_EStateT_run___redArg(
    mut v_init_1957_: *mut crate::leanh::LeanObject,
    mut v_self_1958_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1959_ = crate::leanh::lean_apply_1(v_self_1958_, v_init_1957_);
    return v___x_1959_;
}
pub unsafe fn l_Lake_EStateT_run(
    mut v_00_u03b5_1960_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1961_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1962_: *mut crate::leanh::LeanObject,
    mut v_m_1963_: *mut crate::leanh::LeanObject,
    mut v_init_1964_: *mut crate::leanh::LeanObject,
    mut v_self_1965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1966_ = crate::leanh::lean_apply_1(v_self_1965_, v_init_1964_);
    return v___x_1966_;
}
pub unsafe fn l_Lake_EStateT_run_x27___redArg(
    mut v_inst_1968_: *mut crate::leanh::LeanObject,
    mut v_init_1969_: *mut crate::leanh::LeanObject,
    mut v_x_1970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1971_ = crate::leanh::lean_ctor_get(v_inst_1968_, 0);
    crate::leanh::lean_inc(v_map_1971_);
    crate::leanh::lean_dec_ref(v_inst_1968_);
    v___x_1972_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1973_ = crate::leanh::lean_apply_1(v_x_1970_, v_init_1969_);
    v___x_1974_ = crate::leanh::lean_apply_4(
        v_map_1971_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1972_,
        v___x_1973_,
    );
    return v___x_1974_;
}
pub unsafe fn l_Lake_EStateT_run_x27(
    mut v_00_u03b5_1975_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1976_: *mut crate::leanh::LeanObject,
    mut v_m_1977_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1978_: *mut crate::leanh::LeanObject,
    mut v_inst_1979_: *mut crate::leanh::LeanObject,
    mut v_init_1980_: *mut crate::leanh::LeanObject,
    mut v_x_1981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1982_ = crate::leanh::lean_ctor_get(v_inst_1979_, 0);
    crate::leanh::lean_inc(v_map_1982_);
    crate::leanh::lean_dec_ref(v_inst_1979_);
    v___x_1983_ = l_Lake_EStateT_run_x27___redArg___closed__0;
    v___x_1984_ = crate::leanh::lean_apply_1(v_x_1981_, v_init_1980_);
    v___x_1985_ = crate::leanh::lean_apply_4(
        v_map_1982_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1983_,
        v___x_1984_,
    );
    return v___x_1985_;
}
pub unsafe fn l_Lake_EStateT_toStateT___redArg(
    mut v_inst_1987_: *mut crate::leanh::LeanObject,
    mut v_x_1988_: *mut crate::leanh::LeanObject,
    mut v_s_1989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_1990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_1990_ = crate::leanh::lean_ctor_get(v_inst_1987_, 0);
    crate::leanh::lean_inc(v_map_1990_);
    crate::leanh::lean_dec_ref(v_inst_1987_);
    v___x_1991_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_1992_ = crate::leanh::lean_apply_1(v_x_1988_, v_s_1989_);
    v___x_1993_ = crate::leanh::lean_apply_4(
        v_map_1990_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_1991_,
        v___x_1992_,
    );
    return v___x_1993_;
}
pub unsafe fn l_Lake_EStateT_toStateT(
    mut v_m_1994_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_1995_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_1996_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_1997_: *mut crate::leanh::LeanObject,
    mut v_inst_1998_: *mut crate::leanh::LeanObject,
    mut v_x_1999_: *mut crate::leanh::LeanObject,
    mut v_s_2000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2001_ = crate::leanh::lean_ctor_get(v_inst_1998_, 0);
    crate::leanh::lean_inc(v_map_2001_);
    crate::leanh::lean_dec_ref(v_inst_1998_);
    v___x_2002_ = l_Lake_EStateT_toStateT___redArg___closed__0;
    v___x_2003_ = crate::leanh::lean_apply_1(v_x_1999_, v_s_2000_);
    v___x_2004_ = crate::leanh::lean_apply_4(
        v_map_2001_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2002_,
        v___x_2003_,
    );
    return v___x_2004_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f___redArg(
    mut v_inst_2006_: *mut crate::leanh::LeanObject,
    mut v_x_2007_: *mut crate::leanh::LeanObject,
    mut v_s_2008_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2009_ = crate::leanh::lean_ctor_get(v_inst_2006_, 0);
    crate::leanh::lean_inc(v_map_2009_);
    crate::leanh::lean_dec_ref(v_inst_2006_);
    v___x_2010_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2011_ = crate::leanh::lean_apply_1(v_x_2007_, v_s_2008_);
    v___x_2012_ = crate::leanh::lean_apply_4(
        v_map_2009_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2010_,
        v___x_2011_,
    );
    return v___x_2012_;
}
pub unsafe fn l_Lake_EStateT_toStateT_x3f(
    mut v_m_2013_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2014_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2015_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2016_: *mut crate::leanh::LeanObject,
    mut v_inst_2017_: *mut crate::leanh::LeanObject,
    mut v_x_2018_: *mut crate::leanh::LeanObject,
    mut v_s_2019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2020_ = crate::leanh::lean_ctor_get(v_inst_2017_, 0);
    crate::leanh::lean_inc(v_map_2020_);
    crate::leanh::lean_dec_ref(v_inst_2017_);
    v___x_2021_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2022_ = crate::leanh::lean_apply_1(v_x_2018_, v_s_2019_);
    v___x_2023_ = crate::leanh::lean_apply_4(
        v_map_2020_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2021_,
        v___x_2022_,
    );
    return v___x_2023_;
}
pub unsafe fn l_Lake_EStateT_run_x3f___redArg(
    mut v_inst_2024_: *mut crate::leanh::LeanObject,
    mut v_init_2025_: *mut crate::leanh::LeanObject,
    mut v_x_2026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2027_ = crate::leanh::lean_ctor_get(v_inst_2024_, 0);
    crate::leanh::lean_inc(v_map_2027_);
    crate::leanh::lean_dec_ref(v_inst_2024_);
    v___x_2028_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2029_ = crate::leanh::lean_apply_1(v_x_2026_, v_init_2025_);
    v___x_2030_ = crate::leanh::lean_apply_4(
        v_map_2027_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2028_,
        v___x_2029_,
    );
    return v___x_2030_;
}
pub unsafe fn l_Lake_EStateT_run_x3f(
    mut v_00_u03c3_2031_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2032_: *mut crate::leanh::LeanObject,
    mut v_m_2033_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2034_: *mut crate::leanh::LeanObject,
    mut v_inst_2035_: *mut crate::leanh::LeanObject,
    mut v_init_2036_: *mut crate::leanh::LeanObject,
    mut v_x_2037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2038_ = crate::leanh::lean_ctor_get(v_inst_2035_, 0);
    crate::leanh::lean_inc(v_map_2038_);
    crate::leanh::lean_dec_ref(v_inst_2035_);
    v___x_2039_ = l_Lake_EStateT_toStateT_x3f___redArg___closed__0;
    v___x_2040_ = crate::leanh::lean_apply_1(v_x_2037_, v_init_2036_);
    v___x_2041_ = crate::leanh::lean_apply_4(
        v_map_2038_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2039_,
        v___x_2040_,
    );
    return v___x_2041_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27___redArg(
    mut v_inst_2043_: *mut crate::leanh::LeanObject,
    mut v_init_2044_: *mut crate::leanh::LeanObject,
    mut v_x_2045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2046_ = crate::leanh::lean_ctor_get(v_inst_2043_, 0);
    crate::leanh::lean_inc(v_map_2046_);
    crate::leanh::lean_dec_ref(v_inst_2043_);
    v___x_2047_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2048_ = crate::leanh::lean_apply_1(v_x_2045_, v_init_2044_);
    v___x_2049_ = crate::leanh::lean_apply_4(
        v_map_2046_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2047_,
        v___x_2048_,
    );
    return v___x_2049_;
}
pub unsafe fn l_Lake_EStateT_run_x3f_x27(
    mut v_m_2050_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2051_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2052_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2053_: *mut crate::leanh::LeanObject,
    mut v_inst_2054_: *mut crate::leanh::LeanObject,
    mut v_init_2055_: *mut crate::leanh::LeanObject,
    mut v_x_2056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2057_ = crate::leanh::lean_ctor_get(v_inst_2054_, 0);
    crate::leanh::lean_inc(v_map_2057_);
    crate::leanh::lean_dec_ref(v_inst_2054_);
    v___x_2058_ = l_Lake_EStateT_run_x3f_x27___redArg___closed__0;
    v___x_2059_ = crate::leanh::lean_apply_1(v_x_2056_, v_init_2055_);
    v___x_2060_ = crate::leanh::lean_apply_4(
        v_map_2057_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2058_,
        v___x_2059_,
    );
    return v___x_2060_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg___lam__0(
    mut v_toPure_2061_: *mut crate::leanh::LeanObject,
    mut v_h_2062_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2073_: u8 = 0;
    let mut v_a_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2063_) == 0 {
                    crate::leanh::lean_dec(v_h_2062_);
                    v_a_2064_ = crate::leanh::lean_ctor_get(v_____do__lift_2063_, 0);
                    v_a_2065_ = crate::leanh::lean_ctor_get(v_____do__lift_2063_, 1);
                    v_isSharedCheck_2073_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2063_)) as u8;
                    if v_isSharedCheck_2073_ == 0 {
                        v___x_2067_ = v_____do__lift_2063_;
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2065_);
                        crate::leanh::lean_inc(v_a_2064_);
                        crate::leanh::lean_dec(v_____do__lift_2063_);
                        v___x_2067_ = crate::leanh::lean_box(0);
                        v_isShared_2068_ = v_isSharedCheck_2073_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_toPure_2061_);
                    v_a_2074_ = crate::leanh::lean_ctor_get(v_____do__lift_2063_, 0);
                    crate::leanh::lean_inc(v_a_2074_);
                    v_a_2075_ = crate::leanh::lean_ctor_get(v_____do__lift_2063_, 1);
                    crate::leanh::lean_inc(v_a_2075_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2063_, 2);
                    v___x_2076_ = crate::leanh::lean_apply_2(v_h_2062_, v_a_2074_, v_a_2075_);
                    return v___x_2076_;
                }
            }
            1 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2064_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2072_, 1, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2072_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2071_ = crate::leanh::lean_apply_2(
                    v_toPure_2061_,
                    crate::leanh::lean_box(0),
                    v___x_2070_,
                );
                return v___x_2071_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_catchExceptions___redArg(
    mut v_inst_2077_: *mut crate::leanh::LeanObject,
    mut v_x_2078_: *mut crate::leanh::LeanObject,
    mut v_h_2079_: *mut crate::leanh::LeanObject,
    mut v_s_2080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2081_ = crate::leanh::lean_ctor_get(v_inst_2077_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2081_);
    v_toBind_2082_ = crate::leanh::lean_ctor_get(v_inst_2077_, 1);
    crate::leanh::lean_inc(v_toBind_2082_);
    crate::leanh::lean_dec_ref(v_inst_2077_);
    v_toPure_2083_ = crate::leanh::lean_ctor_get(v_toApplicative_2081_, 1);
    crate::leanh::lean_inc(v_toPure_2083_);
    crate::leanh::lean_dec_ref(v_toApplicative_2081_);
    v___x_2084_ = crate::leanh::lean_apply_1(v_x_2078_, v_s_2080_);
    v___f_2085_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2085_, 0, v_toPure_2083_);
    crate::leanh::lean_closure_set(v___f_2085_, 1, v_h_2079_);
    v___x_2086_ = crate::leanh::lean_apply_4(
        v_toBind_2082_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2084_,
        v___f_2085_,
    );
    return v___x_2086_;
}
pub unsafe fn l_Lake_EStateT_catchExceptions(
    mut v_m_2087_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2088_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2089_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2090_: *mut crate::leanh::LeanObject,
    mut v_inst_2091_: *mut crate::leanh::LeanObject,
    mut v_x_2092_: *mut crate::leanh::LeanObject,
    mut v_h_2093_: *mut crate::leanh::LeanObject,
    mut v_s_2094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2095_ = crate::leanh::lean_ctor_get(v_inst_2091_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2095_);
    v_toBind_2096_ = crate::leanh::lean_ctor_get(v_inst_2091_, 1);
    crate::leanh::lean_inc(v_toBind_2096_);
    crate::leanh::lean_dec_ref(v_inst_2091_);
    v_toPure_2097_ = crate::leanh::lean_ctor_get(v_toApplicative_2095_, 1);
    crate::leanh::lean_inc(v_toPure_2097_);
    crate::leanh::lean_dec_ref(v_toApplicative_2095_);
    v___x_2098_ = crate::leanh::lean_apply_1(v_x_2092_, v_s_2094_);
    v___f_2099_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_catchExceptions___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2099_, 0, v_toPure_2097_);
    crate::leanh::lean_closure_set(v___f_2099_, 1, v_h_2093_);
    v___x_2100_ = crate::leanh::lean_apply_4(
        v_toBind_2096_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2098_,
        v___f_2099_,
    );
    return v___x_2100_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg___lam__0(
    mut v_s_2101_: *mut crate::leanh::LeanObject,
    mut v_toPure_2102_: *mut crate::leanh::LeanObject,
    mut v_a_2103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2104_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2104_, 0, v_a_2103_);
    crate::leanh::lean_ctor_set(v___x_2104_, 1, v_s_2101_);
    v___x_2105_ =
        crate::leanh::lean_apply_2(v_toPure_2102_, crate::leanh::lean_box(0), v___x_2104_);
    return v___x_2105_;
}
pub unsafe fn l_Lake_EStateT_lift___redArg(
    mut v_inst_2106_: *mut crate::leanh::LeanObject,
    mut v_x_2107_: *mut crate::leanh::LeanObject,
    mut v_s_2108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2109_ = crate::leanh::lean_ctor_get(v_inst_2106_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2109_);
    v_toBind_2110_ = crate::leanh::lean_ctor_get(v_inst_2106_, 1);
    crate::leanh::lean_inc(v_toBind_2110_);
    crate::leanh::lean_dec_ref(v_inst_2106_);
    v_toPure_2111_ = crate::leanh::lean_ctor_get(v_toApplicative_2109_, 1);
    crate::leanh::lean_inc(v_toPure_2111_);
    crate::leanh::lean_dec_ref(v_toApplicative_2109_);
    v___f_2112_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2112_, 0, v_s_2108_);
    crate::leanh::lean_closure_set(v___f_2112_, 1, v_toPure_2111_);
    v___x_2113_ = crate::leanh::lean_apply_4(
        v_toBind_2110_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_2107_,
        v___f_2112_,
    );
    return v___x_2113_;
}
pub unsafe fn l_Lake_EStateT_lift(
    mut v_m_2114_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2115_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2116_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2117_: *mut crate::leanh::LeanObject,
    mut v_inst_2118_: *mut crate::leanh::LeanObject,
    mut v_x_2119_: *mut crate::leanh::LeanObject,
    mut v_s_2120_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2121_ = crate::leanh::lean_ctor_get(v_inst_2118_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2121_);
    v_toBind_2122_ = crate::leanh::lean_ctor_get(v_inst_2118_, 1);
    crate::leanh::lean_inc(v_toBind_2122_);
    crate::leanh::lean_dec_ref(v_inst_2118_);
    v_toPure_2123_ = crate::leanh::lean_ctor_get(v_toApplicative_2121_, 1);
    crate::leanh::lean_inc(v_toPure_2123_);
    crate::leanh::lean_dec_ref(v_toApplicative_2121_);
    v___f_2124_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_lift___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2124_, 0, v_s_2120_);
    crate::leanh::lean_closure_set(v___f_2124_, 1, v_toPure_2123_);
    v___x_2125_ = crate::leanh::lean_apply_4(
        v_toBind_2122_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_2119_,
        v___f_2124_,
    );
    return v___x_2125_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0(
    mut v___y_2126_: *mut crate::leanh::LeanObject,
    mut v_toPure_2127_: *mut crate::leanh::LeanObject,
    mut v_a_2128_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2129_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2129_, 0, v_a_2128_);
    crate::leanh::lean_ctor_set(v___x_2129_, 1, v___y_2126_);
    v___x_2130_ =
        crate::leanh::lean_apply_2(v_toPure_2127_, crate::leanh::lean_box(0), v___x_2129_);
    return v___x_2130_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1(
    mut v_inst_2131_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2132_: *mut crate::leanh::LeanObject,
    mut v___y_2133_: *mut crate::leanh::LeanObject,
    mut v___y_2134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2135_ = crate::leanh::lean_ctor_get(v_inst_2131_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2135_);
    v_toBind_2136_ = crate::leanh::lean_ctor_get(v_inst_2131_, 1);
    crate::leanh::lean_inc(v_toBind_2136_);
    crate::leanh::lean_dec_ref(v_inst_2131_);
    v_toPure_2137_ = crate::leanh::lean_ctor_get(v_toApplicative_2135_, 1);
    crate::leanh::lean_inc(v_toPure_2137_);
    crate::leanh::lean_dec_ref(v_toApplicative_2135_);
    v___f_2138_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2138_, 0, v___y_2134_);
    crate::leanh::lean_closure_set(v___f_2138_, 1, v_toPure_2137_);
    v___x_2139_ = crate::leanh::lean_apply_4(
        v_toBind_2136_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___y_2133_,
        v___f_2138_,
    );
    return v___x_2139_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad___redArg(
    mut v_inst_2140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2141_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2141_, 0, v_inst_2140_);
    return v___f_2141_;
}
pub unsafe fn l_Lake_EStateT_instMonadLiftOfMonad(
    mut v_m_2142_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_2143_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2144_: *mut crate::leanh::LeanObject,
    mut v_inst_2145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2146_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadLiftOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2146_, 0, v_inst_2145_);
    return v___f_2146_;
}
pub unsafe fn l_Lake_EStateT_pure___redArg(
    mut v_inst_2147_: *mut crate::leanh::LeanObject,
    mut v_a_2148_: *mut crate::leanh::LeanObject,
    mut v_s_2149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2150_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2150_, 0, v_a_2148_);
    crate::leanh::lean_ctor_set(v___x_2150_, 1, v_s_2149_);
    v___x_2151_ = crate::leanh::lean_apply_2(v_inst_2147_, crate::leanh::lean_box(0), v___x_2150_);
    return v___x_2151_;
}
pub unsafe fn l_Lake_EStateT_pure(
    mut v_00_u03b5_2152_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2153_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2154_: *mut crate::leanh::LeanObject,
    mut v_m_2155_: *mut crate::leanh::LeanObject,
    mut v_inst_2156_: *mut crate::leanh::LeanObject,
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_s_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2159_, 0, v_a_2157_);
    crate::leanh::lean_ctor_set(v___x_2159_, 1, v_s_2158_);
    v___x_2160_ = crate::leanh::lean_apply_2(v_inst_2156_, crate::leanh::lean_box(0), v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg___lam__0(
    mut v_inst_2161_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2162_: *mut crate::leanh::LeanObject,
    mut v___y_2163_: *mut crate::leanh::LeanObject,
    mut v___y_2164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2165_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2165_, 0, v___y_2163_);
    crate::leanh::lean_ctor_set(v___x_2165_, 1, v___y_2164_);
    v___x_2166_ = crate::leanh::lean_apply_2(v_inst_2161_, crate::leanh::lean_box(0), v___x_2165_);
    return v___x_2166_;
}
pub unsafe fn l_Lake_EStateT_instPure___redArg(
    mut v_inst_2167_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2168_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2168_, 0, v_inst_2167_);
    return v___f_2168_;
}
pub unsafe fn l_Lake_EStateT_instPure(
    mut v_00_u03b5_2169_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2170_: *mut crate::leanh::LeanObject,
    mut v_m_2171_: *mut crate::leanh::LeanObject,
    mut v_inst_2172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2173_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2173_, 0, v_inst_2172_);
    return v___f_2173_;
}
pub unsafe fn l_Lake_EStateT_map___redArg___lam__0(
    mut v_f_2174_: *mut crate::leanh::LeanObject,
    mut v_x_2175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2180_: u8 = 0;
    let mut v___x_2181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2185_: u8 = 0;
    let mut v_a_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2175_) == 0 {
                    v_a_2176_ = crate::leanh::lean_ctor_get(v_x_2175_, 0);
                    v_a_2177_ = crate::leanh::lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2185_ = (!crate::leanh::lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2185_ == 0 {
                        v___x_2179_ = v_x_2175_;
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2177_);
                        crate::leanh::lean_inc(v_a_2176_);
                        crate::leanh::lean_dec(v_x_2175_);
                        v___x_2179_ = crate::leanh::lean_box(0);
                        v_isShared_2180_ = v_isSharedCheck_2185_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_f_2174_);
                    v_a_2186_ = crate::leanh::lean_ctor_get(v_x_2175_, 0);
                    v_a_2187_ = crate::leanh::lean_ctor_get(v_x_2175_, 1);
                    v_isSharedCheck_2194_ = (!crate::leanh::lean_is_exclusive(v_x_2175_)) as u8;
                    if v_isSharedCheck_2194_ == 0 {
                        v___x_2189_ = v_x_2175_;
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2187_);
                        crate::leanh::lean_inc(v_a_2186_);
                        crate::leanh::lean_dec(v_x_2175_);
                        v___x_2189_ = crate::leanh::lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2194_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2181_ = crate::leanh::lean_apply_1(v_f_2174_, v_a_2176_);
                if v_isShared_2180_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2179_, 0, v___x_2181_);
                    v___x_2183_ = v___x_2179_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2184_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 0, v___x_2181_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2184_, 1, v_a_2177_);
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
                    v_reuseFailAlloc_2193_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_a_2186_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_a_2187_);
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
    mut v_inst_2195_: *mut crate::leanh::LeanObject,
    mut v_f_2196_: *mut crate::leanh::LeanObject,
    mut v_x_2197_: *mut crate::leanh::LeanObject,
    mut v_s_2198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2199_ = crate::leanh::lean_ctor_get(v_inst_2195_, 0);
    crate::leanh::lean_inc(v_map_2199_);
    crate::leanh::lean_dec_ref(v_inst_2195_);
    v___f_2200_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2200_, 0, v_f_2196_);
    v___x_2201_ = crate::leanh::lean_apply_1(v_x_2197_, v_s_2198_);
    v___x_2202_ = crate::leanh::lean_apply_4(
        v_map_2199_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2200_,
        v___x_2201_,
    );
    return v___x_2202_;
}
pub unsafe fn l_Lake_EStateT_map(
    mut v_00_u03b5_2203_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2204_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2205_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2206_: *mut crate::leanh::LeanObject,
    mut v_m_2207_: *mut crate::leanh::LeanObject,
    mut v_inst_2208_: *mut crate::leanh::LeanObject,
    mut v_f_2209_: *mut crate::leanh::LeanObject,
    mut v_x_2210_: *mut crate::leanh::LeanObject,
    mut v_s_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2212_ = crate::leanh::lean_ctor_get(v_inst_2208_, 0);
    crate::leanh::lean_inc(v_map_2212_);
    crate::leanh::lean_dec_ref(v_inst_2208_);
    v___f_2213_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_map___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2213_, 0, v_f_2209_);
    v___x_2214_ = crate::leanh::lean_apply_1(v_x_2210_, v_s_2211_);
    v___x_2215_ = crate::leanh::lean_apply_4(
        v_map_2212_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2213_,
        v___x_2214_,
    );
    return v___x_2215_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__0(
    mut v___y_2216_: *mut crate::leanh::LeanObject,
    mut v_x_2217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2232_: u8 = 0;
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2217_) == 0 {
                    v_a_2218_ = crate::leanh::lean_ctor_get(v_x_2217_, 0);
                    v_a_2219_ = crate::leanh::lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2227_ = (!crate::leanh::lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2227_ == 0 {
                        v___x_2221_ = v_x_2217_;
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2219_);
                        crate::leanh::lean_inc(v_a_2218_);
                        crate::leanh::lean_dec(v_x_2217_);
                        v___x_2221_ = crate::leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2227_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___y_2216_);
                    v_a_2228_ = crate::leanh::lean_ctor_get(v_x_2217_, 0);
                    v_a_2229_ = crate::leanh::lean_ctor_get(v_x_2217_, 1);
                    v_isSharedCheck_2236_ = (!crate::leanh::lean_is_exclusive(v_x_2217_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v___x_2231_ = v_x_2217_;
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2229_);
                        crate::leanh::lean_inc(v_a_2228_);
                        crate::leanh::lean_dec(v_x_2217_);
                        v___x_2231_ = crate::leanh::lean_box(0);
                        v_isShared_2232_ = v_isSharedCheck_2236_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2223_ = crate::leanh::lean_apply_1(v___y_2216_, v_a_2218_);
                if v_isShared_2222_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2221_, 0, v___x_2223_);
                    v___x_2225_ = v___x_2221_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v___x_2223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 1, v_a_2219_);
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
                    v_reuseFailAlloc_2235_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 0, v_a_2228_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2235_, 1, v_a_2229_);
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
    mut v_inst_2237_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2238_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2239_: *mut crate::leanh::LeanObject,
    mut v___y_2240_: *mut crate::leanh::LeanObject,
    mut v___y_2241_: *mut crate::leanh::LeanObject,
    mut v___y_2242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2243_ = crate::leanh::lean_ctor_get(v_inst_2237_, 0);
    crate::leanh::lean_inc(v_map_2243_);
    crate::leanh::lean_dec_ref(v_inst_2237_);
    v___f_2244_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2244_, 0, v___y_2240_);
    v___x_2245_ = crate::leanh::lean_apply_1(v___y_2241_, v___y_2242_);
    v___x_2246_ = crate::leanh::lean_apply_4(
        v_map_2243_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2244_,
        v___x_2245_,
    );
    return v___x_2246_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg___lam__2(
    mut v___f_2247_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2248_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2249_: *mut crate::leanh::LeanObject,
    mut v___y_2250_: *mut crate::leanh::LeanObject,
    mut v___y_2251_: *mut crate::leanh::LeanObject,
    mut v___y_2252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2253_ =
        crate::leanh::lean_alloc_closure(l_Function_const___boxed as *mut core::ffi::c_void, 4, 3);
    crate::leanh::lean_closure_set(v___x_2253_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2253_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2253_, 2, v___y_2250_);
    v___x_2254_ = crate::leanh::lean_apply_5(
        v___f_2247_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2253_,
        v___y_2251_,
        v___y_2252_,
    );
    return v___x_2254_;
}
pub unsafe fn l_Lake_EStateT_instFunctor___redArg(
    mut v_inst_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2256_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2256_, 0, v_inst_2255_);
    crate::leanh::lean_inc_ref(v___f_2256_);
    v___f_2257_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instFunctor___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2257_, 0, v___f_2256_);
    v___x_2258_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2258_, 0, v___f_2256_);
    crate::leanh::lean_ctor_set(v___x_2258_, 1, v___f_2257_);
    return v___x_2258_;
}
pub unsafe fn l_Lake_EStateT_instFunctor(
    mut v_00_u03b5_2259_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2260_: *mut crate::leanh::LeanObject,
    mut v_m_2261_: *mut crate::leanh::LeanObject,
    mut v_inst_2262_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2263_ = l_Lake_EStateT_instFunctor___redArg(v_inst_2262_);
    return v___x_2263_;
}
pub unsafe fn l_Lake_EStateT_bind___redArg___lam__0(
    mut v_f_2264_: *mut crate::leanh::LeanObject,
    mut v_toPure_2265_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2274_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2279_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2266_) == 0 {
                    crate::leanh::lean_dec(v_toPure_2265_);
                    v_a_2267_ = crate::leanh::lean_ctor_get(v_____do__lift_2266_, 0);
                    crate::leanh::lean_inc(v_a_2267_);
                    v_a_2268_ = crate::leanh::lean_ctor_get(v_____do__lift_2266_, 1);
                    crate::leanh::lean_inc(v_a_2268_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2266_, 2);
                    v___x_2269_ = crate::leanh::lean_apply_2(v_f_2264_, v_a_2267_, v_a_2268_);
                    return v___x_2269_;
                } else {
                    crate::leanh::lean_dec(v_f_2264_);
                    v_a_2270_ = crate::leanh::lean_ctor_get(v_____do__lift_2266_, 0);
                    v_a_2271_ = crate::leanh::lean_ctor_get(v_____do__lift_2266_, 1);
                    v_isSharedCheck_2279_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2266_)) as u8;
                    if v_isSharedCheck_2279_ == 0 {
                        v___x_2273_ = v_____do__lift_2266_;
                        v_isShared_2274_ = v_isSharedCheck_2279_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2271_);
                        crate::leanh::lean_inc(v_a_2270_);
                        crate::leanh::lean_dec(v_____do__lift_2266_);
                        v___x_2273_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2278_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_a_2270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2271_);
                    v___x_2276_ = v_reuseFailAlloc_2278_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2277_ = crate::leanh::lean_apply_2(
                    v_toPure_2265_,
                    crate::leanh::lean_box(0),
                    v___x_2276_,
                );
                return v___x_2277_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_bind___redArg(
    mut v_inst_2280_: *mut crate::leanh::LeanObject,
    mut v_x_2281_: *mut crate::leanh::LeanObject,
    mut v_f_2282_: *mut crate::leanh::LeanObject,
    mut v_s_2283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2284_ = crate::leanh::lean_ctor_get(v_inst_2280_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2284_);
    v_toBind_2285_ = crate::leanh::lean_ctor_get(v_inst_2280_, 1);
    crate::leanh::lean_inc(v_toBind_2285_);
    crate::leanh::lean_dec_ref(v_inst_2280_);
    v_toPure_2286_ = crate::leanh::lean_ctor_get(v_toApplicative_2284_, 1);
    crate::leanh::lean_inc(v_toPure_2286_);
    crate::leanh::lean_dec_ref(v_toApplicative_2284_);
    v___x_2287_ = crate::leanh::lean_apply_1(v_x_2281_, v_s_2283_);
    v___f_2288_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2288_, 0, v_f_2282_);
    crate::leanh::lean_closure_set(v___f_2288_, 1, v_toPure_2286_);
    v___x_2289_ = crate::leanh::lean_apply_4(
        v_toBind_2285_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2287_,
        v___f_2288_,
    );
    return v___x_2289_;
}
pub unsafe fn l_Lake_EStateT_bind(
    mut v_00_u03b5_2290_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2291_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2292_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2293_: *mut crate::leanh::LeanObject,
    mut v_m_2294_: *mut crate::leanh::LeanObject,
    mut v_inst_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: *mut crate::leanh::LeanObject,
    mut v_f_2297_: *mut crate::leanh::LeanObject,
    mut v_s_2298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2299_ = crate::leanh::lean_ctor_get(v_inst_2295_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2299_);
    v_toBind_2300_ = crate::leanh::lean_ctor_get(v_inst_2295_, 1);
    crate::leanh::lean_inc(v_toBind_2300_);
    crate::leanh::lean_dec_ref(v_inst_2295_);
    v_toPure_2301_ = crate::leanh::lean_ctor_get(v_toApplicative_2299_, 1);
    crate::leanh::lean_inc(v_toPure_2301_);
    crate::leanh::lean_dec_ref(v_toApplicative_2299_);
    v___x_2302_ = crate::leanh::lean_apply_1(v_x_2296_, v_s_2298_);
    v___f_2303_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_bind___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2303_, 0, v_f_2297_);
    crate::leanh::lean_closure_set(v___f_2303_, 1, v_toPure_2301_);
    v___x_2304_ = crate::leanh::lean_apply_4(
        v_toBind_2300_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2302_,
        v___f_2303_,
    );
    return v___x_2304_;
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg___lam__0(
    mut v_y_2305_: *mut crate::leanh::LeanObject,
    mut v_toPure_2306_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2307_) == 0 {
                    crate::leanh::lean_dec(v_toPure_2306_);
                    v_a_2308_ = crate::leanh::lean_ctor_get(v_____do__lift_2307_, 1);
                    crate::leanh::lean_inc(v_a_2308_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2307_, 2);
                    v___x_2309_ = crate::leanh::lean_box(0);
                    v___x_2310_ = crate::leanh::lean_apply_2(v_y_2305_, v___x_2309_, v_a_2308_);
                    return v___x_2310_;
                } else {
                    crate::leanh::lean_dec(v_y_2305_);
                    v_a_2311_ = crate::leanh::lean_ctor_get(v_____do__lift_2307_, 0);
                    v_a_2312_ = crate::leanh::lean_ctor_get(v_____do__lift_2307_, 1);
                    v_isSharedCheck_2320_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2307_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2314_ = v_____do__lift_2307_;
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2312_);
                        crate::leanh::lean_inc(v_a_2311_);
                        crate::leanh::lean_dec(v_____do__lift_2307_);
                        v___x_2314_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2319_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v_a_2311_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 1, v_a_2312_);
                    v___x_2317_ = v_reuseFailAlloc_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2318_ = crate::leanh::lean_apply_2(
                    v_toPure_2306_,
                    crate::leanh::lean_box(0),
                    v___x_2317_,
                );
                return v___x_2318_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_seqRight___redArg(
    mut v_inst_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
    mut v_y_2323_: *mut crate::leanh::LeanObject,
    mut v_s_2324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2325_ = crate::leanh::lean_ctor_get(v_inst_2321_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2325_);
    v_toBind_2326_ = crate::leanh::lean_ctor_get(v_inst_2321_, 1);
    crate::leanh::lean_inc(v_toBind_2326_);
    crate::leanh::lean_dec_ref(v_inst_2321_);
    v_toPure_2327_ = crate::leanh::lean_ctor_get(v_toApplicative_2325_, 1);
    crate::leanh::lean_inc(v_toPure_2327_);
    crate::leanh::lean_dec_ref(v_toApplicative_2325_);
    v___x_2328_ = crate::leanh::lean_apply_1(v_x_2322_, v_s_2324_);
    v___f_2329_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2329_, 0, v_y_2323_);
    crate::leanh::lean_closure_set(v___f_2329_, 1, v_toPure_2327_);
    v___x_2330_ = crate::leanh::lean_apply_4(
        v_toBind_2326_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2328_,
        v___f_2329_,
    );
    return v___x_2330_;
}
pub unsafe fn l_Lake_EStateT_seqRight(
    mut v_00_u03b5_2331_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2332_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2333_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2334_: *mut crate::leanh::LeanObject,
    mut v_m_2335_: *mut crate::leanh::LeanObject,
    mut v_inst_2336_: *mut crate::leanh::LeanObject,
    mut v_x_2337_: *mut crate::leanh::LeanObject,
    mut v_y_2338_: *mut crate::leanh::LeanObject,
    mut v_s_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2340_ = crate::leanh::lean_ctor_get(v_inst_2336_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2340_);
    v_toBind_2341_ = crate::leanh::lean_ctor_get(v_inst_2336_, 1);
    crate::leanh::lean_inc(v_toBind_2341_);
    crate::leanh::lean_dec_ref(v_inst_2336_);
    v_toPure_2342_ = crate::leanh::lean_ctor_get(v_toApplicative_2340_, 1);
    crate::leanh::lean_inc(v_toPure_2342_);
    crate::leanh::lean_dec_ref(v_toApplicative_2340_);
    v___x_2343_ = crate::leanh::lean_apply_1(v_x_2337_, v_s_2339_);
    v___f_2344_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_seqRight___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2344_, 0, v_y_2338_);
    crate::leanh::lean_closure_set(v___f_2344_, 1, v_toPure_2342_);
    v___x_2345_ = crate::leanh::lean_apply_4(
        v_toBind_2341_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2343_,
        v___f_2344_,
    );
    return v___x_2345_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__0(
    mut v___y_2346_: *mut crate::leanh::LeanObject,
    mut v_toPure_2347_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2356_: u8 = 0;
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2348_) == 0 {
                    crate::leanh::lean_dec(v_toPure_2347_);
                    v_a_2349_ = crate::leanh::lean_ctor_get(v_____do__lift_2348_, 0);
                    crate::leanh::lean_inc(v_a_2349_);
                    v_a_2350_ = crate::leanh::lean_ctor_get(v_____do__lift_2348_, 1);
                    crate::leanh::lean_inc(v_a_2350_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2348_, 2);
                    v___x_2351_ = crate::leanh::lean_apply_2(v___y_2346_, v_a_2349_, v_a_2350_);
                    return v___x_2351_;
                } else {
                    crate::leanh::lean_dec(v___y_2346_);
                    v_a_2352_ = crate::leanh::lean_ctor_get(v_____do__lift_2348_, 0);
                    v_a_2353_ = crate::leanh::lean_ctor_get(v_____do__lift_2348_, 1);
                    v_isSharedCheck_2361_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2348_)) as u8;
                    if v_isSharedCheck_2361_ == 0 {
                        v___x_2355_ = v_____do__lift_2348_;
                        v_isShared_2356_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2353_);
                        crate::leanh::lean_inc(v_a_2352_);
                        crate::leanh::lean_dec(v_____do__lift_2348_);
                        v___x_2355_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2352_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 1, v_a_2353_);
                    v___x_2358_ = v_reuseFailAlloc_2360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2359_ = crate::leanh::lean_apply_2(
                    v_toPure_2347_,
                    crate::leanh::lean_box(0),
                    v___x_2358_,
                );
                return v___x_2359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__1(
    mut v_toPure_2362_: *mut crate::leanh::LeanObject,
    mut v_toBind_2363_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2364_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2365_: *mut crate::leanh::LeanObject,
    mut v___y_2366_: *mut crate::leanh::LeanObject,
    mut v___y_2367_: *mut crate::leanh::LeanObject,
    mut v___y_2368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2369_ = crate::leanh::lean_apply_1(v___y_2366_, v___y_2368_);
    v___f_2370_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2370_, 0, v___y_2367_);
    crate::leanh::lean_closure_set(v___f_2370_, 1, v_toPure_2362_);
    v___x_2371_ = crate::leanh::lean_apply_4(
        v_toBind_2363_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2369_,
        v___f_2370_,
    );
    return v___x_2371_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__2(
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v_toPure_2373_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2382_: u8 = 0;
    let mut v___x_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2387_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2374_) == 0 {
                    crate::leanh::lean_dec(v_toPure_2373_);
                    v_a_2375_ = crate::leanh::lean_ctor_get(v_____do__lift_2374_, 1);
                    crate::leanh::lean_inc(v_a_2375_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2374_, 2);
                    v___x_2376_ = crate::leanh::lean_box(0);
                    v___x_2377_ = crate::leanh::lean_apply_2(v___y_2372_, v___x_2376_, v_a_2375_);
                    return v___x_2377_;
                } else {
                    crate::leanh::lean_dec(v___y_2372_);
                    v_a_2378_ = crate::leanh::lean_ctor_get(v_____do__lift_2374_, 0);
                    v_a_2379_ = crate::leanh::lean_ctor_get(v_____do__lift_2374_, 1);
                    v_isSharedCheck_2387_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2374_)) as u8;
                    if v_isSharedCheck_2387_ == 0 {
                        v___x_2381_ = v_____do__lift_2374_;
                        v_isShared_2382_ = v_isSharedCheck_2387_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2379_);
                        crate::leanh::lean_inc(v_a_2378_);
                        crate::leanh::lean_dec(v_____do__lift_2374_);
                        v___x_2381_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2386_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2378_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2386_, 1, v_a_2379_);
                    v___x_2384_ = v_reuseFailAlloc_2386_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2385_ = crate::leanh::lean_apply_2(
                    v_toPure_2373_,
                    crate::leanh::lean_box(0),
                    v___x_2384_,
                );
                return v___x_2385_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__3(
    mut v_toPure_2388_: *mut crate::leanh::LeanObject,
    mut v_toBind_2389_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2390_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2395_ = crate::leanh::lean_apply_1(v___y_2392_, v___y_2394_);
    v___f_2396_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__2 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2396_, 0, v___y_2393_);
    crate::leanh::lean_closure_set(v___f_2396_, 1, v_toPure_2388_);
    v___x_2397_ = crate::leanh::lean_apply_4(
        v_toBind_2389_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2395_,
        v___f_2396_,
    );
    return v___x_2397_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6(
    mut v_a_2398_: *mut crate::leanh::LeanObject,
    mut v_toPure_2399_: *mut crate::leanh::LeanObject,
    mut v_x_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2402_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2402_, 0, v_a_2398_);
    crate::leanh::lean_ctor_set(v___x_2402_, 1, v___y_2401_);
    v___x_2403_ =
        crate::leanh::lean_apply_2(v_toPure_2399_, crate::leanh::lean_box(0), v___x_2402_);
    return v___x_2403_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__6___boxed(
    mut v_a_2404_: *mut crate::leanh::LeanObject,
    mut v_toPure_2405_: *mut crate::leanh::LeanObject,
    mut v_x_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2408_ = l_Lake_EStateT_instMonad___redArg___lam__6(
        v_a_2404_,
        v_toPure_2405_,
        v_x_2406_,
        v___y_2407_,
    );
    crate::leanh::lean_dec(v_x_2406_);
    return v_res_2408_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__4(
    mut v_toPure_2409_: *mut crate::leanh::LeanObject,
    mut v_y_2410_: *mut crate::leanh::LeanObject,
    mut v___f_2411_: *mut crate::leanh::LeanObject,
    mut v_a_2412_: *mut crate::leanh::LeanObject,
    mut v___y_2413_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2414_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__6___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2414_, 0, v_a_2412_);
    crate::leanh::lean_closure_set(v___f_2414_, 1, v_toPure_2409_);
    v___x_2415_ = crate::leanh::lean_box(0);
    v___x_2416_ = crate::leanh::lean_apply_1(v_y_2410_, v___x_2415_);
    v___x_2417_ = crate::leanh::lean_apply_5(
        v___f_2411_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2416_,
        v___f_2414_,
        v___y_2413_,
    );
    return v___x_2417_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__5(
    mut v_toPure_2418_: *mut crate::leanh::LeanObject,
    mut v___f_2419_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2420_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2421_: *mut crate::leanh::LeanObject,
    mut v_x_2422_: *mut crate::leanh::LeanObject,
    mut v_y_2423_: *mut crate::leanh::LeanObject,
    mut v___y_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v___f_2419_);
    v___f_2425_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2425_, 0, v_toPure_2418_);
    crate::leanh::lean_closure_set(v___f_2425_, 1, v_y_2423_);
    crate::leanh::lean_closure_set(v___f_2425_, 2, v___f_2419_);
    v___x_2426_ = crate::leanh::lean_apply_5(
        v___f_2419_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v_x_2422_,
        v___f_2425_,
        v___y_2424_,
    );
    return v___x_2426_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__7(
    mut v_a_2427_: *mut crate::leanh::LeanObject,
    mut v_x_2428_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2438_: u8 = 0;
    let mut v_a_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2428_) == 0 {
                    v_a_2429_ = crate::leanh::lean_ctor_get(v_x_2428_, 0);
                    v_a_2430_ = crate::leanh::lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2438_ = (!crate::leanh::lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2438_ == 0 {
                        v___x_2432_ = v_x_2428_;
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2430_);
                        crate::leanh::lean_inc(v_a_2429_);
                        crate::leanh::lean_dec(v_x_2428_);
                        v___x_2432_ = crate::leanh::lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2438_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2427_);
                    v_a_2439_ = crate::leanh::lean_ctor_get(v_x_2428_, 0);
                    v_a_2440_ = crate::leanh::lean_ctor_get(v_x_2428_, 1);
                    v_isSharedCheck_2447_ = (!crate::leanh::lean_is_exclusive(v_x_2428_)) as u8;
                    if v_isSharedCheck_2447_ == 0 {
                        v___x_2442_ = v_x_2428_;
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2440_);
                        crate::leanh::lean_inc(v_a_2439_);
                        crate::leanh::lean_dec(v_x_2428_);
                        v___x_2442_ = crate::leanh::lean_box(0);
                        v_isShared_2443_ = v_isSharedCheck_2447_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2434_ = crate::leanh::lean_apply_1(v_a_2427_, v_a_2429_);
                if v_isShared_2433_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2432_, 0, v___x_2434_);
                    v___x_2436_ = v___x_2432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2437_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2437_, 1, v_a_2430_);
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
                    v_reuseFailAlloc_2446_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2446_, 0, v_a_2439_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2446_, 1, v_a_2440_);
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
    mut v_toFunctor_2448_: *mut crate::leanh::LeanObject,
    mut v_x_2449_: *mut crate::leanh::LeanObject,
    mut v_toPure_2450_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2451_) == 0 {
                    crate::leanh::lean_dec(v_toPure_2450_);
                    v_a_2452_ = crate::leanh::lean_ctor_get(v_____do__lift_2451_, 0);
                    crate::leanh::lean_inc(v_a_2452_);
                    v_a_2453_ = crate::leanh::lean_ctor_get(v_____do__lift_2451_, 1);
                    crate::leanh::lean_inc(v_a_2453_);
                    crate::leanh::lean_dec_ref_known(v_____do__lift_2451_, 2);
                    v_map_2454_ = crate::leanh::lean_ctor_get(v_toFunctor_2448_, 0);
                    crate::leanh::lean_inc(v_map_2454_);
                    crate::leanh::lean_dec_ref(v_toFunctor_2448_);
                    v___f_2455_ = crate::leanh::lean_alloc_closure(
                        l_Lake_EStateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
                        2,
                        1,
                    );
                    crate::leanh::lean_closure_set(v___f_2455_, 0, v_a_2452_);
                    v___x_2456_ = crate::leanh::lean_box(0);
                    v___x_2457_ = crate::leanh::lean_apply_2(v_x_2449_, v___x_2456_, v_a_2453_);
                    v___x_2458_ = crate::leanh::lean_apply_4(
                        v_map_2454_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_2455_,
                        v___x_2457_,
                    );
                    return v___x_2458_;
                } else {
                    crate::leanh::lean_dec(v_x_2449_);
                    crate::leanh::lean_dec_ref(v_toFunctor_2448_);
                    v_a_2459_ = crate::leanh::lean_ctor_get(v_____do__lift_2451_, 0);
                    v_a_2460_ = crate::leanh::lean_ctor_get(v_____do__lift_2451_, 1);
                    v_isSharedCheck_2468_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2451_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v___x_2462_ = v_____do__lift_2451_;
                        v_isShared_2463_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2460_);
                        crate::leanh::lean_inc(v_a_2459_);
                        crate::leanh::lean_dec(v_____do__lift_2451_);
                        v___x_2462_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2467_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2459_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2467_, 1, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2467_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2466_ = crate::leanh::lean_apply_2(
                    v_toPure_2450_,
                    crate::leanh::lean_box(0),
                    v___x_2465_,
                );
                return v___x_2466_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg___lam__9(
    mut v_toFunctor_2469_: *mut crate::leanh::LeanObject,
    mut v_toPure_2470_: *mut crate::leanh::LeanObject,
    mut v_toBind_2471_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2472_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2473_: *mut crate::leanh::LeanObject,
    mut v_f_2474_: *mut crate::leanh::LeanObject,
    mut v_x_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2477_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonad___redArg___lam__8 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2477_, 0, v_toFunctor_2469_);
    crate::leanh::lean_closure_set(v___f_2477_, 1, v_x_2475_);
    crate::leanh::lean_closure_set(v___f_2477_, 2, v_toPure_2470_);
    v___x_2478_ = crate::leanh::lean_apply_1(v_f_2474_, v___y_2476_);
    v___x_2479_ = crate::leanh::lean_apply_4(
        v_toBind_2471_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2478_,
        v___f_2477_,
    );
    return v___x_2479_;
}
pub unsafe fn l_Lake_EStateT_instMonad___redArg(
    mut v_inst_2480_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2485_: u8 = 0;
    let mut v_toFunctor_2486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2490_: u8 = 0;
    let mut v___f_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2503_: u8 = 0;
    let mut v_unused_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2507_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2481_ = crate::leanh::lean_ctor_get(v_inst_2480_, 0);
                v_toBind_2482_ = crate::leanh::lean_ctor_get(v_inst_2480_, 1);
                v_isSharedCheck_2507_ = (!crate::leanh::lean_is_exclusive(v_inst_2480_)) as u8;
                if v_isSharedCheck_2507_ == 0 {
                    v___x_2484_ = v_inst_2480_;
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_2482_);
                    crate::leanh::lean_inc(v_toApplicative_2481_);
                    crate::leanh::lean_dec(v_inst_2480_);
                    v___x_2484_ = crate::leanh::lean_box(0);
                    v_isShared_2485_ = v_isSharedCheck_2507_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2486_ = crate::leanh::lean_ctor_get(v_toApplicative_2481_, 0);
                v_toPure_2487_ = crate::leanh::lean_ctor_get(v_toApplicative_2481_, 1);
                v_isSharedCheck_2503_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2481_)) as u8;
                if v_isSharedCheck_2503_ == 0 {
                    v_unused_2504_ = crate::leanh::lean_ctor_get(v_toApplicative_2481_, 4);
                    crate::leanh::lean_dec(v_unused_2504_);
                    v_unused_2505_ = crate::leanh::lean_ctor_get(v_toApplicative_2481_, 3);
                    crate::leanh::lean_dec(v_unused_2505_);
                    v_unused_2506_ = crate::leanh::lean_ctor_get(v_toApplicative_2481_, 2);
                    crate::leanh::lean_dec(v_unused_2506_);
                    v___x_2489_ = v_toApplicative_2481_;
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toPure_2487_);
                    crate::leanh::lean_inc(v_toFunctor_2486_);
                    crate::leanh::lean_dec(v_toApplicative_2481_);
                    v___x_2489_ = crate::leanh::lean_box(0);
                    v_isShared_2490_ = v_isSharedCheck_2503_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_n(v_toBind_2482_, 2);
                crate::leanh::lean_inc_n(v_toPure_2487_, 4);
                v___f_2491_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2491_, 0, v_toPure_2487_);
                crate::leanh::lean_closure_set(v___f_2491_, 1, v_toBind_2482_);
                v___f_2492_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2492_, 0, v_toPure_2487_);
                crate::leanh::lean_closure_set(v___f_2492_, 1, v_toBind_2482_);
                crate::leanh::lean_inc_ref(v___f_2491_);
                v___f_2493_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2493_, 0, v_toPure_2487_);
                crate::leanh::lean_closure_set(v___f_2493_, 1, v___f_2491_);
                crate::leanh::lean_inc_ref(v_toFunctor_2486_);
                v___f_2494_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2494_, 0, v_toFunctor_2486_);
                crate::leanh::lean_closure_set(v___f_2494_, 1, v_toPure_2487_);
                crate::leanh::lean_closure_set(v___f_2494_, 2, v_toBind_2482_);
                v___x_2495_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2486_);
                v___f_2496_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2496_, 0, v_toPure_2487_);
                if v_isShared_2490_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2489_, 4, v___f_2492_);
                    crate::leanh::lean_ctor_set(v___x_2489_, 3, v___f_2493_);
                    crate::leanh::lean_ctor_set(v___x_2489_, 2, v___f_2494_);
                    crate::leanh::lean_ctor_set(v___x_2489_, 1, v___f_2496_);
                    crate::leanh::lean_ctor_set(v___x_2489_, 0, v___x_2495_);
                    v___x_2498_ = v___x_2489_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2502_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 0, v___x_2495_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 1, v___f_2496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___f_2494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 3, v___f_2493_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2502_, 4, v___f_2492_);
                    v___x_2498_ = v_reuseFailAlloc_2502_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2485_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2484_, 1, v___f_2491_);
                    crate::leanh::lean_ctor_set(v___x_2484_, 0, v___x_2498_);
                    v___x_2500_ = v___x_2484_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2501_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 0, v___x_2498_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2501_, 1, v___f_2491_);
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
    mut v_00_u03b5_2508_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2509_: *mut crate::leanh::LeanObject,
    mut v_m_2510_: *mut crate::leanh::LeanObject,
    mut v_inst_2511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2516_: u8 = 0;
    let mut v_toFunctor_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___f_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2534_: u8 = 0;
    let mut v_unused_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2538_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2512_ = crate::leanh::lean_ctor_get(v_inst_2511_, 0);
                v_toBind_2513_ = crate::leanh::lean_ctor_get(v_inst_2511_, 1);
                v_isSharedCheck_2538_ = (!crate::leanh::lean_is_exclusive(v_inst_2511_)) as u8;
                if v_isSharedCheck_2538_ == 0 {
                    v___x_2515_ = v_inst_2511_;
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_2513_);
                    crate::leanh::lean_inc(v_toApplicative_2512_);
                    crate::leanh::lean_dec(v_inst_2511_);
                    v___x_2515_ = crate::leanh::lean_box(0);
                    v_isShared_2516_ = v_isSharedCheck_2538_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toFunctor_2517_ = crate::leanh::lean_ctor_get(v_toApplicative_2512_, 0);
                v_toPure_2518_ = crate::leanh::lean_ctor_get(v_toApplicative_2512_, 1);
                v_isSharedCheck_2534_ =
                    (!crate::leanh::lean_is_exclusive(v_toApplicative_2512_)) as u8;
                if v_isSharedCheck_2534_ == 0 {
                    v_unused_2535_ = crate::leanh::lean_ctor_get(v_toApplicative_2512_, 4);
                    crate::leanh::lean_dec(v_unused_2535_);
                    v_unused_2536_ = crate::leanh::lean_ctor_get(v_toApplicative_2512_, 3);
                    crate::leanh::lean_dec(v_unused_2536_);
                    v_unused_2537_ = crate::leanh::lean_ctor_get(v_toApplicative_2512_, 2);
                    crate::leanh::lean_dec(v_unused_2537_);
                    v___x_2520_ = v_toApplicative_2512_;
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toPure_2518_);
                    crate::leanh::lean_inc(v_toFunctor_2517_);
                    crate::leanh::lean_dec(v_toApplicative_2512_);
                    v___x_2520_ = crate::leanh::lean_box(0);
                    v_isShared_2521_ = v_isSharedCheck_2534_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_n(v_toBind_2513_, 2);
                crate::leanh::lean_inc_n(v_toPure_2518_, 4);
                v___f_2522_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2522_, 0, v_toPure_2518_);
                crate::leanh::lean_closure_set(v___f_2522_, 1, v_toBind_2513_);
                v___f_2523_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__3 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2523_, 0, v_toPure_2518_);
                crate::leanh::lean_closure_set(v___f_2523_, 1, v_toBind_2513_);
                crate::leanh::lean_inc_ref(v___f_2522_);
                v___f_2524_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__5 as *mut core::ffi::c_void,
                    7,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2524_, 0, v_toPure_2518_);
                crate::leanh::lean_closure_set(v___f_2524_, 1, v___f_2522_);
                crate::leanh::lean_inc_ref(v_toFunctor_2517_);
                v___f_2525_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
                    8,
                    3,
                );
                crate::leanh::lean_closure_set(v___f_2525_, 0, v_toFunctor_2517_);
                crate::leanh::lean_closure_set(v___f_2525_, 1, v_toPure_2518_);
                crate::leanh::lean_closure_set(v___f_2525_, 2, v_toBind_2513_);
                v___x_2526_ = l_Lake_EStateT_instFunctor___redArg(v_toFunctor_2517_);
                v___f_2527_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instPure___redArg___lam__0 as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2527_, 0, v_toPure_2518_);
                if v_isShared_2521_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2520_, 4, v___f_2523_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 3, v___f_2524_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 2, v___f_2525_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 1, v___f_2527_);
                    crate::leanh::lean_ctor_set(v___x_2520_, 0, v___x_2526_);
                    v___x_2529_ = v___x_2520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2533_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 0, v___x_2526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 1, v___f_2527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 2, v___f_2525_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 3, v___f_2524_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2533_, 4, v___f_2523_);
                    v___x_2529_ = v_reuseFailAlloc_2533_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2516_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2515_, 1, v___f_2522_);
                    crate::leanh::lean_ctor_set(v___x_2515_, 0, v___x_2529_);
                    v___x_2531_ = v___x_2515_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2532_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 0, v___x_2529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2532_, 1, v___f_2522_);
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
    mut v_inst_2539_: *mut crate::leanh::LeanObject,
    mut v_s_2540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2541_ = crate::leanh::lean_box(0);
    v___x_2542_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2542_, 0, v___x_2541_);
    crate::leanh::lean_ctor_set(v___x_2542_, 1, v_s_2540_);
    v___x_2543_ = crate::leanh::lean_apply_2(v_inst_2539_, crate::leanh::lean_box(0), v___x_2542_);
    return v___x_2543_;
}
pub unsafe fn l_Lake_EStateT_set(
    mut v_00_u03b5_2544_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2545_: *mut crate::leanh::LeanObject,
    mut v_m_2546_: *mut crate::leanh::LeanObject,
    mut v_inst_2547_: *mut crate::leanh::LeanObject,
    mut v_s_2548_: *mut crate::leanh::LeanObject,
    mut v_x_2549_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2550_ = crate::leanh::lean_box(0);
    v___x_2551_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2551_, 0, v___x_2550_);
    crate::leanh::lean_ctor_set(v___x_2551_, 1, v_s_2548_);
    v___x_2552_ = crate::leanh::lean_apply_2(v_inst_2547_, crate::leanh::lean_box(0), v___x_2551_);
    return v___x_2552_;
}
pub unsafe fn l_Lake_EStateT_set___boxed(
    mut v_00_u03b5_2553_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2554_: *mut crate::leanh::LeanObject,
    mut v_m_2555_: *mut crate::leanh::LeanObject,
    mut v_inst_2556_: *mut crate::leanh::LeanObject,
    mut v_s_2557_: *mut crate::leanh::LeanObject,
    mut v_x_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2559_ = l_Lake_EStateT_set(
        v_00_u03b5_2553_,
        v_00_u03c3_2554_,
        v_m_2555_,
        v_inst_2556_,
        v_s_2557_,
        v_x_2558_,
    );
    crate::leanh::lean_dec(v_x_2558_);
    return v_res_2559_;
}
pub unsafe fn l_Lake_EStateT_get___redArg(
    mut v_inst_2560_: *mut crate::leanh::LeanObject,
    mut v_s_2561_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_2561_);
    v___x_2562_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2562_, 0, v_s_2561_);
    crate::leanh::lean_ctor_set(v___x_2562_, 1, v_s_2561_);
    v___x_2563_ = crate::leanh::lean_apply_2(v_inst_2560_, crate::leanh::lean_box(0), v___x_2562_);
    return v___x_2563_;
}
pub unsafe fn l_Lake_EStateT_get(
    mut v_00_u03b5_2564_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2565_: *mut crate::leanh::LeanObject,
    mut v_m_2566_: *mut crate::leanh::LeanObject,
    mut v_inst_2567_: *mut crate::leanh::LeanObject,
    mut v_s_2568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_s_2568_);
    v___x_2569_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2569_, 0, v_s_2568_);
    crate::leanh::lean_ctor_set(v___x_2569_, 1, v_s_2568_);
    v___x_2570_ = crate::leanh::lean_apply_2(v_inst_2567_, crate::leanh::lean_box(0), v___x_2569_);
    return v___x_2570_;
}
pub unsafe fn l_Lake_EStateT_modifyGet___redArg(
    mut v_inst_2571_: *mut crate::leanh::LeanObject,
    mut v_f_2572_: *mut crate::leanh::LeanObject,
    mut v_s_2573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2579_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2574_ = crate::leanh::lean_apply_1(v_f_2572_, v_s_2573_);
                v_fst_2575_ = crate::leanh::lean_ctor_get(v___x_2574_, 0);
                v_snd_2576_ = crate::leanh::lean_ctor_get(v___x_2574_, 1);
                v_isSharedCheck_2584_ = (!crate::leanh::lean_is_exclusive(v___x_2574_)) as u8;
                if v_isSharedCheck_2584_ == 0 {
                    v___x_2578_ = v___x_2574_;
                    v_isShared_2579_ = v_isSharedCheck_2584_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2576_);
                    crate::leanh::lean_inc(v_fst_2575_);
                    crate::leanh::lean_dec(v___x_2574_);
                    v___x_2578_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2583_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_fst_2575_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_snd_2576_);
                    v___x_2581_ = v_reuseFailAlloc_2583_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2582_ = crate::leanh::lean_apply_2(
                    v_inst_2571_,
                    crate::leanh::lean_box(0),
                    v___x_2581_,
                );
                return v___x_2582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_modifyGet(
    mut v_00_u03b5_2585_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2586_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2587_: *mut crate::leanh::LeanObject,
    mut v_m_2588_: *mut crate::leanh::LeanObject,
    mut v_inst_2589_: *mut crate::leanh::LeanObject,
    mut v_f_2590_: *mut crate::leanh::LeanObject,
    mut v_s_2591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2597_: u8 = 0;
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2602_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2592_ = crate::leanh::lean_apply_1(v_f_2590_, v_s_2591_);
                v_fst_2593_ = crate::leanh::lean_ctor_get(v___x_2592_, 0);
                v_snd_2594_ = crate::leanh::lean_ctor_get(v___x_2592_, 1);
                v_isSharedCheck_2602_ = (!crate::leanh::lean_is_exclusive(v___x_2592_)) as u8;
                if v_isSharedCheck_2602_ == 0 {
                    v___x_2596_ = v___x_2592_;
                    v_isShared_2597_ = v_isSharedCheck_2602_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2594_);
                    crate::leanh::lean_inc(v_fst_2593_);
                    crate::leanh::lean_dec(v___x_2592_);
                    v___x_2596_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 0, v_fst_2593_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2601_, 1, v_snd_2594_);
                    v___x_2599_ = v_reuseFailAlloc_2601_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2600_ = crate::leanh::lean_apply_2(
                    v_inst_2589_,
                    crate::leanh::lean_box(0),
                    v___x_2599_,
                );
                return v___x_2600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0(
    mut v_inst_2603_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2604_: *mut crate::leanh::LeanObject,
    mut v___y_2605_: *mut crate::leanh::LeanObject,
    mut v___y_2606_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2612_: u8 = 0;
    let mut v___x_2614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2617_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2607_ = crate::leanh::lean_apply_1(v___y_2605_, v___y_2606_);
                v_fst_2608_ = crate::leanh::lean_ctor_get(v___x_2607_, 0);
                v_snd_2609_ = crate::leanh::lean_ctor_get(v___x_2607_, 1);
                v_isSharedCheck_2617_ = (!crate::leanh::lean_is_exclusive(v___x_2607_)) as u8;
                if v_isSharedCheck_2617_ == 0 {
                    v___x_2611_ = v___x_2607_;
                    v_isShared_2612_ = v_isSharedCheck_2617_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_2609_);
                    crate::leanh::lean_inc(v_fst_2608_);
                    crate::leanh::lean_dec(v___x_2607_);
                    v___x_2611_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2616_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 0, v_fst_2608_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2616_, 1, v_snd_2609_);
                    v___x_2614_ = v_reuseFailAlloc_2616_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2615_ = crate::leanh::lean_apply_2(
                    v_inst_2603_,
                    crate::leanh::lean_box(0),
                    v___x_2614_,
                );
                return v___x_2615_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure___redArg(
    mut v_inst_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_n(v_inst_2618_, 2);
    v___f_2619_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadStateOfOfPure___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2619_, 0, v_inst_2618_);
    v___x_2620_ =
        crate::leanh::lean_alloc_closure(l_Lake_EStateT_get as *mut core::ffi::c_void, 5, 4);
    crate::leanh::lean_closure_set(v___x_2620_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2620_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2620_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2620_, 3, v_inst_2618_);
    v___x_2621_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_set___boxed as *mut core::ffi::c_void,
        6,
        4,
    );
    crate::leanh::lean_closure_set(v___x_2621_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2621_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2621_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2621_, 3, v_inst_2618_);
    v___x_2622_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2622_, 0, v___x_2620_);
    crate::leanh::lean_ctor_set(v___x_2622_, 1, v___x_2621_);
    crate::leanh::lean_ctor_set(v___x_2622_, 2, v___f_2619_);
    return v___x_2622_;
}
pub unsafe fn l_Lake_EStateT_instMonadStateOfOfPure(
    mut v_00_u03b5_2623_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2624_: *mut crate::leanh::LeanObject,
    mut v_m_2625_: *mut crate::leanh::LeanObject,
    mut v_inst_2626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2627_ = l_Lake_EStateT_instMonadStateOfOfPure___redArg(v_inst_2626_);
    return v___x_2627_;
}
pub unsafe fn l_Lake_EStateT_throw___redArg(
    mut v_inst_2628_: *mut crate::leanh::LeanObject,
    mut v_e_2629_: *mut crate::leanh::LeanObject,
    mut v_s_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2631_, 0, v_e_2629_);
    crate::leanh::lean_ctor_set(v___x_2631_, 1, v_s_2630_);
    v___x_2632_ = crate::leanh::lean_apply_2(v_inst_2628_, crate::leanh::lean_box(0), v___x_2631_);
    return v___x_2632_;
}
pub unsafe fn l_Lake_EStateT_throw(
    mut v_00_u03b5_2633_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2634_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2635_: *mut crate::leanh::LeanObject,
    mut v_m_2636_: *mut crate::leanh::LeanObject,
    mut v_inst_2637_: *mut crate::leanh::LeanObject,
    mut v_e_2638_: *mut crate::leanh::LeanObject,
    mut v_s_2639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2640_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2640_, 0, v_e_2638_);
    crate::leanh::lean_ctor_set(v___x_2640_, 1, v_s_2639_);
    v___x_2641_ = crate::leanh::lean_apply_2(v_inst_2637_, crate::leanh::lean_box(0), v___x_2640_);
    return v___x_2641_;
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg___lam__0(
    mut v_toPure_2642_: *mut crate::leanh::LeanObject,
    mut v_handle_2643_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2644_) == 0 {
        let mut v___x_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_handle_2643_);
        v___x_2645_ = crate::leanh::lean_apply_2(
            v_toPure_2642_,
            crate::leanh::lean_box(0),
            v_____do__lift_2644_,
        );
        return v___x_2645_;
    } else {
        let mut v_a_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2642_);
        v_a_2646_ = crate::leanh::lean_ctor_get(v_____do__lift_2644_, 0);
        crate::leanh::lean_inc(v_a_2646_);
        v_a_2647_ = crate::leanh::lean_ctor_get(v_____do__lift_2644_, 1);
        crate::leanh::lean_inc(v_a_2647_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2644_, 2);
        v___x_2648_ = crate::leanh::lean_apply_2(v_handle_2643_, v_a_2646_, v_a_2647_);
        return v___x_2648_;
    }
}
pub unsafe fn l_Lake_EStateT_tryCatch___redArg(
    mut v_inst_2649_: *mut crate::leanh::LeanObject,
    mut v_x_2650_: *mut crate::leanh::LeanObject,
    mut v_handle_2651_: *mut crate::leanh::LeanObject,
    mut v_s_2652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2653_ = crate::leanh::lean_ctor_get(v_inst_2649_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2653_);
    v_toBind_2654_ = crate::leanh::lean_ctor_get(v_inst_2649_, 1);
    crate::leanh::lean_inc(v_toBind_2654_);
    crate::leanh::lean_dec_ref(v_inst_2649_);
    v_toPure_2655_ = crate::leanh::lean_ctor_get(v_toApplicative_2653_, 1);
    crate::leanh::lean_inc(v_toPure_2655_);
    crate::leanh::lean_dec_ref(v_toApplicative_2653_);
    v___x_2656_ = crate::leanh::lean_apply_1(v_x_2650_, v_s_2652_);
    v___f_2657_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2657_, 0, v_toPure_2655_);
    crate::leanh::lean_closure_set(v___f_2657_, 1, v_handle_2651_);
    v___x_2658_ = crate::leanh::lean_apply_4(
        v_toBind_2654_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2656_,
        v___f_2657_,
    );
    return v___x_2658_;
}
pub unsafe fn l_Lake_EStateT_tryCatch(
    mut v_00_u03b5_2659_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2660_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2661_: *mut crate::leanh::LeanObject,
    mut v_m_2662_: *mut crate::leanh::LeanObject,
    mut v_inst_2663_: *mut crate::leanh::LeanObject,
    mut v_x_2664_: *mut crate::leanh::LeanObject,
    mut v_handle_2665_: *mut crate::leanh::LeanObject,
    mut v_s_2666_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2667_ = crate::leanh::lean_ctor_get(v_inst_2663_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2667_);
    v_toBind_2668_ = crate::leanh::lean_ctor_get(v_inst_2663_, 1);
    crate::leanh::lean_inc(v_toBind_2668_);
    crate::leanh::lean_dec_ref(v_inst_2663_);
    v_toPure_2669_ = crate::leanh::lean_ctor_get(v_toApplicative_2667_, 1);
    crate::leanh::lean_inc(v_toPure_2669_);
    crate::leanh::lean_dec_ref(v_toApplicative_2667_);
    v___x_2670_ = crate::leanh::lean_apply_1(v_x_2664_, v_s_2666_);
    v___f_2671_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_tryCatch___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2671_, 0, v_toPure_2669_);
    crate::leanh::lean_closure_set(v___f_2671_, 1, v_handle_2665_);
    v___x_2672_ = crate::leanh::lean_apply_4(
        v_toBind_2668_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2670_,
        v___f_2671_,
    );
    return v___x_2672_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0(
    mut v_toPure_2673_: *mut crate::leanh::LeanObject,
    mut v___y_2674_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2675_) == 0 {
        let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___y_2674_);
        v___x_2676_ = crate::leanh::lean_apply_2(
            v_toPure_2673_,
            crate::leanh::lean_box(0),
            v_____do__lift_2675_,
        );
        return v___x_2676_;
    } else {
        let mut v_a_2677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2673_);
        v_a_2677_ = crate::leanh::lean_ctor_get(v_____do__lift_2675_, 0);
        crate::leanh::lean_inc(v_a_2677_);
        v_a_2678_ = crate::leanh::lean_ctor_get(v_____do__lift_2675_, 1);
        crate::leanh::lean_inc(v_a_2678_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2675_, 2);
        v___x_2679_ = crate::leanh::lean_apply_2(v___y_2674_, v_a_2677_, v_a_2678_);
        return v___x_2679_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1(
    mut v_toPure_2680_: *mut crate::leanh::LeanObject,
    mut v_toBind_2681_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2682_: *mut crate::leanh::LeanObject,
    mut v___y_2683_: *mut crate::leanh::LeanObject,
    mut v___y_2684_: *mut crate::leanh::LeanObject,
    mut v___y_2685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2686_ = crate::leanh::lean_apply_1(v___y_2683_, v___y_2685_);
    v___f_2687_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2687_, 0, v_toPure_2680_);
    crate::leanh::lean_closure_set(v___f_2687_, 1, v___y_2684_);
    v___x_2688_ = crate::leanh::lean_apply_4(
        v_toBind_2681_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2686_,
        v___f_2687_,
    );
    return v___x_2688_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2(
    mut v_toPure_2689_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2693_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2693_, 0, v___y_2691_);
    crate::leanh::lean_ctor_set(v___x_2693_, 1, v___y_2692_);
    v___x_2694_ =
        crate::leanh::lean_apply_2(v_toPure_2689_, crate::leanh::lean_box(0), v___x_2693_);
    return v___x_2694_;
}
pub unsafe fn l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(
    mut v_inst_2695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2700_: u8 = 0;
    let mut v_toPure_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_2696_ = crate::leanh::lean_ctor_get(v_inst_2695_, 0);
                v_toBind_2697_ = crate::leanh::lean_ctor_get(v_inst_2695_, 1);
                v_isSharedCheck_2707_ = (!crate::leanh::lean_is_exclusive(v_inst_2695_)) as u8;
                if v_isSharedCheck_2707_ == 0 {
                    v___x_2699_ = v_inst_2695_;
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_toBind_2697_);
                    crate::leanh::lean_inc(v_toApplicative_2696_);
                    crate::leanh::lean_dec(v_inst_2695_);
                    v___x_2699_ = crate::leanh::lean_box(0);
                    v_isShared_2700_ = v_isSharedCheck_2707_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_2701_ = crate::leanh::lean_ctor_get(v_toApplicative_2696_, 1);
                crate::leanh::lean_inc_n(v_toPure_2701_, 2);
                crate::leanh::lean_dec_ref(v_toApplicative_2696_);
                v___f_2702_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    2,
                );
                crate::leanh::lean_closure_set(v___f_2702_, 0, v_toPure_2701_);
                crate::leanh::lean_closure_set(v___f_2702_, 1, v_toBind_2697_);
                v___f_2703_ = crate::leanh::lean_alloc_closure(
                    l_Lake_EStateT_instMonadExceptOfOfMonad___redArg___lam__2
                        as *mut core::ffi::c_void,
                    4,
                    1,
                );
                crate::leanh::lean_closure_set(v___f_2703_, 0, v_toPure_2701_);
                if v_isShared_2700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2699_, 1, v___f_2702_);
                    crate::leanh::lean_ctor_set(v___x_2699_, 0, v___f_2703_);
                    v___x_2705_ = v___x_2699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2706_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 0, v___f_2703_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2706_, 1, v___f_2702_);
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
    mut v_00_u03b5_2708_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2709_: *mut crate::leanh::LeanObject,
    mut v_m_2710_: *mut crate::leanh::LeanObject,
    mut v_inst_2711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2712_ = l_Lake_EStateT_instMonadExceptOfOfMonad___redArg(v_inst_2711_);
    return v___x_2712_;
}
pub unsafe fn l_Lake_EStateT_orElse___redArg___lam__0(
    mut v_toPure_2713_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_2714_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_2715_) == 0 {
        let mut v___x_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_u2082_2714_);
        v___x_2716_ = crate::leanh::lean_apply_2(
            v_toPure_2713_,
            crate::leanh::lean_box(0),
            v_____do__lift_2715_,
        );
        return v___x_2716_;
    } else {
        let mut v_a_2717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_2713_);
        v_a_2717_ = crate::leanh::lean_ctor_get(v_____do__lift_2715_, 1);
        crate::leanh::lean_inc(v_a_2717_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_2715_, 2);
        v___x_2718_ = crate::leanh::lean_box(0);
        v___x_2719_ = crate::leanh::lean_apply_2(v_x_u2082_2714_, v___x_2718_, v_a_2717_);
        return v___x_2719_;
    }
}
pub unsafe fn l_Lake_EStateT_orElse___redArg(
    mut v_inst_2720_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_2721_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_2722_: *mut crate::leanh::LeanObject,
    mut v_s_2723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2724_ = crate::leanh::lean_ctor_get(v_inst_2720_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2724_);
    v_toBind_2725_ = crate::leanh::lean_ctor_get(v_inst_2720_, 1);
    crate::leanh::lean_inc(v_toBind_2725_);
    crate::leanh::lean_dec_ref(v_inst_2720_);
    v_toPure_2726_ = crate::leanh::lean_ctor_get(v_toApplicative_2724_, 1);
    crate::leanh::lean_inc(v_toPure_2726_);
    crate::leanh::lean_dec_ref(v_toApplicative_2724_);
    v___x_2727_ = crate::leanh::lean_apply_1(v_x_u2081_2721_, v_s_2723_);
    v___f_2728_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2728_, 0, v_toPure_2726_);
    crate::leanh::lean_closure_set(v___f_2728_, 1, v_x_u2082_2722_);
    v___x_2729_ = crate::leanh::lean_apply_4(
        v_toBind_2725_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2727_,
        v___f_2728_,
    );
    return v___x_2729_;
}
pub unsafe fn l_Lake_EStateT_orElse(
    mut v_00_u03b5_2730_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2731_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2732_: *mut crate::leanh::LeanObject,
    mut v_m_2733_: *mut crate::leanh::LeanObject,
    mut v_inst_2734_: *mut crate::leanh::LeanObject,
    mut v_x_u2081_2735_: *mut crate::leanh::LeanObject,
    mut v_x_u2082_2736_: *mut crate::leanh::LeanObject,
    mut v_s_2737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2738_ = crate::leanh::lean_ctor_get(v_inst_2734_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2738_);
    v_toBind_2739_ = crate::leanh::lean_ctor_get(v_inst_2734_, 1);
    crate::leanh::lean_inc(v_toBind_2739_);
    crate::leanh::lean_dec_ref(v_inst_2734_);
    v_toPure_2740_ = crate::leanh::lean_ctor_get(v_toApplicative_2738_, 1);
    crate::leanh::lean_inc(v_toPure_2740_);
    crate::leanh::lean_dec_ref(v_toApplicative_2738_);
    v___x_2741_ = crate::leanh::lean_apply_1(v_x_u2081_2735_, v_s_2737_);
    v___f_2742_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_orElse___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2742_, 0, v_toPure_2740_);
    crate::leanh::lean_closure_set(v___f_2742_, 1, v_x_u2082_2736_);
    v___x_2743_ = crate::leanh::lean_apply_4(
        v_toBind_2739_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2741_,
        v___f_2742_,
    );
    return v___x_2743_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad___redArg(
    mut v_inst_2744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2745_ =
        crate::leanh::lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    crate::leanh::lean_closure_set(v___x_2745_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2745_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2745_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2745_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2745_, 4, v_inst_2744_);
    return v___x_2745_;
}
pub unsafe fn l_Lake_EStateT_instOrElseOfMonad(
    mut v_00_u03b5_2746_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2747_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2748_: *mut crate::leanh::LeanObject,
    mut v_m_2749_: *mut crate::leanh::LeanObject,
    mut v_inst_2750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2751_ =
        crate::leanh::lean_alloc_closure(l_Lake_EStateT_orElse as *mut core::ffi::c_void, 8, 5);
    crate::leanh::lean_closure_set(v___x_2751_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2751_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2751_, 2, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2751_, 3, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_2751_, 4, v_inst_2750_);
    return v___x_2751_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept___redArg___lam__0(
    mut v_f_2752_: *mut crate::leanh::LeanObject,
    mut v_x_2753_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2758_: u8 = 0;
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_a_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2772_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2753_) == 0 {
                    crate::leanh::lean_dec(v_f_2752_);
                    v_a_2754_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                    v_a_2755_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2762_ = (!crate::leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v___x_2757_ = v_x_2753_;
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2755_);
                        crate::leanh::lean_inc(v_a_2754_);
                        crate::leanh::lean_dec(v_x_2753_);
                        v___x_2757_ = crate::leanh::lean_box(0);
                        v_isShared_2758_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2763_ = crate::leanh::lean_ctor_get(v_x_2753_, 0);
                    v_a_2764_ = crate::leanh::lean_ctor_get(v_x_2753_, 1);
                    v_isSharedCheck_2772_ = (!crate::leanh::lean_is_exclusive(v_x_2753_)) as u8;
                    if v_isSharedCheck_2772_ == 0 {
                        v___x_2766_ = v_x_2753_;
                        v_isShared_2767_ = v_isSharedCheck_2772_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2764_);
                        crate::leanh::lean_inc(v_a_2763_);
                        crate::leanh::lean_dec(v_x_2753_);
                        v___x_2766_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_2761_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 0, v_a_2754_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2761_, 1, v_a_2755_);
                    v___x_2760_ = v_reuseFailAlloc_2761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2760_;
            }
            3 => {
                v___x_2768_ = crate::leanh::lean_apply_1(v_f_2752_, v_a_2763_);
                if v_isShared_2767_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2766_, 0, v___x_2768_);
                    v___x_2770_ = v___x_2766_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2771_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v___x_2768_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_a_2764_);
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
    mut v_inst_2773_: *mut crate::leanh::LeanObject,
    mut v_f_2774_: *mut crate::leanh::LeanObject,
    mut v_x_2775_: *mut crate::leanh::LeanObject,
    mut v_s_2776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2777_ = crate::leanh::lean_ctor_get(v_inst_2773_, 0);
    crate::leanh::lean_inc(v_map_2777_);
    crate::leanh::lean_dec_ref(v_inst_2773_);
    v___f_2778_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2778_, 0, v_f_2774_);
    v___x_2779_ = crate::leanh::lean_apply_1(v_x_2775_, v_s_2776_);
    v___x_2780_ = crate::leanh::lean_apply_4(
        v_map_2777_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2778_,
        v___x_2779_,
    );
    return v___x_2780_;
}
pub unsafe fn l_Lake_EStateT_adaptExcept(
    mut v_00_u03b5_2781_: *mut crate::leanh::LeanObject,
    mut v_00_u03b5_x27_2782_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2784_: *mut crate::leanh::LeanObject,
    mut v_m_2785_: *mut crate::leanh::LeanObject,
    mut v_inst_2786_: *mut crate::leanh::LeanObject,
    mut v_f_2787_: *mut crate::leanh::LeanObject,
    mut v_x_2788_: *mut crate::leanh::LeanObject,
    mut v_s_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_map_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_map_2790_ = crate::leanh::lean_ctor_get(v_inst_2786_, 0);
    crate::leanh::lean_inc(v_map_2790_);
    crate::leanh::lean_dec_ref(v_inst_2786_);
    v___f_2791_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_adaptExcept___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2791_, 0, v_f_2787_);
    v___x_2792_ = crate::leanh::lean_apply_1(v_x_2788_, v_s_2789_);
    v___x_2793_ = crate::leanh::lean_apply_4(
        v_map_2790_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_2791_,
        v___x_2792_,
    );
    return v___x_2793_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__0(
    mut v_a_2794_: *mut crate::leanh::LeanObject,
    mut v_toPure_2795_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2801_: u8 = 0;
    let mut v___x_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2796_) == 0 {
                    v_a_2797_ = crate::leanh::lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2798_ = crate::leanh::lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2807_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2807_ == 0 {
                        v___x_2800_ = v_____do__lift_2796_;
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2798_);
                        crate::leanh::lean_inc(v_a_2797_);
                        crate::leanh::lean_dec(v_____do__lift_2796_);
                        v___x_2800_ = crate::leanh::lean_box(0);
                        v_isShared_2801_ = v_isSharedCheck_2807_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2794_);
                    v_a_2808_ = crate::leanh::lean_ctor_get(v_____do__lift_2796_, 0);
                    v_a_2809_ = crate::leanh::lean_ctor_get(v_____do__lift_2796_, 1);
                    v_isSharedCheck_2817_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2796_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2811_ = v_____do__lift_2796_;
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2809_);
                        crate::leanh::lean_inc(v_a_2808_);
                        crate::leanh::lean_dec(v_____do__lift_2796_);
                        v___x_2811_ = crate::leanh::lean_box(0);
                        v_isShared_2812_ = v_isSharedCheck_2817_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2802_, 0, v_a_2794_);
                crate::leanh::lean_ctor_set(v___x_2802_, 1, v_a_2797_);
                if v_isShared_2801_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2800_, 0, v___x_2802_);
                    v___x_2804_ = v___x_2800_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v___x_2802_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 1, v_a_2798_);
                    v___x_2804_ = v_reuseFailAlloc_2806_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2805_ = crate::leanh::lean_apply_2(
                    v_toPure_2795_,
                    crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_2816_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2808_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 1, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2816_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2815_ = crate::leanh::lean_apply_2(
                    v_toPure_2795_,
                    crate::leanh::lean_box(0),
                    v___x_2814_,
                );
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__1(
    mut v_a_2818_: *mut crate::leanh::LeanObject,
    mut v_toPure_2819_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_2820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2829_: u8 = 0;
    let mut v_unused_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2835_: u8 = 0;
    let mut v___x_2837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2840_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_____do__lift_2820_) == 0 {
                    v_a_2821_ = crate::leanh::lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2829_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2829_ == 0 {
                        v_unused_2830_ = crate::leanh::lean_ctor_get(v_____do__lift_2820_, 0);
                        crate::leanh::lean_dec(v_unused_2830_);
                        v___x_2823_ = v_____do__lift_2820_;
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2821_);
                        crate::leanh::lean_dec(v_____do__lift_2820_);
                        v___x_2823_ = crate::leanh::lean_box(0);
                        v_isShared_2824_ = v_isSharedCheck_2829_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2818_);
                    v_a_2831_ = crate::leanh::lean_ctor_get(v_____do__lift_2820_, 0);
                    v_a_2832_ = crate::leanh::lean_ctor_get(v_____do__lift_2820_, 1);
                    v_isSharedCheck_2840_ =
                        (!crate::leanh::lean_is_exclusive(v_____do__lift_2820_)) as u8;
                    if v_isSharedCheck_2840_ == 0 {
                        v___x_2834_ = v_____do__lift_2820_;
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2832_);
                        crate::leanh::lean_inc(v_a_2831_);
                        crate::leanh::lean_dec(v_____do__lift_2820_);
                        v___x_2834_ = crate::leanh::lean_box(0);
                        v_isShared_2835_ = v_isSharedCheck_2840_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2824_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2823_, 1);
                    crate::leanh::lean_ctor_set(v___x_2823_, 0, v_a_2818_);
                    v___x_2826_ = v___x_2823_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 0, v_a_2818_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_a_2821_);
                    v___x_2826_ = v_reuseFailAlloc_2828_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2827_ = crate::leanh::lean_apply_2(
                    v_toPure_2819_,
                    crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_2839_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 0, v_a_2831_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2839_, 1, v_a_2832_);
                    v___x_2837_ = v_reuseFailAlloc_2839_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2838_ = crate::leanh::lean_apply_2(
                    v_toPure_2819_,
                    crate::leanh::lean_box(0),
                    v___x_2837_,
                );
                return v___x_2838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg___lam__2(
    mut v_toPure_2841_: *mut crate::leanh::LeanObject,
    mut v_f_2842_: *mut crate::leanh::LeanObject,
    mut v_toBind_2843_: *mut crate::leanh::LeanObject,
    mut v_r_2844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_2844_) == 0 {
        let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2845_ = crate::leanh::lean_ctor_get(v_r_2844_, 0);
        crate::leanh::lean_inc_n(v_a_2845_, 2);
        v_a_2846_ = crate::leanh::lean_ctor_get(v_r_2844_, 1);
        crate::leanh::lean_inc(v_a_2846_);
        crate::leanh::lean_dec_ref_known(v_r_2844_, 2);
        v___f_2847_ = crate::leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2847_, 0, v_a_2845_);
        crate::leanh::lean_closure_set(v___f_2847_, 1, v_toPure_2841_);
        v___x_2848_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2848_, 0, v_a_2845_);
        v___x_2849_ = crate::leanh::lean_apply_2(v_f_2842_, v___x_2848_, v_a_2846_);
        v___x_2850_ = crate::leanh::lean_apply_4(
            v_toBind_2843_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2849_,
            v___f_2847_,
        );
        return v___x_2850_;
    } else {
        let mut v_a_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2851_ = crate::leanh::lean_ctor_get(v_r_2844_, 0);
        crate::leanh::lean_inc(v_a_2851_);
        v_a_2852_ = crate::leanh::lean_ctor_get(v_r_2844_, 1);
        crate::leanh::lean_inc(v_a_2852_);
        crate::leanh::lean_dec_ref_known(v_r_2844_, 2);
        v___f_2853_ = crate::leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2853_, 0, v_a_2851_);
        crate::leanh::lean_closure_set(v___f_2853_, 1, v_toPure_2841_);
        v___x_2854_ = crate::leanh::lean_box(0);
        v___x_2855_ = crate::leanh::lean_apply_2(v_f_2842_, v___x_2854_, v_a_2852_);
        v___x_2856_ = crate::leanh::lean_apply_4(
            v_toBind_2843_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2855_,
            v___f_2853_,
        );
        return v___x_2856_;
    }
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27___redArg(
    mut v_inst_2857_: *mut crate::leanh::LeanObject,
    mut v_x_2858_: *mut crate::leanh::LeanObject,
    mut v_f_2859_: *mut crate::leanh::LeanObject,
    mut v_s_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2861_ = crate::leanh::lean_ctor_get(v_inst_2857_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2861_);
    v_toBind_2862_ = crate::leanh::lean_ctor_get(v_inst_2857_, 1);
    crate::leanh::lean_inc_n(v_toBind_2862_, 2);
    crate::leanh::lean_dec_ref(v_inst_2857_);
    v_toPure_2863_ = crate::leanh::lean_ctor_get(v_toApplicative_2861_, 1);
    crate::leanh::lean_inc(v_toPure_2863_);
    crate::leanh::lean_dec_ref(v_toApplicative_2861_);
    v___x_2864_ = crate::leanh::lean_apply_1(v_x_2858_, v_s_2860_);
    v___f_2865_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2865_, 0, v_toPure_2863_);
    crate::leanh::lean_closure_set(v___f_2865_, 1, v_f_2859_);
    crate::leanh::lean_closure_set(v___f_2865_, 2, v_toBind_2862_);
    v___x_2866_ = crate::leanh::lean_apply_4(
        v_toBind_2862_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2864_,
        v___f_2865_,
    );
    return v___x_2866_;
}
pub unsafe fn l_Lake_EStateT_tryFinally_x27(
    mut v_00_u03b5_2867_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2868_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2869_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2870_: *mut crate::leanh::LeanObject,
    mut v_m_2871_: *mut crate::leanh::LeanObject,
    mut v_inst_2872_: *mut crate::leanh::LeanObject,
    mut v_x_2873_: *mut crate::leanh::LeanObject,
    mut v_f_2874_: *mut crate::leanh::LeanObject,
    mut v_s_2875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2876_ = crate::leanh::lean_ctor_get(v_inst_2872_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2876_);
    v_toBind_2877_ = crate::leanh::lean_ctor_get(v_inst_2872_, 1);
    crate::leanh::lean_inc_n(v_toBind_2877_, 2);
    crate::leanh::lean_dec_ref(v_inst_2872_);
    v_toPure_2878_ = crate::leanh::lean_ctor_get(v_toApplicative_2876_, 1);
    crate::leanh::lean_inc(v_toPure_2878_);
    crate::leanh::lean_dec_ref(v_toApplicative_2876_);
    v___x_2879_ = crate::leanh::lean_apply_1(v_x_2873_, v_s_2875_);
    v___f_2880_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_tryFinally_x27___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2880_, 0, v_toPure_2878_);
    crate::leanh::lean_closure_set(v___f_2880_, 1, v_f_2874_);
    crate::leanh::lean_closure_set(v___f_2880_, 2, v_toBind_2877_);
    v___x_2881_ = crate::leanh::lean_apply_4(
        v_toBind_2877_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2879_,
        v___f_2880_,
    );
    return v___x_2881_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2(
    mut v_toPure_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v_toBind_2884_: *mut crate::leanh::LeanObject,
    mut v_r_2885_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_r_2885_) == 0 {
        let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2886_ = crate::leanh::lean_ctor_get(v_r_2885_, 0);
        crate::leanh::lean_inc_n(v_a_2886_, 2);
        v_a_2887_ = crate::leanh::lean_ctor_get(v_r_2885_, 1);
        crate::leanh::lean_inc(v_a_2887_);
        crate::leanh::lean_dec_ref_known(v_r_2885_, 2);
        v___f_2888_ = crate::leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__0 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2888_, 0, v_a_2886_);
        crate::leanh::lean_closure_set(v___f_2888_, 1, v_toPure_2882_);
        v___x_2889_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2889_, 0, v_a_2886_);
        v___x_2890_ = crate::leanh::lean_apply_2(v___y_2883_, v___x_2889_, v_a_2887_);
        v___x_2891_ = crate::leanh::lean_apply_4(
            v_toBind_2884_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2890_,
            v___f_2888_,
        );
        return v___x_2891_;
    } else {
        let mut v_a_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_2894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_2892_ = crate::leanh::lean_ctor_get(v_r_2885_, 0);
        crate::leanh::lean_inc(v_a_2892_);
        v_a_2893_ = crate::leanh::lean_ctor_get(v_r_2885_, 1);
        crate::leanh::lean_inc(v_a_2893_);
        crate::leanh::lean_dec_ref_known(v_r_2885_, 2);
        v___f_2894_ = crate::leanh::lean_alloc_closure(
            l_Lake_EStateT_tryFinally_x27___redArg___lam__1 as *mut core::ffi::c_void,
            3,
            2,
        );
        crate::leanh::lean_closure_set(v___f_2894_, 0, v_a_2892_);
        crate::leanh::lean_closure_set(v___f_2894_, 1, v_toPure_2882_);
        v___x_2895_ = crate::leanh::lean_box(0);
        v___x_2896_ = crate::leanh::lean_apply_2(v___y_2883_, v___x_2895_, v_a_2893_);
        v___x_2897_ = crate::leanh::lean_apply_4(
            v_toBind_2884_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_2896_,
            v___f_2894_,
        );
        return v___x_2897_;
    }
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0(
    mut v_inst_2898_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2899_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_2900_: *mut crate::leanh::LeanObject,
    mut v___y_2901_: *mut crate::leanh::LeanObject,
    mut v___y_2902_: *mut crate::leanh::LeanObject,
    mut v___y_2903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2904_ = crate::leanh::lean_ctor_get(v_inst_2898_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_2904_);
    v_toBind_2905_ = crate::leanh::lean_ctor_get(v_inst_2898_, 1);
    crate::leanh::lean_inc_n(v_toBind_2905_, 2);
    crate::leanh::lean_dec_ref(v_inst_2898_);
    v_toPure_2906_ = crate::leanh::lean_ctor_get(v_toApplicative_2904_, 1);
    crate::leanh::lean_inc(v_toPure_2906_);
    crate::leanh::lean_dec_ref(v_toApplicative_2904_);
    v___x_2907_ = crate::leanh::lean_apply_1(v___y_2901_, v___y_2903_);
    v___f_2908_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_2908_, 0, v_toPure_2906_);
    crate::leanh::lean_closure_set(v___f_2908_, 1, v___y_2902_);
    crate::leanh::lean_closure_set(v___f_2908_, 2, v_toBind_2905_);
    v___x_2909_ = crate::leanh::lean_apply_4(
        v_toBind_2905_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_2907_,
        v___f_2908_,
    );
    return v___x_2909_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad___redArg(
    mut v_inst_2910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2911_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2911_, 0, v_inst_2910_);
    return v___f_2911_;
}
pub unsafe fn l_Lake_EStateT_instMonadFinallyOfMonad(
    mut v_00_u03b5_2912_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2913_: *mut crate::leanh::LeanObject,
    mut v_m_2914_: *mut crate::leanh::LeanObject,
    mut v_inst_2915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_2916_ = crate::leanh::lean_alloc_closure(
        l_Lake_EStateT_instMonadFinallyOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_2916_, 0, v_inst_2915_);
    return v___f_2916_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM___redArg(
    mut v_f_2917_: *mut crate::leanh::LeanObject,
    mut v_s_2918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2919_ = crate::leanh::lean_apply_1(v_f_2917_, v_s_2918_);
    v___x_2920_ = l_Lake_EResult_ofEStateMResult___redArg(v___x_2919_);
    return v___x_2920_;
}
pub unsafe fn l_Lake_EStateT_ofEStateM(
    mut v_00_u03b5_2921_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2922_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2923_: *mut crate::leanh::LeanObject,
    mut v_f_2924_: *mut crate::leanh::LeanObject,
    mut v_s_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2926_ = l_Lake_EStateT_ofEStateM___redArg(v_f_2924_, v_s_2925_);
    return v___x_2926_;
}
pub unsafe fn l_Lake_EStateT_toEStateM___redArg(
    mut v_f_2927_: *mut crate::leanh::LeanObject,
    mut v_s_2928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2929_ = crate::leanh::lean_apply_1(v_f_2927_, v_s_2928_);
    v___x_2930_ = l_Lake_EResult_toEStateMResult___redArg(v___x_2929_);
    return v___x_2930_;
}
pub unsafe fn l_Lake_EStateT_toEStateM(
    mut v_00_u03b5_2931_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_2932_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_2933_: *mut crate::leanh::LeanObject,
    mut v_f_2934_: *mut crate::leanh::LeanObject,
    mut v_s_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Lake_EStateT_toEStateM___redArg(v_f_2934_, v_s_2935_);
    return v___x_2936_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_EStateT(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_EStateT(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_EStateT(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Control_State(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_EStateT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_EStateT(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_EStateT(builtin);
}

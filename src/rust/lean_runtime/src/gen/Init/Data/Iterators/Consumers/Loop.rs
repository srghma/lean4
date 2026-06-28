// Lean compiler output
// Module: Init.Data.Iterators.Consumers.Loop
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.Iterators.Consumers.Partial Init.Data.Iterators.Consumers.Total
use crate::r#gen::Init::Control::Basic::l_instForInOfForIn_x27___redArg___lam__1;
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Partial::{
    initialize_Init_Data_Iterators_Consumers_Partial,
    runtime_initialize_Init_Data_Iterators_Consumers_Partial,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Total::{
    initialize_Init_Data_Iterators_Consumers_Total,
    runtime_initialize_Init_Data_Iterators_Consumers_Total,
};
use crate::lean_imports_rs::Init::Prelude::lean_nat_add;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static l_Std_Iter_instForIn_x27___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Iter_instForIn_x27___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Iter_instForIn_x27___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_instForIn_x27___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_foldM___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iter_foldM___redArg___lam__1 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iter_foldM___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_foldM___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_first_x3f___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Iter_first_x3f___redArg___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Iter_first_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_first_x3f___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_first_x3f___redArg___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Iter_first_x3f___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Iter_first_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_first_x3f___redArg___closed__1_value) as *mut LeanObject;
pub static l_Std_Iter_isEmpty___redArg___lam__1___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Std_Iter_isEmpty___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_isEmpty___redArg___lam__1___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_isEmpty___redArg___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Iter_isEmpty___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Iter_isEmpty___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_isEmpty___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_length___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iter_length___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iter_length___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_length___redArg___closed__0_value) as *mut LeanObject;
pub static l_Std_Iter_length___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Iter_length___redArg___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Iter_length___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Iter_length___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Std_Iter_instForIn_x27___redArg___lam__0(
    mut v_x_1646_: *mut LeanObject,
    mut v_x_1647_: *mut LeanObject,
    mut v_f_1648_: *mut LeanObject,
    mut v_c_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1650_ = lean_apply_1(v_f_1648_, v_c_1649_);
    return v___x_1650_;
}
pub unsafe fn l_Std_Iter_instForIn_x27___redArg___lam__1(
    mut v_toPure_1651_: *mut LeanObject,
    mut v_____do__lift_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    v___x_1653_ = lean_apply_2(v_toPure_1651_, lean_box(0), v_____do__lift_1652_);
    return v___x_1653_;
}
pub unsafe fn l_Std_Iter_instForIn_x27___redArg___lam__2(
    mut v_f_1654_: *mut LeanObject,
    mut v_toBind_1655_: *mut LeanObject,
    mut v___f_1656_: *mut LeanObject,
    mut v_x1_1657_: *mut LeanObject,
    mut v_x2_1658_: *mut LeanObject,
    mut v_x3_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1660_ = lean_apply_3(v_f_1654_, v_x1_1657_, lean_box(0), v_x3_1659_);
    v___x_1661_ = lean_apply_4(
        v_toBind_1655_,
        lean_box(0),
        lean_box(0),
        v___x_1660_,
        v___f_1656_,
    );
    return v___x_1661_;
}
pub unsafe fn l_Std_Iter_instForIn_x27___redArg___lam__3(
    mut v_inst_1662_: *mut LeanObject,
    mut v_inst_1663_: *mut LeanObject,
    mut v___f_1664_: *mut LeanObject,
    mut v_00_u03b2_1665_: *mut LeanObject,
    mut v_it_1666_: *mut LeanObject,
    mut v_init_1667_: *mut LeanObject,
    mut v_f_1668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1669_ = lean_ctor_get(v_inst_1662_, 0);
    lean_inc_ref(v_toApplicative_1669_);
    v_toBind_1670_ = lean_ctor_get(v_inst_1662_, 1);
    lean_inc(v_toBind_1670_);
    lean_dec_ref(v_inst_1662_);
    v_toPure_1671_ = lean_ctor_get(v_toApplicative_1669_, 1);
    lean_inc(v_toPure_1671_);
    lean_dec_ref(v_toApplicative_1669_);
    v___f_1672_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1672_, 0, v_toPure_1671_);
    v___f_1673_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__2 as *mut core::ffi::c_void,
        6,
        3,
    );
    lean_closure_set(v___f_1673_, 0, v_f_1668_);
    lean_closure_set(v___f_1673_, 1, v_toBind_1670_);
    lean_closure_set(v___f_1673_, 2, v___f_1672_);
    v___x_1674_ = lean_apply_6(
        v_inst_1663_,
        v___f_1664_,
        lean_box(0),
        lean_box(0),
        v_it_1666_,
        v_init_1667_,
        v___f_1673_,
    );
    return v___x_1674_;
}
pub unsafe fn l_Std_Iter_instForIn_x27___redArg(
    mut v_inst_1676_: *mut LeanObject,
    mut v_inst_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1679_: *mut LeanObject = core::ptr::null_mut();
    v___f_1678_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1679_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1679_, 0, v_inst_1676_);
    lean_closure_set(v___f_1679_, 1, v_inst_1677_);
    lean_closure_set(v___f_1679_, 2, v___f_1678_);
    return v___f_1679_;
}
pub unsafe fn l_Std_Iter_instForIn_x27(
    mut v_00_u03b1_1680_: *mut LeanObject,
    mut v_00_u03b2_1681_: *mut LeanObject,
    mut v_n_1682_: *mut LeanObject,
    mut v_inst_1683_: *mut LeanObject,
    mut v_inst_1684_: *mut LeanObject,
    mut v_inst_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1687_: *mut LeanObject = core::ptr::null_mut();
    v___f_1686_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1687_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1687_, 0, v_inst_1683_);
    lean_closure_set(v___f_1687_, 1, v_inst_1685_);
    lean_closure_set(v___f_1687_, 2, v___f_1686_);
    return v___f_1687_;
}
pub unsafe fn l_Std_Iter_instForIn_x27___boxed(
    mut v_00_u03b1_1688_: *mut LeanObject,
    mut v_00_u03b2_1689_: *mut LeanObject,
    mut v_n_1690_: *mut LeanObject,
    mut v_inst_1691_: *mut LeanObject,
    mut v_inst_1692_: *mut LeanObject,
    mut v_inst_1693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1694_: *mut LeanObject = core::ptr::null_mut();
    v_res_1694_ = l_Std_Iter_instForIn_x27(
        v_00_u03b1_1688_,
        v_00_u03b2_1689_,
        v_n_1690_,
        v_inst_1691_,
        v_inst_1692_,
        v_inst_1693_,
    );
    lean_dec(v_inst_1692_);
    return v_res_1694_;
}
pub unsafe fn l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(
    mut v_inst_1695_: *mut LeanObject,
    mut v_inst_1696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1699_: *mut LeanObject = core::ptr::null_mut();
    v___f_1697_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1698_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1698_, 0, v_inst_1695_);
    lean_closure_set(v___f_1698_, 1, v_inst_1696_);
    lean_closure_set(v___f_1698_, 2, v___f_1697_);
    v___f_1699_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1699_, 0, v___f_1698_);
    return v___f_1699_;
}
pub unsafe fn l_Std_instForInIterOfMonadOfIteratorLoopId(
    mut v_00_u03b1_1700_: *mut LeanObject,
    mut v_00_u03b2_1701_: *mut LeanObject,
    mut v_n_1702_: *mut LeanObject,
    mut v_inst_1703_: *mut LeanObject,
    mut v_inst_1704_: *mut LeanObject,
    mut v_inst_1705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1706_: *mut LeanObject = core::ptr::null_mut();
    v___x_1706_ = l_Std_instForInIterOfMonadOfIteratorLoopId___redArg(v_inst_1703_, v_inst_1705_);
    return v___x_1706_;
}
pub unsafe fn l_Std_instForInIterOfMonadOfIteratorLoopId___boxed(
    mut v_00_u03b1_1707_: *mut LeanObject,
    mut v_00_u03b2_1708_: *mut LeanObject,
    mut v_n_1709_: *mut LeanObject,
    mut v_inst_1710_: *mut LeanObject,
    mut v_inst_1711_: *mut LeanObject,
    mut v_inst_1712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1713_: *mut LeanObject = core::ptr::null_mut();
    v_res_1713_ = l_Std_instForInIterOfMonadOfIteratorLoopId(
        v_00_u03b1_1707_,
        v_00_u03b2_1708_,
        v_n_1709_,
        v_inst_1710_,
        v_inst_1711_,
        v_inst_1712_,
    );
    lean_dec(v_inst_1711_);
    return v_res_1713_;
}
pub unsafe fn l_Std_Iter_Partial_instForIn_x27___redArg(
    mut v_inst_1714_: *mut LeanObject,
    mut v_inst_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1717_: *mut LeanObject = core::ptr::null_mut();
    v___f_1716_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1717_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1717_, 0, v_inst_1714_);
    lean_closure_set(v___f_1717_, 1, v_inst_1715_);
    lean_closure_set(v___f_1717_, 2, v___f_1716_);
    return v___f_1717_;
}
pub unsafe fn l_Std_Iter_Partial_instForIn_x27(
    mut v_00_u03b1_1718_: *mut LeanObject,
    mut v_00_u03b2_1719_: *mut LeanObject,
    mut v_n_1720_: *mut LeanObject,
    mut v_inst_1721_: *mut LeanObject,
    mut v_inst_1722_: *mut LeanObject,
    mut v_inst_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1725_: *mut LeanObject = core::ptr::null_mut();
    v___f_1724_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1725_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1725_, 0, v_inst_1721_);
    lean_closure_set(v___f_1725_, 1, v_inst_1723_);
    lean_closure_set(v___f_1725_, 2, v___f_1724_);
    return v___f_1725_;
}
pub unsafe fn l_Std_Iter_Partial_instForIn_x27___boxed(
    mut v_00_u03b1_1726_: *mut LeanObject,
    mut v_00_u03b2_1727_: *mut LeanObject,
    mut v_n_1728_: *mut LeanObject,
    mut v_inst_1729_: *mut LeanObject,
    mut v_inst_1730_: *mut LeanObject,
    mut v_inst_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1732_: *mut LeanObject = core::ptr::null_mut();
    v_res_1732_ = l_Std_Iter_Partial_instForIn_x27(
        v_00_u03b1_1726_,
        v_00_u03b2_1727_,
        v_n_1728_,
        v_inst_1729_,
        v_inst_1730_,
        v_inst_1731_,
    );
    lean_dec(v_inst_1730_);
    return v_res_1732_;
}
pub unsafe fn l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(
    mut v_inst_1733_: *mut LeanObject,
    mut v_inst_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1737_: *mut LeanObject = core::ptr::null_mut();
    v___f_1735_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1736_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1736_, 0, v_inst_1733_);
    lean_closure_set(v___f_1736_, 1, v_inst_1734_);
    lean_closure_set(v___f_1736_, 2, v___f_1735_);
    v___f_1737_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1737_, 0, v___f_1736_);
    return v___f_1737_;
}
pub unsafe fn l_Std_instForInPartialOfMonadOfIteratorLoopId(
    mut v_00_u03b1_1738_: *mut LeanObject,
    mut v_00_u03b2_1739_: *mut LeanObject,
    mut v_n_1740_: *mut LeanObject,
    mut v_inst_1741_: *mut LeanObject,
    mut v_inst_1742_: *mut LeanObject,
    mut v_inst_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1744_: *mut LeanObject = core::ptr::null_mut();
    v___x_1744_ =
        l_Std_instForInPartialOfMonadOfIteratorLoopId___redArg(v_inst_1741_, v_inst_1743_);
    return v___x_1744_;
}
pub unsafe fn l_Std_instForInPartialOfMonadOfIteratorLoopId___boxed(
    mut v_00_u03b1_1745_: *mut LeanObject,
    mut v_00_u03b2_1746_: *mut LeanObject,
    mut v_n_1747_: *mut LeanObject,
    mut v_inst_1748_: *mut LeanObject,
    mut v_inst_1749_: *mut LeanObject,
    mut v_inst_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1751_: *mut LeanObject = core::ptr::null_mut();
    v_res_1751_ = l_Std_instForInPartialOfMonadOfIteratorLoopId(
        v_00_u03b1_1745_,
        v_00_u03b2_1746_,
        v_n_1747_,
        v_inst_1748_,
        v_inst_1749_,
        v_inst_1750_,
    );
    lean_dec(v_inst_1749_);
    return v_res_1751_;
}
pub unsafe fn l_Std_Iter_Total_instForIn_x27___redArg(
    mut v_inst_1752_: *mut LeanObject,
    mut v_inst_1753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1755_: *mut LeanObject = core::ptr::null_mut();
    v___f_1754_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1755_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1755_, 0, v_inst_1752_);
    lean_closure_set(v___f_1755_, 1, v_inst_1753_);
    lean_closure_set(v___f_1755_, 2, v___f_1754_);
    return v___f_1755_;
}
pub unsafe fn l_Std_Iter_Total_instForIn_x27(
    mut v_00_u03b1_1756_: *mut LeanObject,
    mut v_00_u03b2_1757_: *mut LeanObject,
    mut v_n_1758_: *mut LeanObject,
    mut v_inst_1759_: *mut LeanObject,
    mut v_inst_1760_: *mut LeanObject,
    mut v_inst_1761_: *mut LeanObject,
    mut v_inst_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1764_: *mut LeanObject = core::ptr::null_mut();
    v___f_1763_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1764_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1764_, 0, v_inst_1759_);
    lean_closure_set(v___f_1764_, 1, v_inst_1761_);
    lean_closure_set(v___f_1764_, 2, v___f_1763_);
    return v___f_1764_;
}
pub unsafe fn l_Std_Iter_Total_instForIn_x27___boxed(
    mut v_00_u03b1_1765_: *mut LeanObject,
    mut v_00_u03b2_1766_: *mut LeanObject,
    mut v_n_1767_: *mut LeanObject,
    mut v_inst_1768_: *mut LeanObject,
    mut v_inst_1769_: *mut LeanObject,
    mut v_inst_1770_: *mut LeanObject,
    mut v_inst_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1772_: *mut LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_Std_Iter_Total_instForIn_x27(
        v_00_u03b1_1765_,
        v_00_u03b2_1766_,
        v_n_1767_,
        v_inst_1768_,
        v_inst_1769_,
        v_inst_1770_,
        v_inst_1771_,
    );
    lean_dec(v_inst_1769_);
    return v_res_1772_;
}
pub unsafe fn l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(
    mut v_inst_1773_: *mut LeanObject,
    mut v_inst_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1777_: *mut LeanObject = core::ptr::null_mut();
    v___f_1775_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1776_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1776_, 0, v_inst_1773_);
    lean_closure_set(v___f_1776_, 1, v_inst_1774_);
    lean_closure_set(v___f_1776_, 2, v___f_1775_);
    v___f_1777_ = lean_alloc_closure(
        l_instForInOfForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1777_, 0, v___f_1776_);
    return v___f_1777_;
}
pub unsafe fn l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(
    mut v_00_u03b1_1778_: *mut LeanObject,
    mut v_00_u03b2_1779_: *mut LeanObject,
    mut v_n_1780_: *mut LeanObject,
    mut v_inst_1781_: *mut LeanObject,
    mut v_inst_1782_: *mut LeanObject,
    mut v_inst_1783_: *mut LeanObject,
    mut v_inst_1784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    v___x_1785_ =
        l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___redArg(v_inst_1781_, v_inst_1783_);
    return v___x_1785_;
}
pub unsafe fn l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId___boxed(
    mut v_00_u03b1_1786_: *mut LeanObject,
    mut v_00_u03b2_1787_: *mut LeanObject,
    mut v_n_1788_: *mut LeanObject,
    mut v_inst_1789_: *mut LeanObject,
    mut v_inst_1790_: *mut LeanObject,
    mut v_inst_1791_: *mut LeanObject,
    mut v_inst_1792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1793_: *mut LeanObject = core::ptr::null_mut();
    v_res_1793_ = l_Std_instForInTotalOfMonadOfIteratorLoopOfFiniteId(
        v_00_u03b1_1786_,
        v_00_u03b2_1787_,
        v_n_1788_,
        v_inst_1789_,
        v_inst_1790_,
        v_inst_1791_,
        v_inst_1792_,
    );
    lean_dec(v_inst_1790_);
    return v_res_1793_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1(
    mut v_toPure_1794_: *mut LeanObject,
    mut v_____do__lift_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    v___x_1796_ = lean_apply_2(v_toPure_1794_, lean_box(0), v_____do__lift_1795_);
    return v___x_1796_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0(
    mut v___x_1797_: *mut LeanObject,
    mut v_toPure_1798_: *mut LeanObject,
    mut v_____r_1799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    v___x_1800_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1800_, 0, v___x_1797_);
    v___x_1801_ = lean_apply_2(v_toPure_1798_, lean_box(0), v___x_1800_);
    return v___x_1801_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2(
    mut v_f_1802_: *mut LeanObject,
    mut v_toBind_1803_: *mut LeanObject,
    mut v___f_1804_: *mut LeanObject,
    mut v___f_1805_: *mut LeanObject,
    mut v_x1_1806_: *mut LeanObject,
    mut v_x2_1807_: *mut LeanObject,
    mut v_x3_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    v___x_1809_ = lean_apply_1(v_f_1802_, v_x1_1806_);
    lean_inc(v_toBind_1803_);
    v___x_1810_ = lean_apply_4(
        v_toBind_1803_,
        lean_box(0),
        lean_box(0),
        v___x_1809_,
        v___f_1804_,
    );
    v___x_1811_ = lean_apply_4(
        v_toBind_1803_,
        lean_box(0),
        lean_box(0),
        v___x_1810_,
        v___f_1805_,
    );
    return v___x_1811_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3(
    mut v_toPure_1812_: *mut LeanObject,
    mut v_toBind_1813_: *mut LeanObject,
    mut v___f_1814_: *mut LeanObject,
    mut v_inst_1815_: *mut LeanObject,
    mut v___f_1816_: *mut LeanObject,
    mut v_it_1817_: *mut LeanObject,
    mut v_f_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1822_: *mut LeanObject = core::ptr::null_mut();
    v___x_1819_ = lean_box(0);
    v___f_1820_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1820_, 0, v___x_1819_);
    lean_closure_set(v___f_1820_, 1, v_toPure_1812_);
    v___f_1821_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__2 as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_1821_, 0, v_f_1818_);
    lean_closure_set(v___f_1821_, 1, v_toBind_1813_);
    lean_closure_set(v___f_1821_, 2, v___f_1820_);
    lean_closure_set(v___f_1821_, 3, v___f_1814_);
    v___x_1822_ = lean_apply_6(
        v_inst_1815_,
        v___f_1816_,
        lean_box(0),
        lean_box(0),
        v_it_1817_,
        v___x_1819_,
        v___f_1821_,
    );
    return v___x_1822_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(
    mut v_inst_1823_: *mut LeanObject,
    mut v_inst_1824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1830_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1825_ = lean_ctor_get(v_inst_1824_, 0);
    lean_inc_ref(v_toApplicative_1825_);
    v_toBind_1826_ = lean_ctor_get(v_inst_1824_, 1);
    lean_inc(v_toBind_1826_);
    lean_dec_ref(v_inst_1824_);
    v_toPure_1827_ = lean_ctor_get(v_toApplicative_1825_, 1);
    lean_inc_n(v_toPure_1827_, 2);
    lean_dec_ref(v_toApplicative_1825_);
    v___f_1828_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1829_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1829_, 0, v_toPure_1827_);
    v___f_1830_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_1830_, 0, v_toPure_1827_);
    lean_closure_set(v___f_1830_, 1, v_toBind_1826_);
    lean_closure_set(v___f_1830_, 2, v___f_1829_);
    lean_closure_set(v___f_1830_, 3, v_inst_1823_);
    lean_closure_set(v___f_1830_, 4, v___f_1828_);
    return v___f_1830_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad(
    mut v_m_1831_: *mut LeanObject,
    mut v_00_u03b1_1832_: *mut LeanObject,
    mut v_00_u03b2_1833_: *mut LeanObject,
    mut v_inst_1834_: *mut LeanObject,
    mut v_inst_1835_: *mut LeanObject,
    mut v_inst_1836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1837_: *mut LeanObject = core::ptr::null_mut();
    v___x_1837_ = l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg(v_inst_1835_, v_inst_1836_);
    return v___x_1837_;
}
pub unsafe fn l_Std_instForMIterOfIteratorLoopIdOfMonad___boxed(
    mut v_m_1838_: *mut LeanObject,
    mut v_00_u03b1_1839_: *mut LeanObject,
    mut v_00_u03b2_1840_: *mut LeanObject,
    mut v_inst_1841_: *mut LeanObject,
    mut v_inst_1842_: *mut LeanObject,
    mut v_inst_1843_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1844_: *mut LeanObject = core::ptr::null_mut();
    v_res_1844_ = l_Std_instForMIterOfIteratorLoopIdOfMonad(
        v_m_1838_,
        v_00_u03b1_1839_,
        v_00_u03b2_1840_,
        v_inst_1841_,
        v_inst_1842_,
        v_inst_1843_,
    );
    lean_dec(v_inst_1841_);
    return v_res_1844_;
}
pub unsafe fn l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(
    mut v_inst_1845_: *mut LeanObject,
    mut v_inst_1846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1852_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1847_ = lean_ctor_get(v_inst_1846_, 0);
    lean_inc_ref(v_toApplicative_1847_);
    v_toBind_1848_ = lean_ctor_get(v_inst_1846_, 1);
    lean_inc(v_toBind_1848_);
    lean_dec_ref(v_inst_1846_);
    v_toPure_1849_ = lean_ctor_get(v_toApplicative_1847_, 1);
    lean_inc_n(v_toPure_1849_, 2);
    lean_dec_ref(v_toApplicative_1847_);
    v___f_1850_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1851_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1851_, 0, v_toPure_1849_);
    v___f_1852_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_1852_, 0, v_toPure_1849_);
    lean_closure_set(v___f_1852_, 1, v_toBind_1848_);
    lean_closure_set(v___f_1852_, 2, v___f_1851_);
    lean_closure_set(v___f_1852_, 3, v_inst_1845_);
    lean_closure_set(v___f_1852_, 4, v___f_1850_);
    return v___f_1852_;
}
pub unsafe fn l_Std_instForMPartialOfIteratorLoopIdOfMonad(
    mut v_m_1853_: *mut LeanObject,
    mut v_00_u03b1_1854_: *mut LeanObject,
    mut v_00_u03b2_1855_: *mut LeanObject,
    mut v_inst_1856_: *mut LeanObject,
    mut v_inst_1857_: *mut LeanObject,
    mut v_inst_1858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1859_: *mut LeanObject = core::ptr::null_mut();
    v___x_1859_ = l_Std_instForMPartialOfIteratorLoopIdOfMonad___redArg(v_inst_1857_, v_inst_1858_);
    return v___x_1859_;
}
pub unsafe fn l_Std_instForMPartialOfIteratorLoopIdOfMonad___boxed(
    mut v_m_1860_: *mut LeanObject,
    mut v_00_u03b1_1861_: *mut LeanObject,
    mut v_00_u03b2_1862_: *mut LeanObject,
    mut v_inst_1863_: *mut LeanObject,
    mut v_inst_1864_: *mut LeanObject,
    mut v_inst_1865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1866_: *mut LeanObject = core::ptr::null_mut();
    v_res_1866_ = l_Std_instForMPartialOfIteratorLoopIdOfMonad(
        v_m_1860_,
        v_00_u03b1_1861_,
        v_00_u03b2_1862_,
        v_inst_1863_,
        v_inst_1864_,
        v_inst_1865_,
    );
    lean_dec(v_inst_1863_);
    return v_res_1866_;
}
pub unsafe fn l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(
    mut v_inst_1867_: *mut LeanObject,
    mut v_inst_1868_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1874_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1869_ = lean_ctor_get(v_inst_1867_, 0);
    lean_inc_ref(v_toApplicative_1869_);
    v_toBind_1870_ = lean_ctor_get(v_inst_1867_, 1);
    lean_inc(v_toBind_1870_);
    lean_dec_ref(v_inst_1867_);
    v_toPure_1871_ = lean_ctor_get(v_toApplicative_1869_, 1);
    lean_inc_n(v_toPure_1871_, 2);
    lean_dec_ref(v_toApplicative_1869_);
    v___f_1872_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1873_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1873_, 0, v_toPure_1871_);
    v___f_1874_ = lean_alloc_closure(
        l_Std_instForMIterOfIteratorLoopIdOfMonad___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        5,
    );
    lean_closure_set(v___f_1874_, 0, v_toPure_1871_);
    lean_closure_set(v___f_1874_, 1, v_toBind_1870_);
    lean_closure_set(v___f_1874_, 2, v___f_1873_);
    lean_closure_set(v___f_1874_, 3, v_inst_1868_);
    lean_closure_set(v___f_1874_, 4, v___f_1872_);
    return v___f_1874_;
}
pub unsafe fn l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(
    mut v_m_1875_: *mut LeanObject,
    mut v_00_u03b1_1876_: *mut LeanObject,
    mut v_00_u03b2_1877_: *mut LeanObject,
    mut v_inst_1878_: *mut LeanObject,
    mut v_inst_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_inst_1881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ =
        l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___redArg(v_inst_1878_, v_inst_1880_);
    return v___x_1882_;
}
pub unsafe fn l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId___boxed(
    mut v_m_1883_: *mut LeanObject,
    mut v_00_u03b1_1884_: *mut LeanObject,
    mut v_00_u03b2_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_inst_1887_: *mut LeanObject,
    mut v_inst_1888_: *mut LeanObject,
    mut v_inst_1889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1890_: *mut LeanObject = core::ptr::null_mut();
    v_res_1890_ = l_Std_instForMTotalOfMonadOfIteratorLoopOfFiniteId(
        v_m_1883_,
        v_00_u03b1_1884_,
        v_00_u03b2_1885_,
        v_inst_1886_,
        v_inst_1887_,
        v_inst_1888_,
        v_inst_1889_,
    );
    lean_dec(v_inst_1887_);
    return v_res_1890_;
}
pub unsafe fn l_Std_Iter_foldM___redArg___lam__1(
    mut v_a_1891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1892_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_1892_, 0, v_a_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Std_Iter_foldM___redArg___lam__2(
    mut v_toFunctor_1893_: *mut LeanObject,
    mut v_f_1894_: *mut LeanObject,
    mut v___f_1895_: *mut LeanObject,
    mut v_toBind_1896_: *mut LeanObject,
    mut v___f_1897_: *mut LeanObject,
    mut v_x1_1898_: *mut LeanObject,
    mut v_x2_1899_: *mut LeanObject,
    mut v_x3_1900_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_map_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    v_map_1901_ = lean_ctor_get(v_toFunctor_1893_, 0);
    lean_inc(v_map_1901_);
    lean_dec_ref(v_toFunctor_1893_);
    v___x_1902_ = lean_apply_2(v_f_1894_, v_x3_1900_, v_x1_1898_);
    v___x_1903_ = lean_apply_4(
        v_map_1901_,
        lean_box(0),
        lean_box(0),
        v___f_1895_,
        v___x_1902_,
    );
    v___x_1904_ = lean_apply_4(
        v_toBind_1896_,
        lean_box(0),
        lean_box(0),
        v___x_1903_,
        v___f_1897_,
    );
    return v___x_1904_;
}
pub unsafe fn l_Std_Iter_foldM___redArg(
    mut v_inst_1906_: *mut LeanObject,
    mut v_inst_1907_: *mut LeanObject,
    mut v_f_1908_: *mut LeanObject,
    mut v_init_1909_: *mut LeanObject,
    mut v_it_1910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1911_ = lean_ctor_get(v_inst_1906_, 0);
    lean_inc_ref(v_toApplicative_1911_);
    v_toBind_1912_ = lean_ctor_get(v_inst_1906_, 1);
    lean_inc(v_toBind_1912_);
    lean_dec_ref(v_inst_1906_);
    v_toFunctor_1913_ = lean_ctor_get(v_toApplicative_1911_, 0);
    lean_inc_ref(v_toFunctor_1913_);
    v_toPure_1914_ = lean_ctor_get(v_toApplicative_1911_, 1);
    lean_inc(v_toPure_1914_);
    lean_dec_ref(v_toApplicative_1911_);
    v___f_1915_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1916_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_1917_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1917_, 0, v_toPure_1914_);
    v___f_1918_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_1918_, 0, v_toFunctor_1913_);
    lean_closure_set(v___f_1918_, 1, v_f_1908_);
    lean_closure_set(v___f_1918_, 2, v___f_1916_);
    lean_closure_set(v___f_1918_, 3, v_toBind_1912_);
    lean_closure_set(v___f_1918_, 4, v___f_1917_);
    v___x_1919_ = lean_apply_6(
        v_inst_1907_,
        v___f_1915_,
        lean_box(0),
        lean_box(0),
        v_it_1910_,
        v_init_1909_,
        v___f_1918_,
    );
    return v___x_1919_;
}
pub unsafe fn l_Std_Iter_foldM(
    mut v_m_1920_: *mut LeanObject,
    mut v_inst_1921_: *mut LeanObject,
    mut v_00_u03b1_1922_: *mut LeanObject,
    mut v_00_u03b2_1923_: *mut LeanObject,
    mut v_00_u03b3_1924_: *mut LeanObject,
    mut v_inst_1925_: *mut LeanObject,
    mut v_inst_1926_: *mut LeanObject,
    mut v_f_1927_: *mut LeanObject,
    mut v_init_1928_: *mut LeanObject,
    mut v_it_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1930_ = lean_ctor_get(v_inst_1921_, 0);
    lean_inc_ref(v_toApplicative_1930_);
    v_toBind_1931_ = lean_ctor_get(v_inst_1921_, 1);
    lean_inc(v_toBind_1931_);
    lean_dec_ref(v_inst_1921_);
    v_toFunctor_1932_ = lean_ctor_get(v_toApplicative_1930_, 0);
    lean_inc_ref(v_toFunctor_1932_);
    v_toPure_1933_ = lean_ctor_get(v_toApplicative_1930_, 1);
    lean_inc(v_toPure_1933_);
    lean_dec_ref(v_toApplicative_1930_);
    v___f_1934_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1935_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_1936_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1936_, 0, v_toPure_1933_);
    v___f_1937_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_1937_, 0, v_toFunctor_1932_);
    lean_closure_set(v___f_1937_, 1, v_f_1927_);
    lean_closure_set(v___f_1937_, 2, v___f_1935_);
    lean_closure_set(v___f_1937_, 3, v_toBind_1931_);
    lean_closure_set(v___f_1937_, 4, v___f_1936_);
    v___x_1938_ = lean_apply_6(
        v_inst_1926_,
        v___f_1934_,
        lean_box(0),
        lean_box(0),
        v_it_1929_,
        v_init_1928_,
        v___f_1937_,
    );
    return v___x_1938_;
}
pub unsafe fn l_Std_Iter_foldM___boxed(
    mut v_m_1939_: *mut LeanObject,
    mut v_inst_1940_: *mut LeanObject,
    mut v_00_u03b1_1941_: *mut LeanObject,
    mut v_00_u03b2_1942_: *mut LeanObject,
    mut v_00_u03b3_1943_: *mut LeanObject,
    mut v_inst_1944_: *mut LeanObject,
    mut v_inst_1945_: *mut LeanObject,
    mut v_f_1946_: *mut LeanObject,
    mut v_init_1947_: *mut LeanObject,
    mut v_it_1948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1949_: *mut LeanObject = core::ptr::null_mut();
    v_res_1949_ = l_Std_Iter_foldM(
        v_m_1939_,
        v_inst_1940_,
        v_00_u03b1_1941_,
        v_00_u03b2_1942_,
        v_00_u03b3_1943_,
        v_inst_1944_,
        v_inst_1945_,
        v_f_1946_,
        v_init_1947_,
        v_it_1948_,
    );
    lean_dec(v_inst_1944_);
    return v_res_1949_;
}
pub unsafe fn l_Std_Iter_Partial_foldM___redArg(
    mut v_inst_1950_: *mut LeanObject,
    mut v_inst_1951_: *mut LeanObject,
    mut v_f_1952_: *mut LeanObject,
    mut v_init_1953_: *mut LeanObject,
    mut v_it_1954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1955_ = lean_ctor_get(v_inst_1950_, 0);
    lean_inc_ref(v_toApplicative_1955_);
    v_toBind_1956_ = lean_ctor_get(v_inst_1950_, 1);
    lean_inc(v_toBind_1956_);
    lean_dec_ref(v_inst_1950_);
    v_toFunctor_1957_ = lean_ctor_get(v_toApplicative_1955_, 0);
    lean_inc_ref(v_toFunctor_1957_);
    v_toPure_1958_ = lean_ctor_get(v_toApplicative_1955_, 1);
    lean_inc(v_toPure_1958_);
    lean_dec_ref(v_toApplicative_1955_);
    v___f_1959_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1960_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_1961_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1961_, 0, v_toPure_1958_);
    v___f_1962_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_1962_, 0, v_toFunctor_1957_);
    lean_closure_set(v___f_1962_, 1, v_f_1952_);
    lean_closure_set(v___f_1962_, 2, v___f_1960_);
    lean_closure_set(v___f_1962_, 3, v_toBind_1956_);
    lean_closure_set(v___f_1962_, 4, v___f_1961_);
    v___x_1963_ = lean_apply_6(
        v_inst_1951_,
        v___f_1959_,
        lean_box(0),
        lean_box(0),
        v_it_1954_,
        v_init_1953_,
        v___f_1962_,
    );
    return v___x_1963_;
}
pub unsafe fn l_Std_Iter_Partial_foldM(
    mut v_m_1964_: *mut LeanObject,
    mut v_inst_1965_: *mut LeanObject,
    mut v_00_u03b1_1966_: *mut LeanObject,
    mut v_00_u03b2_1967_: *mut LeanObject,
    mut v_00_u03b3_1968_: *mut LeanObject,
    mut v_inst_1969_: *mut LeanObject,
    mut v_inst_1970_: *mut LeanObject,
    mut v_f_1971_: *mut LeanObject,
    mut v_init_1972_: *mut LeanObject,
    mut v_it_1973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_1976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1974_ = lean_ctor_get(v_inst_1965_, 0);
    lean_inc_ref(v_toApplicative_1974_);
    v_toBind_1975_ = lean_ctor_get(v_inst_1965_, 1);
    lean_inc(v_toBind_1975_);
    lean_dec_ref(v_inst_1965_);
    v_toFunctor_1976_ = lean_ctor_get(v_toApplicative_1974_, 0);
    lean_inc_ref(v_toFunctor_1976_);
    v_toPure_1977_ = lean_ctor_get(v_toApplicative_1974_, 1);
    lean_inc(v_toPure_1977_);
    lean_dec_ref(v_toApplicative_1974_);
    v___f_1978_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_1979_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_1980_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1980_, 0, v_toPure_1977_);
    v___f_1981_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_1981_, 0, v_toFunctor_1976_);
    lean_closure_set(v___f_1981_, 1, v_f_1971_);
    lean_closure_set(v___f_1981_, 2, v___f_1979_);
    lean_closure_set(v___f_1981_, 3, v_toBind_1975_);
    lean_closure_set(v___f_1981_, 4, v___f_1980_);
    v___x_1982_ = lean_apply_6(
        v_inst_1970_,
        v___f_1978_,
        lean_box(0),
        lean_box(0),
        v_it_1973_,
        v_init_1972_,
        v___f_1981_,
    );
    return v___x_1982_;
}
pub unsafe fn l_Std_Iter_Partial_foldM___boxed(
    mut v_m_1983_: *mut LeanObject,
    mut v_inst_1984_: *mut LeanObject,
    mut v_00_u03b1_1985_: *mut LeanObject,
    mut v_00_u03b2_1986_: *mut LeanObject,
    mut v_00_u03b3_1987_: *mut LeanObject,
    mut v_inst_1988_: *mut LeanObject,
    mut v_inst_1989_: *mut LeanObject,
    mut v_f_1990_: *mut LeanObject,
    mut v_init_1991_: *mut LeanObject,
    mut v_it_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Std_Iter_Partial_foldM(
        v_m_1983_,
        v_inst_1984_,
        v_00_u03b1_1985_,
        v_00_u03b2_1986_,
        v_00_u03b3_1987_,
        v_inst_1988_,
        v_inst_1989_,
        v_f_1990_,
        v_init_1991_,
        v_it_1992_,
    );
    lean_dec(v_inst_1988_);
    return v_res_1993_;
}
pub unsafe fn l_Std_Iter_Total_foldM___redArg(
    mut v_inst_1994_: *mut LeanObject,
    mut v_inst_1995_: *mut LeanObject,
    mut v_f_1996_: *mut LeanObject,
    mut v_init_1997_: *mut LeanObject,
    mut v_it_1998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2007_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1999_ = lean_ctor_get(v_inst_1994_, 0);
    lean_inc_ref(v_toApplicative_1999_);
    v_toBind_2000_ = lean_ctor_get(v_inst_1994_, 1);
    lean_inc(v_toBind_2000_);
    lean_dec_ref(v_inst_1994_);
    v_toFunctor_2001_ = lean_ctor_get(v_toApplicative_1999_, 0);
    lean_inc_ref(v_toFunctor_2001_);
    v_toPure_2002_ = lean_ctor_get(v_toApplicative_1999_, 1);
    lean_inc(v_toPure_2002_);
    lean_dec_ref(v_toApplicative_1999_);
    v___f_2003_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2004_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_2005_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2005_, 0, v_toPure_2002_);
    v___f_2006_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_2006_, 0, v_toFunctor_2001_);
    lean_closure_set(v___f_2006_, 1, v_f_1996_);
    lean_closure_set(v___f_2006_, 2, v___f_2004_);
    lean_closure_set(v___f_2006_, 3, v_toBind_2000_);
    lean_closure_set(v___f_2006_, 4, v___f_2005_);
    v___x_2007_ = lean_apply_6(
        v_inst_1995_,
        v___f_2003_,
        lean_box(0),
        lean_box(0),
        v_it_1998_,
        v_init_1997_,
        v___f_2006_,
    );
    return v___x_2007_;
}
pub unsafe fn l_Std_Iter_Total_foldM(
    mut v_m_2008_: *mut LeanObject,
    mut v_inst_2009_: *mut LeanObject,
    mut v_00_u03b1_2010_: *mut LeanObject,
    mut v_00_u03b2_2011_: *mut LeanObject,
    mut v_00_u03b3_2012_: *mut LeanObject,
    mut v_inst_2013_: *mut LeanObject,
    mut v_inst_2014_: *mut LeanObject,
    mut v_inst_2015_: *mut LeanObject,
    mut v_f_2016_: *mut LeanObject,
    mut v_init_2017_: *mut LeanObject,
    mut v_it_2018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2027_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2019_ = lean_ctor_get(v_inst_2009_, 0);
    lean_inc_ref(v_toApplicative_2019_);
    v_toBind_2020_ = lean_ctor_get(v_inst_2009_, 1);
    lean_inc(v_toBind_2020_);
    lean_dec_ref(v_inst_2009_);
    v_toFunctor_2021_ = lean_ctor_get(v_toApplicative_2019_, 0);
    lean_inc_ref(v_toFunctor_2021_);
    v_toPure_2022_ = lean_ctor_get(v_toApplicative_2019_, 1);
    lean_inc(v_toPure_2022_);
    lean_dec_ref(v_toApplicative_2019_);
    v___f_2023_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2024_ = l_Std_Iter_foldM___redArg___closed__0;
    v___f_2025_ = lean_alloc_closure(
        l_Std_Iter_instForIn_x27___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2025_, 0, v_toPure_2022_);
    v___f_2026_ = lean_alloc_closure(
        l_Std_Iter_foldM___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        5,
    );
    lean_closure_set(v___f_2026_, 0, v_toFunctor_2021_);
    lean_closure_set(v___f_2026_, 1, v_f_2016_);
    lean_closure_set(v___f_2026_, 2, v___f_2024_);
    lean_closure_set(v___f_2026_, 3, v_toBind_2020_);
    lean_closure_set(v___f_2026_, 4, v___f_2025_);
    v___x_2027_ = lean_apply_6(
        v_inst_2014_,
        v___f_2023_,
        lean_box(0),
        lean_box(0),
        v_it_2018_,
        v_init_2017_,
        v___f_2026_,
    );
    return v___x_2027_;
}
pub unsafe fn l_Std_Iter_Total_foldM___boxed(
    mut v_m_2028_: *mut LeanObject,
    mut v_inst_2029_: *mut LeanObject,
    mut v_00_u03b1_2030_: *mut LeanObject,
    mut v_00_u03b2_2031_: *mut LeanObject,
    mut v_00_u03b3_2032_: *mut LeanObject,
    mut v_inst_2033_: *mut LeanObject,
    mut v_inst_2034_: *mut LeanObject,
    mut v_inst_2035_: *mut LeanObject,
    mut v_f_2036_: *mut LeanObject,
    mut v_init_2037_: *mut LeanObject,
    mut v_it_2038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2039_: *mut LeanObject = core::ptr::null_mut();
    v_res_2039_ = l_Std_Iter_Total_foldM(
        v_m_2028_,
        v_inst_2029_,
        v_00_u03b1_2030_,
        v_00_u03b2_2031_,
        v_00_u03b3_2032_,
        v_inst_2033_,
        v_inst_2034_,
        v_inst_2035_,
        v_f_2036_,
        v_init_2037_,
        v_it_2038_,
    );
    lean_dec(v_inst_2033_);
    return v_res_2039_;
}
pub unsafe fn l_Std_Iter_fold___redArg___lam__1(
    mut v_f_2040_: *mut LeanObject,
    mut v_x1_2041_: *mut LeanObject,
    mut v_x2_2042_: *mut LeanObject,
    mut v_x3_2043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut LeanObject = core::ptr::null_mut();
    v___x_2044_ = lean_apply_2(v_f_2040_, v_x3_2043_, v_x1_2041_);
    v___x_2045_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2045_, 0, v___x_2044_);
    return v___x_2045_;
}
pub unsafe fn l_Std_Iter_fold___redArg(
    mut v_inst_2046_: *mut LeanObject,
    mut v_f_2047_: *mut LeanObject,
    mut v_init_2048_: *mut LeanObject,
    mut v_it_2049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    v___f_2050_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2051_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2051_, 0, v_f_2047_);
    v___x_2052_ = lean_apply_6(
        v_inst_2046_,
        v___f_2050_,
        lean_box(0),
        lean_box(0),
        v_it_2049_,
        v_init_2048_,
        v___f_2051_,
    );
    return v___x_2052_;
}
pub unsafe fn l_Std_Iter_fold(
    mut v_00_u03b1_2053_: *mut LeanObject,
    mut v_00_u03b2_2054_: *mut LeanObject,
    mut v_00_u03b3_2055_: *mut LeanObject,
    mut v_inst_2056_: *mut LeanObject,
    mut v_inst_2057_: *mut LeanObject,
    mut v_f_2058_: *mut LeanObject,
    mut v_init_2059_: *mut LeanObject,
    mut v_it_2060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut LeanObject = core::ptr::null_mut();
    v___f_2061_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2062_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2062_, 0, v_f_2058_);
    v___x_2063_ = lean_apply_6(
        v_inst_2057_,
        v___f_2061_,
        lean_box(0),
        lean_box(0),
        v_it_2060_,
        v_init_2059_,
        v___f_2062_,
    );
    return v___x_2063_;
}
pub unsafe fn l_Std_Iter_fold___boxed(
    mut v_00_u03b1_2064_: *mut LeanObject,
    mut v_00_u03b2_2065_: *mut LeanObject,
    mut v_00_u03b3_2066_: *mut LeanObject,
    mut v_inst_2067_: *mut LeanObject,
    mut v_inst_2068_: *mut LeanObject,
    mut v_f_2069_: *mut LeanObject,
    mut v_init_2070_: *mut LeanObject,
    mut v_it_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2072_: *mut LeanObject = core::ptr::null_mut();
    v_res_2072_ = l_Std_Iter_fold(
        v_00_u03b1_2064_,
        v_00_u03b2_2065_,
        v_00_u03b3_2066_,
        v_inst_2067_,
        v_inst_2068_,
        v_f_2069_,
        v_init_2070_,
        v_it_2071_,
    );
    lean_dec(v_inst_2067_);
    return v_res_2072_;
}
pub unsafe fn l_Std_Iter_Partial_fold___redArg(
    mut v_inst_2073_: *mut LeanObject,
    mut v_f_2074_: *mut LeanObject,
    mut v_init_2075_: *mut LeanObject,
    mut v_it_2076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    v___f_2077_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2078_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2078_, 0, v_f_2074_);
    v___x_2079_ = lean_apply_6(
        v_inst_2073_,
        v___f_2077_,
        lean_box(0),
        lean_box(0),
        v_it_2076_,
        v_init_2075_,
        v___f_2078_,
    );
    return v___x_2079_;
}
pub unsafe fn l_Std_Iter_Partial_fold(
    mut v_00_u03b1_2080_: *mut LeanObject,
    mut v_00_u03b2_2081_: *mut LeanObject,
    mut v_00_u03b3_2082_: *mut LeanObject,
    mut v_inst_2083_: *mut LeanObject,
    mut v_inst_2084_: *mut LeanObject,
    mut v_f_2085_: *mut LeanObject,
    mut v_init_2086_: *mut LeanObject,
    mut v_it_2087_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut LeanObject = core::ptr::null_mut();
    v___f_2088_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2089_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2089_, 0, v_f_2085_);
    v___x_2090_ = lean_apply_6(
        v_inst_2084_,
        v___f_2088_,
        lean_box(0),
        lean_box(0),
        v_it_2087_,
        v_init_2086_,
        v___f_2089_,
    );
    return v___x_2090_;
}
pub unsafe fn l_Std_Iter_Partial_fold___boxed(
    mut v_00_u03b1_2091_: *mut LeanObject,
    mut v_00_u03b2_2092_: *mut LeanObject,
    mut v_00_u03b3_2093_: *mut LeanObject,
    mut v_inst_2094_: *mut LeanObject,
    mut v_inst_2095_: *mut LeanObject,
    mut v_f_2096_: *mut LeanObject,
    mut v_init_2097_: *mut LeanObject,
    mut v_it_2098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2099_: *mut LeanObject = core::ptr::null_mut();
    v_res_2099_ = l_Std_Iter_Partial_fold(
        v_00_u03b1_2091_,
        v_00_u03b2_2092_,
        v_00_u03b3_2093_,
        v_inst_2094_,
        v_inst_2095_,
        v_f_2096_,
        v_init_2097_,
        v_it_2098_,
    );
    lean_dec(v_inst_2094_);
    return v_res_2099_;
}
pub unsafe fn l_Std_Iter_Total_fold___redArg(
    mut v_inst_2100_: *mut LeanObject,
    mut v_f_2101_: *mut LeanObject,
    mut v_init_2102_: *mut LeanObject,
    mut v_it_2103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    v___f_2104_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2105_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2105_, 0, v_f_2101_);
    v___x_2106_ = lean_apply_6(
        v_inst_2100_,
        v___f_2104_,
        lean_box(0),
        lean_box(0),
        v_it_2103_,
        v_init_2102_,
        v___f_2105_,
    );
    return v___x_2106_;
}
pub unsafe fn l_Std_Iter_Total_fold(
    mut v_00_u03b1_2107_: *mut LeanObject,
    mut v_00_u03b2_2108_: *mut LeanObject,
    mut v_00_u03b3_2109_: *mut LeanObject,
    mut v_inst_2110_: *mut LeanObject,
    mut v_inst_2111_: *mut LeanObject,
    mut v_inst_2112_: *mut LeanObject,
    mut v_f_2113_: *mut LeanObject,
    mut v_init_2114_: *mut LeanObject,
    mut v_it_2115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    v___f_2116_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2117_ = lean_alloc_closure(
        l_Std_Iter_fold___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        1,
    );
    lean_closure_set(v___f_2117_, 0, v_f_2113_);
    v___x_2118_ = lean_apply_6(
        v_inst_2111_,
        v___f_2116_,
        lean_box(0),
        lean_box(0),
        v_it_2115_,
        v_init_2114_,
        v___f_2117_,
    );
    return v___x_2118_;
}
pub unsafe fn l_Std_Iter_Total_fold___boxed(
    mut v_00_u03b1_2119_: *mut LeanObject,
    mut v_00_u03b2_2120_: *mut LeanObject,
    mut v_00_u03b3_2121_: *mut LeanObject,
    mut v_inst_2122_: *mut LeanObject,
    mut v_inst_2123_: *mut LeanObject,
    mut v_inst_2124_: *mut LeanObject,
    mut v_f_2125_: *mut LeanObject,
    mut v_init_2126_: *mut LeanObject,
    mut v_it_2127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2128_: *mut LeanObject = core::ptr::null_mut();
    v_res_2128_ = l_Std_Iter_Total_fold(
        v_00_u03b1_2119_,
        v_00_u03b2_2120_,
        v_00_u03b3_2121_,
        v_inst_2122_,
        v_inst_2123_,
        v_inst_2124_,
        v_f_2125_,
        v_init_2126_,
        v_it_2127_,
    );
    lean_dec(v_inst_2122_);
    return v_res_2128_;
}
pub unsafe fn l_Std_Iter_anyM___redArg___lam__1(
    mut v___x_2129_: u8,
    mut v_toPure_2130_: *mut LeanObject,
    mut v_____do__lift_2131_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2131_ == 0 {
        let mut v___x_2132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2134_: *mut LeanObject = core::ptr::null_mut();
        v___x_2132_ = lean_box((v___x_2129_) as usize);
        v___x_2133_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2133_, 0, v___x_2132_);
        v___x_2134_ = lean_apply_2(v_toPure_2130_, lean_box(0), v___x_2133_);
        return v___x_2134_;
    } else {
        let mut v___x_2135_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2137_: *mut LeanObject = core::ptr::null_mut();
        v___x_2135_ = lean_box((v_____do__lift_2131_) as usize);
        v___x_2136_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2136_, 0, v___x_2135_);
        v___x_2137_ = lean_apply_2(v_toPure_2130_, lean_box(0), v___x_2136_);
        return v___x_2137_;
    }
}
pub unsafe fn l_Std_Iter_anyM___redArg___lam__1___boxed(
    mut v___x_2138_: *mut LeanObject,
    mut v_toPure_2139_: *mut LeanObject,
    mut v_____do__lift_2140_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_230__boxed_2141_: u8 = 0;
    let mut v_____do__lift_231__boxed_2142_: u8 = 0;
    let mut v_res_2143_: *mut LeanObject = core::ptr::null_mut();
    v___x_230__boxed_2141_ = (lean_unbox(v___x_2138_) as u8);
    v_____do__lift_231__boxed_2142_ = (lean_unbox(v_____do__lift_2140_) as u8);
    v_res_2143_ = l_Std_Iter_anyM___redArg___lam__1(
        v___x_230__boxed_2141_,
        v_toPure_2139_,
        v_____do__lift_231__boxed_2142_,
    );
    return v_res_2143_;
}
pub unsafe fn l_Std_Iter_anyM___redArg___lam__0(
    mut v_toPure_2144_: *mut LeanObject,
    mut v_____do__lift_2145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    v___x_2146_ = lean_apply_2(v_toPure_2144_, lean_box(0), v_____do__lift_2145_);
    return v___x_2146_;
}
pub unsafe fn l_Std_Iter_anyM___redArg___lam__2(
    mut v_p_2147_: *mut LeanObject,
    mut v_toBind_2148_: *mut LeanObject,
    mut v___f_2149_: *mut LeanObject,
    mut v___f_2150_: *mut LeanObject,
    mut v_x1_2151_: *mut LeanObject,
    mut v_x2_2152_: *mut LeanObject,
    mut v_x3_2153_: u8,
) -> *mut LeanObject {
    let mut v___x_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    v___x_2154_ = lean_apply_1(v_p_2147_, v_x1_2151_);
    lean_inc(v_toBind_2148_);
    v___x_2155_ = lean_apply_4(
        v_toBind_2148_,
        lean_box(0),
        lean_box(0),
        v___x_2154_,
        v___f_2149_,
    );
    v___x_2156_ = lean_apply_4(
        v_toBind_2148_,
        lean_box(0),
        lean_box(0),
        v___x_2155_,
        v___f_2150_,
    );
    return v___x_2156_;
}
pub unsafe fn l_Std_Iter_anyM___redArg___lam__2___boxed(
    mut v_p_2157_: *mut LeanObject,
    mut v_toBind_2158_: *mut LeanObject,
    mut v___f_2159_: *mut LeanObject,
    mut v___f_2160_: *mut LeanObject,
    mut v_x1_2161_: *mut LeanObject,
    mut v_x2_2162_: *mut LeanObject,
    mut v_x3_2163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x3_256__boxed_2164_: u8 = 0;
    let mut v_res_2165_: *mut LeanObject = core::ptr::null_mut();
    v_x3_256__boxed_2164_ = (lean_unbox(v_x3_2163_) as u8);
    v_res_2165_ = l_Std_Iter_anyM___redArg___lam__2(
        v_p_2157_,
        v_toBind_2158_,
        v___f_2159_,
        v___f_2160_,
        v_x1_2161_,
        v_x2_2162_,
        v_x3_256__boxed_2164_,
    );
    return v_res_2165_;
}
pub unsafe fn l_Std_Iter_anyM___redArg(
    mut v_inst_2166_: *mut LeanObject,
    mut v_inst_2167_: *mut LeanObject,
    mut v_p_2168_: *mut LeanObject,
    mut v_it_2169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: u8 = 0;
    let mut v___x_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2170_ = lean_ctor_get(v_inst_2166_, 0);
    lean_inc_ref(v_toApplicative_2170_);
    v_toBind_2171_ = lean_ctor_get(v_inst_2166_, 1);
    lean_inc(v_toBind_2171_);
    lean_dec_ref(v_inst_2166_);
    v_toPure_2172_ = lean_ctor_get(v_toApplicative_2170_, 1);
    lean_inc_n(v_toPure_2172_, 2);
    lean_dec_ref(v_toApplicative_2170_);
    v___f_2173_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2174_ = 0;
    v___x_2175_ = lean_box((v___x_2174_) as usize);
    v___f_2176_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2176_, 0, v___x_2175_);
    lean_closure_set(v___f_2176_, 1, v_toPure_2172_);
    v___f_2177_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2177_, 0, v_toPure_2172_);
    v___f_2178_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2178_, 0, v_p_2168_);
    lean_closure_set(v___f_2178_, 1, v_toBind_2171_);
    lean_closure_set(v___f_2178_, 2, v___f_2176_);
    lean_closure_set(v___f_2178_, 3, v___f_2177_);
    v___x_2179_ = lean_box((v___x_2174_) as usize);
    v___x_2180_ = lean_apply_6(
        v_inst_2167_,
        v___f_2173_,
        lean_box(0),
        lean_box(0),
        v_it_2169_,
        v___x_2179_,
        v___f_2178_,
    );
    return v___x_2180_;
}
pub unsafe fn l_Std_Iter_anyM(
    mut v_00_u03b1_2181_: *mut LeanObject,
    mut v_00_u03b2_2182_: *mut LeanObject,
    mut v_m_2183_: *mut LeanObject,
    mut v_inst_2184_: *mut LeanObject,
    mut v_inst_2185_: *mut LeanObject,
    mut v_inst_2186_: *mut LeanObject,
    mut v_p_2187_: *mut LeanObject,
    mut v_it_2188_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v___x_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2189_ = lean_ctor_get(v_inst_2184_, 0);
    lean_inc_ref(v_toApplicative_2189_);
    v_toBind_2190_ = lean_ctor_get(v_inst_2184_, 1);
    lean_inc(v_toBind_2190_);
    lean_dec_ref(v_inst_2184_);
    v_toPure_2191_ = lean_ctor_get(v_toApplicative_2189_, 1);
    lean_inc_n(v_toPure_2191_, 2);
    lean_dec_ref(v_toApplicative_2189_);
    v___f_2192_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2193_ = 0;
    v___x_2194_ = lean_box((v___x_2193_) as usize);
    v___f_2195_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2195_, 0, v___x_2194_);
    lean_closure_set(v___f_2195_, 1, v_toPure_2191_);
    v___f_2196_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2196_, 0, v_toPure_2191_);
    v___f_2197_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2197_, 0, v_p_2187_);
    lean_closure_set(v___f_2197_, 1, v_toBind_2190_);
    lean_closure_set(v___f_2197_, 2, v___f_2195_);
    lean_closure_set(v___f_2197_, 3, v___f_2196_);
    v___x_2198_ = lean_box((v___x_2193_) as usize);
    v___x_2199_ = lean_apply_6(
        v_inst_2186_,
        v___f_2192_,
        lean_box(0),
        lean_box(0),
        v_it_2188_,
        v___x_2198_,
        v___f_2197_,
    );
    return v___x_2199_;
}
pub unsafe fn l_Std_Iter_anyM___boxed(
    mut v_00_u03b1_2200_: *mut LeanObject,
    mut v_00_u03b2_2201_: *mut LeanObject,
    mut v_m_2202_: *mut LeanObject,
    mut v_inst_2203_: *mut LeanObject,
    mut v_inst_2204_: *mut LeanObject,
    mut v_inst_2205_: *mut LeanObject,
    mut v_p_2206_: *mut LeanObject,
    mut v_it_2207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2208_: *mut LeanObject = core::ptr::null_mut();
    v_res_2208_ = l_Std_Iter_anyM(
        v_00_u03b1_2200_,
        v_00_u03b2_2201_,
        v_m_2202_,
        v_inst_2203_,
        v_inst_2204_,
        v_inst_2205_,
        v_p_2206_,
        v_it_2207_,
    );
    lean_dec(v_inst_2204_);
    return v_res_2208_;
}
pub unsafe fn l_Std_Iter_Total_anyM___redArg(
    mut v_inst_2209_: *mut LeanObject,
    mut v_inst_2210_: *mut LeanObject,
    mut v_p_2211_: *mut LeanObject,
    mut v_it_2212_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: u8 = 0;
    let mut v___x_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2223_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2213_ = lean_ctor_get(v_inst_2209_, 0);
    lean_inc_ref(v_toApplicative_2213_);
    v_toBind_2214_ = lean_ctor_get(v_inst_2209_, 1);
    lean_inc(v_toBind_2214_);
    lean_dec_ref(v_inst_2209_);
    v_toPure_2215_ = lean_ctor_get(v_toApplicative_2213_, 1);
    lean_inc_n(v_toPure_2215_, 2);
    lean_dec_ref(v_toApplicative_2213_);
    v___f_2216_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2217_ = 0;
    v___x_2218_ = lean_box((v___x_2217_) as usize);
    v___f_2219_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2219_, 0, v___x_2218_);
    lean_closure_set(v___f_2219_, 1, v_toPure_2215_);
    v___f_2220_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2220_, 0, v_toPure_2215_);
    v___f_2221_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2221_, 0, v_p_2211_);
    lean_closure_set(v___f_2221_, 1, v_toBind_2214_);
    lean_closure_set(v___f_2221_, 2, v___f_2219_);
    lean_closure_set(v___f_2221_, 3, v___f_2220_);
    v___x_2222_ = lean_box((v___x_2217_) as usize);
    v___x_2223_ = lean_apply_6(
        v_inst_2210_,
        v___f_2216_,
        lean_box(0),
        lean_box(0),
        v_it_2212_,
        v___x_2222_,
        v___f_2221_,
    );
    return v___x_2223_;
}
pub unsafe fn l_Std_Iter_Total_anyM(
    mut v_00_u03b1_2224_: *mut LeanObject,
    mut v_00_u03b2_2225_: *mut LeanObject,
    mut v_m_2226_: *mut LeanObject,
    mut v_inst_2227_: *mut LeanObject,
    mut v_inst_2228_: *mut LeanObject,
    mut v_inst_2229_: *mut LeanObject,
    mut v_inst_2230_: *mut LeanObject,
    mut v_p_2231_: *mut LeanObject,
    mut v_it_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: u8 = 0;
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2233_ = lean_ctor_get(v_inst_2227_, 0);
    lean_inc_ref(v_toApplicative_2233_);
    v_toBind_2234_ = lean_ctor_get(v_inst_2227_, 1);
    lean_inc(v_toBind_2234_);
    lean_dec_ref(v_inst_2227_);
    v_toPure_2235_ = lean_ctor_get(v_toApplicative_2233_, 1);
    lean_inc_n(v_toPure_2235_, 2);
    lean_dec_ref(v_toApplicative_2233_);
    v___f_2236_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2237_ = 0;
    v___x_2238_ = lean_box((v___x_2237_) as usize);
    v___f_2239_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2239_, 0, v___x_2238_);
    lean_closure_set(v___f_2239_, 1, v_toPure_2235_);
    v___f_2240_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2240_, 0, v_toPure_2235_);
    v___f_2241_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2241_, 0, v_p_2231_);
    lean_closure_set(v___f_2241_, 1, v_toBind_2234_);
    lean_closure_set(v___f_2241_, 2, v___f_2239_);
    lean_closure_set(v___f_2241_, 3, v___f_2240_);
    v___x_2242_ = lean_box((v___x_2237_) as usize);
    v___x_2243_ = lean_apply_6(
        v_inst_2229_,
        v___f_2236_,
        lean_box(0),
        lean_box(0),
        v_it_2232_,
        v___x_2242_,
        v___f_2241_,
    );
    return v___x_2243_;
}
pub unsafe fn l_Std_Iter_Total_anyM___boxed(
    mut v_00_u03b1_2244_: *mut LeanObject,
    mut v_00_u03b2_2245_: *mut LeanObject,
    mut v_m_2246_: *mut LeanObject,
    mut v_inst_2247_: *mut LeanObject,
    mut v_inst_2248_: *mut LeanObject,
    mut v_inst_2249_: *mut LeanObject,
    mut v_inst_2250_: *mut LeanObject,
    mut v_p_2251_: *mut LeanObject,
    mut v_it_2252_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2253_: *mut LeanObject = core::ptr::null_mut();
    v_res_2253_ = l_Std_Iter_Total_anyM(
        v_00_u03b1_2244_,
        v_00_u03b2_2245_,
        v_m_2246_,
        v_inst_2247_,
        v_inst_2248_,
        v_inst_2249_,
        v_inst_2250_,
        v_p_2251_,
        v_it_2252_,
    );
    lean_dec(v_inst_2248_);
    return v_res_2253_;
}
pub unsafe fn l_Std_Iter_any___redArg___lam__1(
    mut v_p_2254_: *mut LeanObject,
    mut v___x_2255_: u8,
    mut v_x1_2256_: *mut LeanObject,
    mut v_x2_2257_: *mut LeanObject,
    mut v_x3_2258_: u8,
) -> *mut LeanObject {
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    v___x_2259_ = lean_apply_1(v_p_2254_, v_x1_2256_);
    v___x_2260_ = (lean_unbox(v___x_2259_) as u8);
    if v___x_2260_ == 0 {
        let mut v___x_2261_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2262_: *mut LeanObject = core::ptr::null_mut();
        v___x_2261_ = lean_box((v___x_2255_) as usize);
        v___x_2262_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2262_, 0, v___x_2261_);
        return v___x_2262_;
    } else {
        let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
        v___x_2263_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2263_, 0, v___x_2259_);
        return v___x_2263_;
    }
}
pub unsafe fn l_Std_Iter_any___redArg___lam__1___boxed(
    mut v_p_2264_: *mut LeanObject,
    mut v___x_2265_: *mut LeanObject,
    mut v_x1_2266_: *mut LeanObject,
    mut v_x2_2267_: *mut LeanObject,
    mut v_x3_2268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_280__boxed_2269_: u8 = 0;
    let mut v_x3_283__boxed_2270_: u8 = 0;
    let mut v_res_2271_: *mut LeanObject = core::ptr::null_mut();
    v___x_280__boxed_2269_ = (lean_unbox(v___x_2265_) as u8);
    v_x3_283__boxed_2270_ = (lean_unbox(v_x3_2268_) as u8);
    v_res_2271_ = l_Std_Iter_any___redArg___lam__1(
        v_p_2264_,
        v___x_280__boxed_2269_,
        v_x1_2266_,
        v_x2_2267_,
        v_x3_283__boxed_2270_,
    );
    return v_res_2271_;
}
pub unsafe fn l_Std_Iter_any___redArg(
    mut v_inst_2272_: *mut LeanObject,
    mut v_p_2273_: *mut LeanObject,
    mut v_it_2274_: *mut LeanObject,
) -> u8 {
    let mut v___f_2275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2276_: u8 = 0;
    let mut v___x_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: u8 = 0;
    v___f_2275_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2276_ = 0;
    v___x_2277_ = lean_box((v___x_2276_) as usize);
    v___f_2278_ = lean_alloc_closure(
        l_Std_Iter_any___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2278_, 0, v_p_2273_);
    lean_closure_set(v___f_2278_, 1, v___x_2277_);
    v___x_2279_ = lean_box((v___x_2276_) as usize);
    v___x_2280_ = lean_apply_6(
        v_inst_2272_,
        v___f_2275_,
        lean_box(0),
        lean_box(0),
        v_it_2274_,
        v___x_2279_,
        v___f_2278_,
    );
    v___x_2281_ = (lean_unbox(v___x_2280_) as u8);
    return v___x_2281_;
}
pub unsafe fn l_Std_Iter_any___redArg___boxed(
    mut v_inst_2282_: *mut LeanObject,
    mut v_p_2283_: *mut LeanObject,
    mut v_it_2284_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2285_: u8 = 0;
    let mut v_r_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2285_ = l_Std_Iter_any___redArg(v_inst_2282_, v_p_2283_, v_it_2284_);
    v_r_2286_ = lean_box((v_res_2285_) as usize);
    return v_r_2286_;
}
pub unsafe fn l_Std_Iter_any(
    mut v_00_u03b1_2287_: *mut LeanObject,
    mut v_00_u03b2_2288_: *mut LeanObject,
    mut v_inst_2289_: *mut LeanObject,
    mut v_inst_2290_: *mut LeanObject,
    mut v_p_2291_: *mut LeanObject,
    mut v_it_2292_: *mut LeanObject,
) -> u8 {
    let mut v___f_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2294_: u8 = 0;
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: u8 = 0;
    v___f_2293_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2294_ = 0;
    v___x_2295_ = lean_box((v___x_2294_) as usize);
    v___f_2296_ = lean_alloc_closure(
        l_Std_Iter_any___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2296_, 0, v_p_2291_);
    lean_closure_set(v___f_2296_, 1, v___x_2295_);
    v___x_2297_ = lean_box((v___x_2294_) as usize);
    v___x_2298_ = lean_apply_6(
        v_inst_2290_,
        v___f_2293_,
        lean_box(0),
        lean_box(0),
        v_it_2292_,
        v___x_2297_,
        v___f_2296_,
    );
    v___x_2299_ = (lean_unbox(v___x_2298_) as u8);
    return v___x_2299_;
}
pub unsafe fn l_Std_Iter_any___boxed(
    mut v_00_u03b1_2300_: *mut LeanObject,
    mut v_00_u03b2_2301_: *mut LeanObject,
    mut v_inst_2302_: *mut LeanObject,
    mut v_inst_2303_: *mut LeanObject,
    mut v_p_2304_: *mut LeanObject,
    mut v_it_2305_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2306_: u8 = 0;
    let mut v_r_2307_: *mut LeanObject = core::ptr::null_mut();
    v_res_2306_ = l_Std_Iter_any(
        v_00_u03b1_2300_,
        v_00_u03b2_2301_,
        v_inst_2302_,
        v_inst_2303_,
        v_p_2304_,
        v_it_2305_,
    );
    lean_dec(v_inst_2302_);
    v_r_2307_ = lean_box((v_res_2306_) as usize);
    return v_r_2307_;
}
pub unsafe fn l_Std_Iter_Total_any___redArg(
    mut v_inst_2308_: *mut LeanObject,
    mut v_p_2309_: *mut LeanObject,
    mut v_it_2310_: *mut LeanObject,
) -> u8 {
    let mut v___f_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: u8 = 0;
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2317_: u8 = 0;
    v___f_2311_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2312_ = 0;
    v___x_2313_ = lean_box((v___x_2312_) as usize);
    v___f_2314_ = lean_alloc_closure(
        l_Std_Iter_any___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2314_, 0, v_p_2309_);
    lean_closure_set(v___f_2314_, 1, v___x_2313_);
    v___x_2315_ = lean_box((v___x_2312_) as usize);
    v___x_2316_ = lean_apply_6(
        v_inst_2308_,
        v___f_2311_,
        lean_box(0),
        lean_box(0),
        v_it_2310_,
        v___x_2315_,
        v___f_2314_,
    );
    v___x_2317_ = (lean_unbox(v___x_2316_) as u8);
    return v___x_2317_;
}
pub unsafe fn l_Std_Iter_Total_any___redArg___boxed(
    mut v_inst_2318_: *mut LeanObject,
    mut v_p_2319_: *mut LeanObject,
    mut v_it_2320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2321_: u8 = 0;
    let mut v_r_2322_: *mut LeanObject = core::ptr::null_mut();
    v_res_2321_ = l_Std_Iter_Total_any___redArg(v_inst_2318_, v_p_2319_, v_it_2320_);
    v_r_2322_ = lean_box((v_res_2321_) as usize);
    return v_r_2322_;
}
pub unsafe fn l_Std_Iter_Total_any(
    mut v_00_u03b1_2323_: *mut LeanObject,
    mut v_00_u03b2_2324_: *mut LeanObject,
    mut v_inst_2325_: *mut LeanObject,
    mut v_inst_2326_: *mut LeanObject,
    mut v_inst_2327_: *mut LeanObject,
    mut v_p_2328_: *mut LeanObject,
    mut v_it_2329_: *mut LeanObject,
) -> u8 {
    let mut v___f_2330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2331_: u8 = 0;
    let mut v___x_2332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2336_: u8 = 0;
    v___f_2330_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2331_ = 0;
    v___x_2332_ = lean_box((v___x_2331_) as usize);
    v___f_2333_ = lean_alloc_closure(
        l_Std_Iter_any___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2333_, 0, v_p_2328_);
    lean_closure_set(v___f_2333_, 1, v___x_2332_);
    v___x_2334_ = lean_box((v___x_2331_) as usize);
    v___x_2335_ = lean_apply_6(
        v_inst_2326_,
        v___f_2330_,
        lean_box(0),
        lean_box(0),
        v_it_2329_,
        v___x_2334_,
        v___f_2333_,
    );
    v___x_2336_ = (lean_unbox(v___x_2335_) as u8);
    return v___x_2336_;
}
pub unsafe fn l_Std_Iter_Total_any___boxed(
    mut v_00_u03b1_2337_: *mut LeanObject,
    mut v_00_u03b2_2338_: *mut LeanObject,
    mut v_inst_2339_: *mut LeanObject,
    mut v_inst_2340_: *mut LeanObject,
    mut v_inst_2341_: *mut LeanObject,
    mut v_p_2342_: *mut LeanObject,
    mut v_it_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2344_: u8 = 0;
    let mut v_r_2345_: *mut LeanObject = core::ptr::null_mut();
    v_res_2344_ = l_Std_Iter_Total_any(
        v_00_u03b1_2337_,
        v_00_u03b2_2338_,
        v_inst_2339_,
        v_inst_2340_,
        v_inst_2341_,
        v_p_2342_,
        v_it_2343_,
    );
    lean_dec(v_inst_2339_);
    v_r_2345_ = lean_box((v_res_2344_) as usize);
    return v_r_2345_;
}
pub unsafe fn l_Std_Iter_allM___redArg___lam__1(
    mut v_toPure_2346_: *mut LeanObject,
    mut v___x_2347_: u8,
    mut v_____do__lift_2348_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2348_ == 0 {
        let mut v___x_2349_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
        v___x_2349_ = lean_box((v_____do__lift_2348_) as usize);
        v___x_2350_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2350_, 0, v___x_2349_);
        v___x_2351_ = lean_apply_2(v_toPure_2346_, lean_box(0), v___x_2350_);
        return v___x_2351_;
    } else {
        let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2353_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
        v___x_2352_ = lean_box((v___x_2347_) as usize);
        v___x_2353_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2353_, 0, v___x_2352_);
        v___x_2354_ = lean_apply_2(v_toPure_2346_, lean_box(0), v___x_2353_);
        return v___x_2354_;
    }
}
pub unsafe fn l_Std_Iter_allM___redArg___lam__1___boxed(
    mut v_toPure_2355_: *mut LeanObject,
    mut v___x_2356_: *mut LeanObject,
    mut v_____do__lift_2357_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_232__boxed_2358_: u8 = 0;
    let mut v_____do__lift_233__boxed_2359_: u8 = 0;
    let mut v_res_2360_: *mut LeanObject = core::ptr::null_mut();
    v___x_232__boxed_2358_ = (lean_unbox(v___x_2356_) as u8);
    v_____do__lift_233__boxed_2359_ = (lean_unbox(v_____do__lift_2357_) as u8);
    v_res_2360_ = l_Std_Iter_allM___redArg___lam__1(
        v_toPure_2355_,
        v___x_232__boxed_2358_,
        v_____do__lift_233__boxed_2359_,
    );
    return v_res_2360_;
}
pub unsafe fn l_Std_Iter_allM___redArg(
    mut v_inst_2361_: *mut LeanObject,
    mut v_inst_2362_: *mut LeanObject,
    mut v_p_2363_: *mut LeanObject,
    mut v_it_2364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: u8 = 0;
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2365_ = lean_ctor_get(v_inst_2361_, 0);
    lean_inc_ref(v_toApplicative_2365_);
    v_toBind_2366_ = lean_ctor_get(v_inst_2361_, 1);
    lean_inc(v_toBind_2366_);
    lean_dec_ref(v_inst_2361_);
    v_toPure_2367_ = lean_ctor_get(v_toApplicative_2365_, 1);
    lean_inc_n(v_toPure_2367_, 2);
    lean_dec_ref(v_toApplicative_2365_);
    v___f_2368_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2369_ = 1;
    v___x_2370_ = lean_box((v___x_2369_) as usize);
    v___f_2371_ = lean_alloc_closure(
        l_Std_Iter_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2371_, 0, v_toPure_2367_);
    lean_closure_set(v___f_2371_, 1, v___x_2370_);
    v___f_2372_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2372_, 0, v_toPure_2367_);
    v___f_2373_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2373_, 0, v_p_2363_);
    lean_closure_set(v___f_2373_, 1, v_toBind_2366_);
    lean_closure_set(v___f_2373_, 2, v___f_2371_);
    lean_closure_set(v___f_2373_, 3, v___f_2372_);
    v___x_2374_ = lean_box((v___x_2369_) as usize);
    v___x_2375_ = lean_apply_6(
        v_inst_2362_,
        v___f_2368_,
        lean_box(0),
        lean_box(0),
        v_it_2364_,
        v___x_2374_,
        v___f_2373_,
    );
    return v___x_2375_;
}
pub unsafe fn l_Std_Iter_allM(
    mut v_00_u03b1_2376_: *mut LeanObject,
    mut v_00_u03b2_2377_: *mut LeanObject,
    mut v_m_2378_: *mut LeanObject,
    mut v_inst_2379_: *mut LeanObject,
    mut v_inst_2380_: *mut LeanObject,
    mut v_inst_2381_: *mut LeanObject,
    mut v_p_2382_: *mut LeanObject,
    mut v_it_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: u8 = 0;
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2384_ = lean_ctor_get(v_inst_2379_, 0);
    lean_inc_ref(v_toApplicative_2384_);
    v_toBind_2385_ = lean_ctor_get(v_inst_2379_, 1);
    lean_inc(v_toBind_2385_);
    lean_dec_ref(v_inst_2379_);
    v_toPure_2386_ = lean_ctor_get(v_toApplicative_2384_, 1);
    lean_inc_n(v_toPure_2386_, 2);
    lean_dec_ref(v_toApplicative_2384_);
    v___f_2387_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2388_ = 1;
    v___x_2389_ = lean_box((v___x_2388_) as usize);
    v___f_2390_ = lean_alloc_closure(
        l_Std_Iter_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2390_, 0, v_toPure_2386_);
    lean_closure_set(v___f_2390_, 1, v___x_2389_);
    v___f_2391_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2391_, 0, v_toPure_2386_);
    v___f_2392_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2392_, 0, v_p_2382_);
    lean_closure_set(v___f_2392_, 1, v_toBind_2385_);
    lean_closure_set(v___f_2392_, 2, v___f_2390_);
    lean_closure_set(v___f_2392_, 3, v___f_2391_);
    v___x_2393_ = lean_box((v___x_2388_) as usize);
    v___x_2394_ = lean_apply_6(
        v_inst_2381_,
        v___f_2387_,
        lean_box(0),
        lean_box(0),
        v_it_2383_,
        v___x_2393_,
        v___f_2392_,
    );
    return v___x_2394_;
}
pub unsafe fn l_Std_Iter_allM___boxed(
    mut v_00_u03b1_2395_: *mut LeanObject,
    mut v_00_u03b2_2396_: *mut LeanObject,
    mut v_m_2397_: *mut LeanObject,
    mut v_inst_2398_: *mut LeanObject,
    mut v_inst_2399_: *mut LeanObject,
    mut v_inst_2400_: *mut LeanObject,
    mut v_p_2401_: *mut LeanObject,
    mut v_it_2402_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2403_: *mut LeanObject = core::ptr::null_mut();
    v_res_2403_ = l_Std_Iter_allM(
        v_00_u03b1_2395_,
        v_00_u03b2_2396_,
        v_m_2397_,
        v_inst_2398_,
        v_inst_2399_,
        v_inst_2400_,
        v_p_2401_,
        v_it_2402_,
    );
    lean_dec(v_inst_2399_);
    return v_res_2403_;
}
pub unsafe fn l_Std_Iter_Total_allM___redArg(
    mut v_inst_2404_: *mut LeanObject,
    mut v_inst_2405_: *mut LeanObject,
    mut v_p_2406_: *mut LeanObject,
    mut v_it_2407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: u8 = 0;
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2408_ = lean_ctor_get(v_inst_2404_, 0);
    lean_inc_ref(v_toApplicative_2408_);
    v_toBind_2409_ = lean_ctor_get(v_inst_2404_, 1);
    lean_inc(v_toBind_2409_);
    lean_dec_ref(v_inst_2404_);
    v_toPure_2410_ = lean_ctor_get(v_toApplicative_2408_, 1);
    lean_inc_n(v_toPure_2410_, 2);
    lean_dec_ref(v_toApplicative_2408_);
    v___f_2411_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2412_ = 1;
    v___x_2413_ = lean_box((v___x_2412_) as usize);
    v___f_2414_ = lean_alloc_closure(
        l_Std_Iter_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2414_, 0, v_toPure_2410_);
    lean_closure_set(v___f_2414_, 1, v___x_2413_);
    v___f_2415_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2415_, 0, v_toPure_2410_);
    v___f_2416_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2416_, 0, v_p_2406_);
    lean_closure_set(v___f_2416_, 1, v_toBind_2409_);
    lean_closure_set(v___f_2416_, 2, v___f_2414_);
    lean_closure_set(v___f_2416_, 3, v___f_2415_);
    v___x_2417_ = lean_box((v___x_2412_) as usize);
    v___x_2418_ = lean_apply_6(
        v_inst_2405_,
        v___f_2411_,
        lean_box(0),
        lean_box(0),
        v_it_2407_,
        v___x_2417_,
        v___f_2416_,
    );
    return v___x_2418_;
}
pub unsafe fn l_Std_Iter_Total_allM(
    mut v_00_u03b1_2419_: *mut LeanObject,
    mut v_00_u03b2_2420_: *mut LeanObject,
    mut v_m_2421_: *mut LeanObject,
    mut v_inst_2422_: *mut LeanObject,
    mut v_inst_2423_: *mut LeanObject,
    mut v_inst_2424_: *mut LeanObject,
    mut v_inst_2425_: *mut LeanObject,
    mut v_p_2426_: *mut LeanObject,
    mut v_it_2427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: u8 = 0;
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2428_ = lean_ctor_get(v_inst_2422_, 0);
    lean_inc_ref(v_toApplicative_2428_);
    v_toBind_2429_ = lean_ctor_get(v_inst_2422_, 1);
    lean_inc(v_toBind_2429_);
    lean_dec_ref(v_inst_2422_);
    v_toPure_2430_ = lean_ctor_get(v_toApplicative_2428_, 1);
    lean_inc_n(v_toPure_2430_, 2);
    lean_dec_ref(v_toApplicative_2428_);
    v___f_2431_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2432_ = 1;
    v___x_2433_ = lean_box((v___x_2432_) as usize);
    v___f_2434_ = lean_alloc_closure(
        l_Std_Iter_allM___redArg___lam__1___boxed as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2434_, 0, v_toPure_2430_);
    lean_closure_set(v___f_2434_, 1, v___x_2433_);
    v___f_2435_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2435_, 0, v_toPure_2430_);
    v___f_2436_ = lean_alloc_closure(
        l_Std_Iter_anyM___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2436_, 0, v_p_2426_);
    lean_closure_set(v___f_2436_, 1, v_toBind_2429_);
    lean_closure_set(v___f_2436_, 2, v___f_2434_);
    lean_closure_set(v___f_2436_, 3, v___f_2435_);
    v___x_2437_ = lean_box((v___x_2432_) as usize);
    v___x_2438_ = lean_apply_6(
        v_inst_2424_,
        v___f_2431_,
        lean_box(0),
        lean_box(0),
        v_it_2427_,
        v___x_2437_,
        v___f_2436_,
    );
    return v___x_2438_;
}
pub unsafe fn l_Std_Iter_Total_allM___boxed(
    mut v_00_u03b1_2439_: *mut LeanObject,
    mut v_00_u03b2_2440_: *mut LeanObject,
    mut v_m_2441_: *mut LeanObject,
    mut v_inst_2442_: *mut LeanObject,
    mut v_inst_2443_: *mut LeanObject,
    mut v_inst_2444_: *mut LeanObject,
    mut v_inst_2445_: *mut LeanObject,
    mut v_p_2446_: *mut LeanObject,
    mut v_it_2447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2448_: *mut LeanObject = core::ptr::null_mut();
    v_res_2448_ = l_Std_Iter_Total_allM(
        v_00_u03b1_2439_,
        v_00_u03b2_2440_,
        v_m_2441_,
        v_inst_2442_,
        v_inst_2443_,
        v_inst_2444_,
        v_inst_2445_,
        v_p_2446_,
        v_it_2447_,
    );
    lean_dec(v_inst_2443_);
    return v_res_2448_;
}
pub unsafe fn l_Std_Iter_all___redArg___lam__1(
    mut v_p_2449_: *mut LeanObject,
    mut v___x_2450_: u8,
    mut v_x1_2451_: *mut LeanObject,
    mut v_x2_2452_: *mut LeanObject,
    mut v_x3_2453_: u8,
) -> *mut LeanObject {
    let mut v___x_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2455_: u8 = 0;
    v___x_2454_ = lean_apply_1(v_p_2449_, v_x1_2451_);
    v___x_2455_ = (lean_unbox(v___x_2454_) as u8);
    if v___x_2455_ == 0 {
        let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
        v___x_2456_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2456_, 0, v___x_2454_);
        return v___x_2456_;
    } else {
        let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
        v___x_2457_ = lean_box((v___x_2450_) as usize);
        v___x_2458_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2458_, 0, v___x_2457_);
        return v___x_2458_;
    }
}
pub unsafe fn l_Std_Iter_all___redArg___lam__1___boxed(
    mut v_p_2459_: *mut LeanObject,
    mut v___x_2460_: *mut LeanObject,
    mut v_x1_2461_: *mut LeanObject,
    mut v_x2_2462_: *mut LeanObject,
    mut v_x3_2463_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_280__boxed_2464_: u8 = 0;
    let mut v_x3_283__boxed_2465_: u8 = 0;
    let mut v_res_2466_: *mut LeanObject = core::ptr::null_mut();
    v___x_280__boxed_2464_ = (lean_unbox(v___x_2460_) as u8);
    v_x3_283__boxed_2465_ = (lean_unbox(v_x3_2463_) as u8);
    v_res_2466_ = l_Std_Iter_all___redArg___lam__1(
        v_p_2459_,
        v___x_280__boxed_2464_,
        v_x1_2461_,
        v_x2_2462_,
        v_x3_283__boxed_2465_,
    );
    return v_res_2466_;
}
pub unsafe fn l_Std_Iter_all___redArg(
    mut v_inst_2467_: *mut LeanObject,
    mut v_p_2468_: *mut LeanObject,
    mut v_it_2469_: *mut LeanObject,
) -> u8 {
    let mut v___f_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: u8 = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: u8 = 0;
    v___f_2470_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2471_ = 1;
    v___x_2472_ = lean_box((v___x_2471_) as usize);
    v___f_2473_ = lean_alloc_closure(
        l_Std_Iter_all___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2473_, 0, v_p_2468_);
    lean_closure_set(v___f_2473_, 1, v___x_2472_);
    v___x_2474_ = lean_box((v___x_2471_) as usize);
    v___x_2475_ = lean_apply_6(
        v_inst_2467_,
        v___f_2470_,
        lean_box(0),
        lean_box(0),
        v_it_2469_,
        v___x_2474_,
        v___f_2473_,
    );
    v___x_2476_ = (lean_unbox(v___x_2475_) as u8);
    return v___x_2476_;
}
pub unsafe fn l_Std_Iter_all___redArg___boxed(
    mut v_inst_2477_: *mut LeanObject,
    mut v_p_2478_: *mut LeanObject,
    mut v_it_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2480_: u8 = 0;
    let mut v_r_2481_: *mut LeanObject = core::ptr::null_mut();
    v_res_2480_ = l_Std_Iter_all___redArg(v_inst_2477_, v_p_2478_, v_it_2479_);
    v_r_2481_ = lean_box((v_res_2480_) as usize);
    return v_r_2481_;
}
pub unsafe fn l_Std_Iter_all(
    mut v_00_u03b1_2482_: *mut LeanObject,
    mut v_00_u03b2_2483_: *mut LeanObject,
    mut v_inst_2484_: *mut LeanObject,
    mut v_inst_2485_: *mut LeanObject,
    mut v_p_2486_: *mut LeanObject,
    mut v_it_2487_: *mut LeanObject,
) -> u8 {
    let mut v___f_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: u8 = 0;
    v___f_2488_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2489_ = 1;
    v___x_2490_ = lean_box((v___x_2489_) as usize);
    v___f_2491_ = lean_alloc_closure(
        l_Std_Iter_all___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2491_, 0, v_p_2486_);
    lean_closure_set(v___f_2491_, 1, v___x_2490_);
    v___x_2492_ = lean_box((v___x_2489_) as usize);
    v___x_2493_ = lean_apply_6(
        v_inst_2485_,
        v___f_2488_,
        lean_box(0),
        lean_box(0),
        v_it_2487_,
        v___x_2492_,
        v___f_2491_,
    );
    v___x_2494_ = (lean_unbox(v___x_2493_) as u8);
    return v___x_2494_;
}
pub unsafe fn l_Std_Iter_all___boxed(
    mut v_00_u03b1_2495_: *mut LeanObject,
    mut v_00_u03b2_2496_: *mut LeanObject,
    mut v_inst_2497_: *mut LeanObject,
    mut v_inst_2498_: *mut LeanObject,
    mut v_p_2499_: *mut LeanObject,
    mut v_it_2500_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2501_: u8 = 0;
    let mut v_r_2502_: *mut LeanObject = core::ptr::null_mut();
    v_res_2501_ = l_Std_Iter_all(
        v_00_u03b1_2495_,
        v_00_u03b2_2496_,
        v_inst_2497_,
        v_inst_2498_,
        v_p_2499_,
        v_it_2500_,
    );
    lean_dec(v_inst_2497_);
    v_r_2502_ = lean_box((v_res_2501_) as usize);
    return v_r_2502_;
}
pub unsafe fn l_Std_Iter_Total_all___redArg(
    mut v_inst_2503_: *mut LeanObject,
    mut v_p_2504_: *mut LeanObject,
    mut v_it_2505_: *mut LeanObject,
) -> u8 {
    let mut v___f_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: u8 = 0;
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: u8 = 0;
    v___f_2506_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2507_ = 1;
    v___x_2508_ = lean_box((v___x_2507_) as usize);
    v___f_2509_ = lean_alloc_closure(
        l_Std_Iter_all___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2509_, 0, v_p_2504_);
    lean_closure_set(v___f_2509_, 1, v___x_2508_);
    v___x_2510_ = lean_box((v___x_2507_) as usize);
    v___x_2511_ = lean_apply_6(
        v_inst_2503_,
        v___f_2506_,
        lean_box(0),
        lean_box(0),
        v_it_2505_,
        v___x_2510_,
        v___f_2509_,
    );
    v___x_2512_ = (lean_unbox(v___x_2511_) as u8);
    return v___x_2512_;
}
pub unsafe fn l_Std_Iter_Total_all___redArg___boxed(
    mut v_inst_2513_: *mut LeanObject,
    mut v_p_2514_: *mut LeanObject,
    mut v_it_2515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2516_: u8 = 0;
    let mut v_r_2517_: *mut LeanObject = core::ptr::null_mut();
    v_res_2516_ = l_Std_Iter_Total_all___redArg(v_inst_2513_, v_p_2514_, v_it_2515_);
    v_r_2517_ = lean_box((v_res_2516_) as usize);
    return v_r_2517_;
}
pub unsafe fn l_Std_Iter_Total_all(
    mut v_00_u03b1_2518_: *mut LeanObject,
    mut v_00_u03b2_2519_: *mut LeanObject,
    mut v_inst_2520_: *mut LeanObject,
    mut v_inst_2521_: *mut LeanObject,
    mut v_inst_2522_: *mut LeanObject,
    mut v_p_2523_: *mut LeanObject,
    mut v_it_2524_: *mut LeanObject,
) -> u8 {
    let mut v___f_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    v___f_2525_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2526_ = 1;
    v___x_2527_ = lean_box((v___x_2526_) as usize);
    v___f_2528_ = lean_alloc_closure(
        l_Std_Iter_all___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2528_, 0, v_p_2523_);
    lean_closure_set(v___f_2528_, 1, v___x_2527_);
    v___x_2529_ = lean_box((v___x_2526_) as usize);
    v___x_2530_ = lean_apply_6(
        v_inst_2521_,
        v___f_2525_,
        lean_box(0),
        lean_box(0),
        v_it_2524_,
        v___x_2529_,
        v___f_2528_,
    );
    v___x_2531_ = (lean_unbox(v___x_2530_) as u8);
    return v___x_2531_;
}
pub unsafe fn l_Std_Iter_Total_all___boxed(
    mut v_00_u03b1_2532_: *mut LeanObject,
    mut v_00_u03b2_2533_: *mut LeanObject,
    mut v_inst_2534_: *mut LeanObject,
    mut v_inst_2535_: *mut LeanObject,
    mut v_inst_2536_: *mut LeanObject,
    mut v_p_2537_: *mut LeanObject,
    mut v_it_2538_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2539_: u8 = 0;
    let mut v_r_2540_: *mut LeanObject = core::ptr::null_mut();
    v_res_2539_ = l_Std_Iter_Total_all(
        v_00_u03b1_2532_,
        v_00_u03b2_2533_,
        v_inst_2534_,
        v_inst_2535_,
        v_inst_2536_,
        v_p_2537_,
        v_it_2538_,
    );
    lean_dec(v_inst_2534_);
    v_r_2540_ = lean_box((v_res_2539_) as usize);
    return v_r_2540_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___redArg___lam__1(
    mut v_toPure_2541_: *mut LeanObject,
    mut v_____do__lift_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    v___x_2543_ = lean_apply_2(v_toPure_2541_, lean_box(0), v_____do__lift_2542_);
    return v___x_2543_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___redArg___lam__0(
    mut v___x_2544_: *mut LeanObject,
    mut v_toPure_2545_: *mut LeanObject,
    mut v_____do__lift_2546_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_2546_) == 0 {
        let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2548_: *mut LeanObject = core::ptr::null_mut();
        v___x_2547_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2547_, 0, v___x_2544_);
        v___x_2548_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2547_);
        return v___x_2548_;
    } else {
        let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2544_);
        v___x_2549_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2549_, 0, v_____do__lift_2546_);
        v___x_2550_ = lean_apply_2(v_toPure_2545_, lean_box(0), v___x_2549_);
        return v___x_2550_;
    }
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___redArg___lam__2(
    mut v_f_2551_: *mut LeanObject,
    mut v_toBind_2552_: *mut LeanObject,
    mut v___f_2553_: *mut LeanObject,
    mut v___f_2554_: *mut LeanObject,
    mut v_x1_2555_: *mut LeanObject,
    mut v_x2_2556_: *mut LeanObject,
    mut v_x3_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    v___x_2558_ = lean_apply_1(v_f_2551_, v_x1_2555_);
    lean_inc(v_toBind_2552_);
    v___x_2559_ = lean_apply_4(
        v_toBind_2552_,
        lean_box(0),
        lean_box(0),
        v___x_2558_,
        v___f_2553_,
    );
    v___x_2560_ = lean_apply_4(
        v_toBind_2552_,
        lean_box(0),
        lean_box(0),
        v___x_2559_,
        v___f_2554_,
    );
    return v___x_2560_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed(
    mut v_f_2561_: *mut LeanObject,
    mut v_toBind_2562_: *mut LeanObject,
    mut v___f_2563_: *mut LeanObject,
    mut v___f_2564_: *mut LeanObject,
    mut v_x1_2565_: *mut LeanObject,
    mut v_x2_2566_: *mut LeanObject,
    mut v_x3_2567_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2568_: *mut LeanObject = core::ptr::null_mut();
    v_res_2568_ = l_Std_Iter_findSomeM_x3f___redArg___lam__2(
        v_f_2561_,
        v_toBind_2562_,
        v___f_2563_,
        v___f_2564_,
        v_x1_2565_,
        v_x2_2566_,
        v_x3_2567_,
    );
    lean_dec(v_x3_2567_);
    return v_res_2568_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___redArg(
    mut v_inst_2569_: *mut LeanObject,
    mut v_inst_2570_: *mut LeanObject,
    mut v_it_2571_: *mut LeanObject,
    mut v_f_2572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2573_ = lean_ctor_get(v_inst_2569_, 0);
    lean_inc_ref(v_toApplicative_2573_);
    v_toBind_2574_ = lean_ctor_get(v_inst_2569_, 1);
    lean_inc(v_toBind_2574_);
    lean_dec_ref(v_inst_2569_);
    v_toPure_2575_ = lean_ctor_get(v_toApplicative_2573_, 1);
    lean_inc_n(v_toPure_2575_, 2);
    lean_dec_ref(v_toApplicative_2573_);
    v___f_2576_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2577_ = lean_box(0);
    v___f_2578_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2578_, 0, v_toPure_2575_);
    v___f_2579_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2579_, 0, v___x_2577_);
    lean_closure_set(v___f_2579_, 1, v_toPure_2575_);
    v___f_2580_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2580_, 0, v_f_2572_);
    lean_closure_set(v___f_2580_, 1, v_toBind_2574_);
    lean_closure_set(v___f_2580_, 2, v___f_2579_);
    lean_closure_set(v___f_2580_, 3, v___f_2578_);
    v___x_2581_ = lean_apply_6(
        v_inst_2570_,
        v___f_2576_,
        lean_box(0),
        lean_box(0),
        v_it_2571_,
        v___x_2577_,
        v___f_2580_,
    );
    return v___x_2581_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f(
    mut v_00_u03b1_2582_: *mut LeanObject,
    mut v_00_u03b2_2583_: *mut LeanObject,
    mut v_00_u03b3_2584_: *mut LeanObject,
    mut v_m_2585_: *mut LeanObject,
    mut v_inst_2586_: *mut LeanObject,
    mut v_inst_2587_: *mut LeanObject,
    mut v_inst_2588_: *mut LeanObject,
    mut v_it_2589_: *mut LeanObject,
    mut v_f_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2591_ = lean_ctor_get(v_inst_2586_, 0);
    lean_inc_ref(v_toApplicative_2591_);
    v_toBind_2592_ = lean_ctor_get(v_inst_2586_, 1);
    lean_inc(v_toBind_2592_);
    lean_dec_ref(v_inst_2586_);
    v_toPure_2593_ = lean_ctor_get(v_toApplicative_2591_, 1);
    lean_inc_n(v_toPure_2593_, 2);
    lean_dec_ref(v_toApplicative_2591_);
    v___f_2594_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2595_ = lean_box(0);
    v___f_2596_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2596_, 0, v_toPure_2593_);
    v___f_2597_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2597_, 0, v___x_2595_);
    lean_closure_set(v___f_2597_, 1, v_toPure_2593_);
    v___f_2598_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2598_, 0, v_f_2590_);
    lean_closure_set(v___f_2598_, 1, v_toBind_2592_);
    lean_closure_set(v___f_2598_, 2, v___f_2597_);
    lean_closure_set(v___f_2598_, 3, v___f_2596_);
    v___x_2599_ = lean_apply_6(
        v_inst_2588_,
        v___f_2594_,
        lean_box(0),
        lean_box(0),
        v_it_2589_,
        v___x_2595_,
        v___f_2598_,
    );
    return v___x_2599_;
}
pub unsafe fn l_Std_Iter_findSomeM_x3f___boxed(
    mut v_00_u03b1_2600_: *mut LeanObject,
    mut v_00_u03b2_2601_: *mut LeanObject,
    mut v_00_u03b3_2602_: *mut LeanObject,
    mut v_m_2603_: *mut LeanObject,
    mut v_inst_2604_: *mut LeanObject,
    mut v_inst_2605_: *mut LeanObject,
    mut v_inst_2606_: *mut LeanObject,
    mut v_it_2607_: *mut LeanObject,
    mut v_f_2608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2609_: *mut LeanObject = core::ptr::null_mut();
    v_res_2609_ = l_Std_Iter_findSomeM_x3f(
        v_00_u03b1_2600_,
        v_00_u03b2_2601_,
        v_00_u03b3_2602_,
        v_m_2603_,
        v_inst_2604_,
        v_inst_2605_,
        v_inst_2606_,
        v_it_2607_,
        v_f_2608_,
    );
    lean_dec(v_inst_2605_);
    return v_res_2609_;
}
pub unsafe fn l_Std_Iter_Partial_findSomeM_x3f___redArg(
    mut v_inst_2610_: *mut LeanObject,
    mut v_inst_2611_: *mut LeanObject,
    mut v_it_2612_: *mut LeanObject,
    mut v_f_2613_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2614_ = lean_ctor_get(v_inst_2610_, 0);
    lean_inc_ref(v_toApplicative_2614_);
    v_toBind_2615_ = lean_ctor_get(v_inst_2610_, 1);
    lean_inc(v_toBind_2615_);
    lean_dec_ref(v_inst_2610_);
    v_toPure_2616_ = lean_ctor_get(v_toApplicative_2614_, 1);
    lean_inc_n(v_toPure_2616_, 2);
    lean_dec_ref(v_toApplicative_2614_);
    v___f_2617_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2618_ = lean_box(0);
    v___f_2619_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2619_, 0, v___x_2618_);
    lean_closure_set(v___f_2619_, 1, v_toPure_2616_);
    v___f_2620_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2620_, 0, v_toPure_2616_);
    v___f_2621_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2621_, 0, v_f_2613_);
    lean_closure_set(v___f_2621_, 1, v_toBind_2615_);
    lean_closure_set(v___f_2621_, 2, v___f_2619_);
    lean_closure_set(v___f_2621_, 3, v___f_2620_);
    v___x_2622_ = lean_apply_6(
        v_inst_2611_,
        v___f_2617_,
        lean_box(0),
        lean_box(0),
        v_it_2612_,
        v___x_2618_,
        v___f_2621_,
    );
    return v___x_2622_;
}
pub unsafe fn l_Std_Iter_Partial_findSomeM_x3f(
    mut v_00_u03b1_2623_: *mut LeanObject,
    mut v_00_u03b2_2624_: *mut LeanObject,
    mut v_00_u03b3_2625_: *mut LeanObject,
    mut v_m_2626_: *mut LeanObject,
    mut v_inst_2627_: *mut LeanObject,
    mut v_inst_2628_: *mut LeanObject,
    mut v_inst_2629_: *mut LeanObject,
    mut v_it_2630_: *mut LeanObject,
    mut v_f_2631_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2632_ = lean_ctor_get(v_inst_2627_, 0);
    lean_inc_ref(v_toApplicative_2632_);
    v_toBind_2633_ = lean_ctor_get(v_inst_2627_, 1);
    lean_inc(v_toBind_2633_);
    lean_dec_ref(v_inst_2627_);
    v_toPure_2634_ = lean_ctor_get(v_toApplicative_2632_, 1);
    lean_inc_n(v_toPure_2634_, 2);
    lean_dec_ref(v_toApplicative_2632_);
    v___f_2635_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2636_ = lean_box(0);
    v___f_2637_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2637_, 0, v___x_2636_);
    lean_closure_set(v___f_2637_, 1, v_toPure_2634_);
    v___f_2638_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2638_, 0, v_toPure_2634_);
    v___f_2639_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2639_, 0, v_f_2631_);
    lean_closure_set(v___f_2639_, 1, v_toBind_2633_);
    lean_closure_set(v___f_2639_, 2, v___f_2637_);
    lean_closure_set(v___f_2639_, 3, v___f_2638_);
    v___x_2640_ = lean_apply_6(
        v_inst_2629_,
        v___f_2635_,
        lean_box(0),
        lean_box(0),
        v_it_2630_,
        v___x_2636_,
        v___f_2639_,
    );
    return v___x_2640_;
}
pub unsafe fn l_Std_Iter_Partial_findSomeM_x3f___boxed(
    mut v_00_u03b1_2641_: *mut LeanObject,
    mut v_00_u03b2_2642_: *mut LeanObject,
    mut v_00_u03b3_2643_: *mut LeanObject,
    mut v_m_2644_: *mut LeanObject,
    mut v_inst_2645_: *mut LeanObject,
    mut v_inst_2646_: *mut LeanObject,
    mut v_inst_2647_: *mut LeanObject,
    mut v_it_2648_: *mut LeanObject,
    mut v_f_2649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2650_: *mut LeanObject = core::ptr::null_mut();
    v_res_2650_ = l_Std_Iter_Partial_findSomeM_x3f(
        v_00_u03b1_2641_,
        v_00_u03b2_2642_,
        v_00_u03b3_2643_,
        v_m_2644_,
        v_inst_2645_,
        v_inst_2646_,
        v_inst_2647_,
        v_it_2648_,
        v_f_2649_,
    );
    lean_dec(v_inst_2646_);
    return v_res_2650_;
}
pub unsafe fn l_Std_Iter_Total_findSomeM_x3f___redArg(
    mut v_inst_2651_: *mut LeanObject,
    mut v_inst_2652_: *mut LeanObject,
    mut v_it_2653_: *mut LeanObject,
    mut v_f_2654_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2663_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2655_ = lean_ctor_get(v_inst_2651_, 0);
    lean_inc_ref(v_toApplicative_2655_);
    v_toBind_2656_ = lean_ctor_get(v_inst_2651_, 1);
    lean_inc(v_toBind_2656_);
    lean_dec_ref(v_inst_2651_);
    v_toPure_2657_ = lean_ctor_get(v_toApplicative_2655_, 1);
    lean_inc_n(v_toPure_2657_, 2);
    lean_dec_ref(v_toApplicative_2655_);
    v___f_2658_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2659_ = lean_box(0);
    v___f_2660_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2660_, 0, v___x_2659_);
    lean_closure_set(v___f_2660_, 1, v_toPure_2657_);
    v___f_2661_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2661_, 0, v_toPure_2657_);
    v___f_2662_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2662_, 0, v_f_2654_);
    lean_closure_set(v___f_2662_, 1, v_toBind_2656_);
    lean_closure_set(v___f_2662_, 2, v___f_2660_);
    lean_closure_set(v___f_2662_, 3, v___f_2661_);
    v___x_2663_ = lean_apply_6(
        v_inst_2652_,
        v___f_2658_,
        lean_box(0),
        lean_box(0),
        v_it_2653_,
        v___x_2659_,
        v___f_2662_,
    );
    return v___x_2663_;
}
pub unsafe fn l_Std_Iter_Total_findSomeM_x3f(
    mut v_00_u03b1_2664_: *mut LeanObject,
    mut v_00_u03b2_2665_: *mut LeanObject,
    mut v_00_u03b3_2666_: *mut LeanObject,
    mut v_m_2667_: *mut LeanObject,
    mut v_inst_2668_: *mut LeanObject,
    mut v_inst_2669_: *mut LeanObject,
    mut v_inst_2670_: *mut LeanObject,
    mut v_inst_2671_: *mut LeanObject,
    mut v_it_2672_: *mut LeanObject,
    mut v_f_2673_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2674_ = lean_ctor_get(v_inst_2668_, 0);
    lean_inc_ref(v_toApplicative_2674_);
    v_toBind_2675_ = lean_ctor_get(v_inst_2668_, 1);
    lean_inc(v_toBind_2675_);
    lean_dec_ref(v_inst_2668_);
    v_toPure_2676_ = lean_ctor_get(v_toApplicative_2674_, 1);
    lean_inc_n(v_toPure_2676_, 2);
    lean_dec_ref(v_toApplicative_2674_);
    v___f_2677_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2678_ = lean_box(0);
    v___f_2679_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2679_, 0, v___x_2678_);
    lean_closure_set(v___f_2679_, 1, v_toPure_2676_);
    v___f_2680_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2680_, 0, v_toPure_2676_);
    v___f_2681_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__2___boxed as *mut core::ffi::c_void,
        7,
        4,
    );
    lean_closure_set(v___f_2681_, 0, v_f_2673_);
    lean_closure_set(v___f_2681_, 1, v_toBind_2675_);
    lean_closure_set(v___f_2681_, 2, v___f_2679_);
    lean_closure_set(v___f_2681_, 3, v___f_2680_);
    v___x_2682_ = lean_apply_6(
        v_inst_2670_,
        v___f_2677_,
        lean_box(0),
        lean_box(0),
        v_it_2672_,
        v___x_2678_,
        v___f_2681_,
    );
    return v___x_2682_;
}
pub unsafe fn l_Std_Iter_Total_findSomeM_x3f___boxed(
    mut v_00_u03b1_2683_: *mut LeanObject,
    mut v_00_u03b2_2684_: *mut LeanObject,
    mut v_00_u03b3_2685_: *mut LeanObject,
    mut v_m_2686_: *mut LeanObject,
    mut v_inst_2687_: *mut LeanObject,
    mut v_inst_2688_: *mut LeanObject,
    mut v_inst_2689_: *mut LeanObject,
    mut v_inst_2690_: *mut LeanObject,
    mut v_it_2691_: *mut LeanObject,
    mut v_f_2692_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_res_2693_ = l_Std_Iter_Total_findSomeM_x3f(
        v_00_u03b1_2683_,
        v_00_u03b2_2684_,
        v_00_u03b3_2685_,
        v_m_2686_,
        v_inst_2687_,
        v_inst_2688_,
        v_inst_2689_,
        v_inst_2690_,
        v_it_2691_,
        v_f_2692_,
    );
    lean_dec(v_inst_2688_);
    return v_res_2693_;
}
pub unsafe fn l_Std_Iter_findSome_x3f___redArg___lam__1(
    mut v_f_2694_: *mut LeanObject,
    mut v___x_2695_: *mut LeanObject,
    mut v_x1_2696_: *mut LeanObject,
    mut v_x2_2697_: *mut LeanObject,
    mut v_x3_2698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    v___x_2699_ = lean_apply_1(v_f_2694_, v_x1_2696_);
    if lean_obj_tag(v___x_2699_) == 0 {
        let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
        v___x_2700_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2700_, 0, v___x_2695_);
        return v___x_2700_;
    } else {
        let mut v___x_2701_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2695_);
        v___x_2701_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2701_, 0, v___x_2699_);
        return v___x_2701_;
    }
}
pub unsafe fn l_Std_Iter_findSome_x3f___redArg___lam__1___boxed(
    mut v_f_2702_: *mut LeanObject,
    mut v___x_2703_: *mut LeanObject,
    mut v_x1_2704_: *mut LeanObject,
    mut v_x2_2705_: *mut LeanObject,
    mut v_x3_2706_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2707_: *mut LeanObject = core::ptr::null_mut();
    v_res_2707_ = l_Std_Iter_findSome_x3f___redArg___lam__1(
        v_f_2702_,
        v___x_2703_,
        v_x1_2704_,
        v_x2_2705_,
        v_x3_2706_,
    );
    lean_dec(v_x3_2706_);
    return v_res_2707_;
}
pub unsafe fn l_Std_Iter_findSome_x3f___redArg(
    mut v_inst_2708_: *mut LeanObject,
    mut v_it_2709_: *mut LeanObject,
    mut v_f_2710_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    v___f_2711_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2712_ = lean_box(0);
    v___f_2713_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2713_, 0, v_f_2710_);
    lean_closure_set(v___f_2713_, 1, v___x_2712_);
    v___x_2714_ = lean_apply_6(
        v_inst_2708_,
        v___f_2711_,
        lean_box(0),
        lean_box(0),
        v_it_2709_,
        v___x_2712_,
        v___f_2713_,
    );
    return v___x_2714_;
}
pub unsafe fn l_Std_Iter_findSome_x3f(
    mut v_00_u03b1_2715_: *mut LeanObject,
    mut v_00_u03b2_2716_: *mut LeanObject,
    mut v_00_u03b3_2717_: *mut LeanObject,
    mut v_inst_2718_: *mut LeanObject,
    mut v_inst_2719_: *mut LeanObject,
    mut v_it_2720_: *mut LeanObject,
    mut v_f_2721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    v___f_2722_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2723_ = lean_box(0);
    v___f_2724_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2724_, 0, v_f_2721_);
    lean_closure_set(v___f_2724_, 1, v___x_2723_);
    v___x_2725_ = lean_apply_6(
        v_inst_2719_,
        v___f_2722_,
        lean_box(0),
        lean_box(0),
        v_it_2720_,
        v___x_2723_,
        v___f_2724_,
    );
    return v___x_2725_;
}
pub unsafe fn l_Std_Iter_findSome_x3f___boxed(
    mut v_00_u03b1_2726_: *mut LeanObject,
    mut v_00_u03b2_2727_: *mut LeanObject,
    mut v_00_u03b3_2728_: *mut LeanObject,
    mut v_inst_2729_: *mut LeanObject,
    mut v_inst_2730_: *mut LeanObject,
    mut v_it_2731_: *mut LeanObject,
    mut v_f_2732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2733_: *mut LeanObject = core::ptr::null_mut();
    v_res_2733_ = l_Std_Iter_findSome_x3f(
        v_00_u03b1_2726_,
        v_00_u03b2_2727_,
        v_00_u03b3_2728_,
        v_inst_2729_,
        v_inst_2730_,
        v_it_2731_,
        v_f_2732_,
    );
    lean_dec(v_inst_2729_);
    return v_res_2733_;
}
pub unsafe fn l_Std_Iter_Partial_findSome_x3f___redArg(
    mut v_inst_2734_: *mut LeanObject,
    mut v_it_2735_: *mut LeanObject,
    mut v_f_2736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2740_: *mut LeanObject = core::ptr::null_mut();
    v___f_2737_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2738_ = lean_box(0);
    v___f_2739_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2739_, 0, v_f_2736_);
    lean_closure_set(v___f_2739_, 1, v___x_2738_);
    v___x_2740_ = lean_apply_6(
        v_inst_2734_,
        v___f_2737_,
        lean_box(0),
        lean_box(0),
        v_it_2735_,
        v___x_2738_,
        v___f_2739_,
    );
    return v___x_2740_;
}
pub unsafe fn l_Std_Iter_Partial_findSome_x3f(
    mut v_00_u03b1_2741_: *mut LeanObject,
    mut v_00_u03b2_2742_: *mut LeanObject,
    mut v_00_u03b3_2743_: *mut LeanObject,
    mut v_inst_2744_: *mut LeanObject,
    mut v_inst_2745_: *mut LeanObject,
    mut v_it_2746_: *mut LeanObject,
    mut v_f_2747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    v___f_2748_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2749_ = lean_box(0);
    v___f_2750_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2750_, 0, v_f_2747_);
    lean_closure_set(v___f_2750_, 1, v___x_2749_);
    v___x_2751_ = lean_apply_6(
        v_inst_2745_,
        v___f_2748_,
        lean_box(0),
        lean_box(0),
        v_it_2746_,
        v___x_2749_,
        v___f_2750_,
    );
    return v___x_2751_;
}
pub unsafe fn l_Std_Iter_Partial_findSome_x3f___boxed(
    mut v_00_u03b1_2752_: *mut LeanObject,
    mut v_00_u03b2_2753_: *mut LeanObject,
    mut v_00_u03b3_2754_: *mut LeanObject,
    mut v_inst_2755_: *mut LeanObject,
    mut v_inst_2756_: *mut LeanObject,
    mut v_it_2757_: *mut LeanObject,
    mut v_f_2758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2759_: *mut LeanObject = core::ptr::null_mut();
    v_res_2759_ = l_Std_Iter_Partial_findSome_x3f(
        v_00_u03b1_2752_,
        v_00_u03b2_2753_,
        v_00_u03b3_2754_,
        v_inst_2755_,
        v_inst_2756_,
        v_it_2757_,
        v_f_2758_,
    );
    lean_dec(v_inst_2755_);
    return v_res_2759_;
}
pub unsafe fn l_Std_Iter_Total_findSome_x3f___redArg(
    mut v_inst_2760_: *mut LeanObject,
    mut v_it_2761_: *mut LeanObject,
    mut v_f_2762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    v___f_2763_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2764_ = lean_box(0);
    v___f_2765_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2765_, 0, v_f_2762_);
    lean_closure_set(v___f_2765_, 1, v___x_2764_);
    v___x_2766_ = lean_apply_6(
        v_inst_2760_,
        v___f_2763_,
        lean_box(0),
        lean_box(0),
        v_it_2761_,
        v___x_2764_,
        v___f_2765_,
    );
    return v___x_2766_;
}
pub unsafe fn l_Std_Iter_Total_findSome_x3f(
    mut v_00_u03b1_2767_: *mut LeanObject,
    mut v_00_u03b2_2768_: *mut LeanObject,
    mut v_00_u03b3_2769_: *mut LeanObject,
    mut v_inst_2770_: *mut LeanObject,
    mut v_inst_2771_: *mut LeanObject,
    mut v_inst_2772_: *mut LeanObject,
    mut v_it_2773_: *mut LeanObject,
    mut v_f_2774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: *mut LeanObject = core::ptr::null_mut();
    v___f_2775_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2776_ = lean_box(0);
    v___f_2777_ = lean_alloc_closure(
        l_Std_Iter_findSome_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2777_, 0, v_f_2774_);
    lean_closure_set(v___f_2777_, 1, v___x_2776_);
    v___x_2778_ = lean_apply_6(
        v_inst_2771_,
        v___f_2775_,
        lean_box(0),
        lean_box(0),
        v_it_2773_,
        v___x_2776_,
        v___f_2777_,
    );
    return v___x_2778_;
}
pub unsafe fn l_Std_Iter_Total_findSome_x3f___boxed(
    mut v_00_u03b1_2779_: *mut LeanObject,
    mut v_00_u03b2_2780_: *mut LeanObject,
    mut v_00_u03b3_2781_: *mut LeanObject,
    mut v_inst_2782_: *mut LeanObject,
    mut v_inst_2783_: *mut LeanObject,
    mut v_inst_2784_: *mut LeanObject,
    mut v_it_2785_: *mut LeanObject,
    mut v_f_2786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2787_: *mut LeanObject = core::ptr::null_mut();
    v_res_2787_ = l_Std_Iter_Total_findSome_x3f(
        v_00_u03b1_2779_,
        v_00_u03b2_2780_,
        v_00_u03b3_2781_,
        v_inst_2782_,
        v_inst_2783_,
        v_inst_2784_,
        v_it_2785_,
        v_f_2786_,
    );
    lean_dec(v_inst_2782_);
    return v_res_2787_;
}
pub unsafe fn l_Std_Iter_findM_x3f___redArg___lam__3(
    mut v_toPure_2788_: *mut LeanObject,
    mut v___x_2789_: *mut LeanObject,
    mut v_x1_2790_: *mut LeanObject,
    mut v_____do__lift_2791_: u8,
) -> *mut LeanObject {
    if v_____do__lift_2791_ == 0 {
        let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x1_2790_);
        v___x_2792_ = lean_apply_2(v_toPure_2788_, lean_box(0), v___x_2789_);
        return v___x_2792_;
    } else {
        let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2789_);
        v___x_2793_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2793_, 0, v_x1_2790_);
        v___x_2794_ = lean_apply_2(v_toPure_2788_, lean_box(0), v___x_2793_);
        return v___x_2794_;
    }
}
pub unsafe fn l_Std_Iter_findM_x3f___redArg___lam__3___boxed(
    mut v_toPure_2795_: *mut LeanObject,
    mut v___x_2796_: *mut LeanObject,
    mut v_x1_2797_: *mut LeanObject,
    mut v_____do__lift_2798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_191__boxed_2799_: u8 = 0;
    let mut v_res_2800_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_191__boxed_2799_ = (lean_unbox(v_____do__lift_2798_) as u8);
    v_res_2800_ = l_Std_Iter_findM_x3f___redArg___lam__3(
        v_toPure_2795_,
        v___x_2796_,
        v_x1_2797_,
        v_____do__lift_191__boxed_2799_,
    );
    return v_res_2800_;
}
pub unsafe fn l_Std_Iter_findM_x3f___redArg___lam__0(
    mut v_toPure_2801_: *mut LeanObject,
    mut v___x_2802_: *mut LeanObject,
    mut v_f_2803_: *mut LeanObject,
    mut v_toBind_2804_: *mut LeanObject,
    mut v___f_2805_: *mut LeanObject,
    mut v___f_2806_: *mut LeanObject,
    mut v_x1_2807_: *mut LeanObject,
    mut v_x2_2808_: *mut LeanObject,
    mut v_x3_2809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_x1_2807_);
    v___f_2810_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__3___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_2810_, 0, v_toPure_2801_);
    lean_closure_set(v___f_2810_, 1, v___x_2802_);
    lean_closure_set(v___f_2810_, 2, v_x1_2807_);
    v___x_2811_ = lean_apply_1(v_f_2803_, v_x1_2807_);
    lean_inc_n(v_toBind_2804_, 2);
    v___x_2812_ = lean_apply_4(
        v_toBind_2804_,
        lean_box(0),
        lean_box(0),
        v___x_2811_,
        v___f_2810_,
    );
    v___x_2813_ = lean_apply_4(
        v_toBind_2804_,
        lean_box(0),
        lean_box(0),
        v___x_2812_,
        v___f_2805_,
    );
    v___x_2814_ = lean_apply_4(
        v_toBind_2804_,
        lean_box(0),
        lean_box(0),
        v___x_2813_,
        v___f_2806_,
    );
    return v___x_2814_;
}
pub unsafe fn l_Std_Iter_findM_x3f___redArg___lam__0___boxed(
    mut v_toPure_2815_: *mut LeanObject,
    mut v___x_2816_: *mut LeanObject,
    mut v_f_2817_: *mut LeanObject,
    mut v_toBind_2818_: *mut LeanObject,
    mut v___f_2819_: *mut LeanObject,
    mut v___f_2820_: *mut LeanObject,
    mut v_x1_2821_: *mut LeanObject,
    mut v_x2_2822_: *mut LeanObject,
    mut v_x3_2823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2824_: *mut LeanObject = core::ptr::null_mut();
    v_res_2824_ = l_Std_Iter_findM_x3f___redArg___lam__0(
        v_toPure_2815_,
        v___x_2816_,
        v_f_2817_,
        v_toBind_2818_,
        v___f_2819_,
        v___f_2820_,
        v_x1_2821_,
        v_x2_2822_,
        v_x3_2823_,
    );
    lean_dec(v_x3_2823_);
    return v_res_2824_;
}
pub unsafe fn l_Std_Iter_findM_x3f___redArg(
    mut v_inst_2825_: *mut LeanObject,
    mut v_inst_2826_: *mut LeanObject,
    mut v_it_2827_: *mut LeanObject,
    mut v_f_2828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2829_ = lean_ctor_get(v_inst_2825_, 0);
    lean_inc_ref(v_toApplicative_2829_);
    v_toBind_2830_ = lean_ctor_get(v_inst_2825_, 1);
    lean_inc(v_toBind_2830_);
    lean_dec_ref(v_inst_2825_);
    v_toPure_2831_ = lean_ctor_get(v_toApplicative_2829_, 1);
    lean_inc_n(v_toPure_2831_, 3);
    lean_dec_ref(v_toApplicative_2829_);
    v___f_2832_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2833_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2833_, 0, v_toPure_2831_);
    v___x_2834_ = lean_box(0);
    v___f_2835_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2835_, 0, v___x_2834_);
    lean_closure_set(v___f_2835_, 1, v_toPure_2831_);
    v___f_2836_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2836_, 0, v_toPure_2831_);
    lean_closure_set(v___f_2836_, 1, v___x_2834_);
    lean_closure_set(v___f_2836_, 2, v_f_2828_);
    lean_closure_set(v___f_2836_, 3, v_toBind_2830_);
    lean_closure_set(v___f_2836_, 4, v___f_2835_);
    lean_closure_set(v___f_2836_, 5, v___f_2833_);
    v___x_2837_ = lean_apply_6(
        v_inst_2826_,
        v___f_2832_,
        lean_box(0),
        lean_box(0),
        v_it_2827_,
        v___x_2834_,
        v___f_2836_,
    );
    return v___x_2837_;
}
pub unsafe fn l_Std_Iter_findM_x3f(
    mut v_00_u03b1_2838_: *mut LeanObject,
    mut v_00_u03b2_2839_: *mut LeanObject,
    mut v_m_2840_: *mut LeanObject,
    mut v_inst_2841_: *mut LeanObject,
    mut v_inst_2842_: *mut LeanObject,
    mut v_inst_2843_: *mut LeanObject,
    mut v_it_2844_: *mut LeanObject,
    mut v_f_2845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2846_ = lean_ctor_get(v_inst_2841_, 0);
    lean_inc_ref(v_toApplicative_2846_);
    v_toBind_2847_ = lean_ctor_get(v_inst_2841_, 1);
    lean_inc(v_toBind_2847_);
    lean_dec_ref(v_inst_2841_);
    v_toPure_2848_ = lean_ctor_get(v_toApplicative_2846_, 1);
    lean_inc_n(v_toPure_2848_, 3);
    lean_dec_ref(v_toApplicative_2846_);
    v___f_2849_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2850_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2850_, 0, v_toPure_2848_);
    v___x_2851_ = lean_box(0);
    v___f_2852_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2852_, 0, v___x_2851_);
    lean_closure_set(v___f_2852_, 1, v_toPure_2848_);
    v___f_2853_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2853_, 0, v_toPure_2848_);
    lean_closure_set(v___f_2853_, 1, v___x_2851_);
    lean_closure_set(v___f_2853_, 2, v_f_2845_);
    lean_closure_set(v___f_2853_, 3, v_toBind_2847_);
    lean_closure_set(v___f_2853_, 4, v___f_2852_);
    lean_closure_set(v___f_2853_, 5, v___f_2850_);
    v___x_2854_ = lean_apply_6(
        v_inst_2843_,
        v___f_2849_,
        lean_box(0),
        lean_box(0),
        v_it_2844_,
        v___x_2851_,
        v___f_2853_,
    );
    return v___x_2854_;
}
pub unsafe fn l_Std_Iter_findM_x3f___boxed(
    mut v_00_u03b1_2855_: *mut LeanObject,
    mut v_00_u03b2_2856_: *mut LeanObject,
    mut v_m_2857_: *mut LeanObject,
    mut v_inst_2858_: *mut LeanObject,
    mut v_inst_2859_: *mut LeanObject,
    mut v_inst_2860_: *mut LeanObject,
    mut v_it_2861_: *mut LeanObject,
    mut v_f_2862_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2863_: *mut LeanObject = core::ptr::null_mut();
    v_res_2863_ = l_Std_Iter_findM_x3f(
        v_00_u03b1_2855_,
        v_00_u03b2_2856_,
        v_m_2857_,
        v_inst_2858_,
        v_inst_2859_,
        v_inst_2860_,
        v_it_2861_,
        v_f_2862_,
    );
    lean_dec(v_inst_2859_);
    return v_res_2863_;
}
pub unsafe fn l_Std_Iter_Partial_findM_x3f___redArg(
    mut v_inst_2864_: *mut LeanObject,
    mut v_inst_2865_: *mut LeanObject,
    mut v_it_2866_: *mut LeanObject,
    mut v_f_2867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2868_ = lean_ctor_get(v_inst_2864_, 0);
    lean_inc_ref(v_toApplicative_2868_);
    v_toBind_2869_ = lean_ctor_get(v_inst_2864_, 1);
    lean_inc(v_toBind_2869_);
    lean_dec_ref(v_inst_2864_);
    v_toPure_2870_ = lean_ctor_get(v_toApplicative_2868_, 1);
    lean_inc_n(v_toPure_2870_, 3);
    lean_dec_ref(v_toApplicative_2868_);
    v___f_2871_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2872_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2872_, 0, v_toPure_2870_);
    v___x_2873_ = lean_box(0);
    v___f_2874_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2874_, 0, v___x_2873_);
    lean_closure_set(v___f_2874_, 1, v_toPure_2870_);
    v___f_2875_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2875_, 0, v_toPure_2870_);
    lean_closure_set(v___f_2875_, 1, v___x_2873_);
    lean_closure_set(v___f_2875_, 2, v_f_2867_);
    lean_closure_set(v___f_2875_, 3, v_toBind_2869_);
    lean_closure_set(v___f_2875_, 4, v___f_2874_);
    lean_closure_set(v___f_2875_, 5, v___f_2872_);
    v___x_2876_ = lean_apply_6(
        v_inst_2865_,
        v___f_2871_,
        lean_box(0),
        lean_box(0),
        v_it_2866_,
        v___x_2873_,
        v___f_2875_,
    );
    return v___x_2876_;
}
pub unsafe fn l_Std_Iter_Partial_findM_x3f(
    mut v_00_u03b1_2877_: *mut LeanObject,
    mut v_00_u03b2_2878_: *mut LeanObject,
    mut v_m_2879_: *mut LeanObject,
    mut v_inst_2880_: *mut LeanObject,
    mut v_inst_2881_: *mut LeanObject,
    mut v_inst_2882_: *mut LeanObject,
    mut v_it_2883_: *mut LeanObject,
    mut v_f_2884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2885_ = lean_ctor_get(v_inst_2880_, 0);
    lean_inc_ref(v_toApplicative_2885_);
    v_toBind_2886_ = lean_ctor_get(v_inst_2880_, 1);
    lean_inc(v_toBind_2886_);
    lean_dec_ref(v_inst_2880_);
    v_toPure_2887_ = lean_ctor_get(v_toApplicative_2885_, 1);
    lean_inc_n(v_toPure_2887_, 3);
    lean_dec_ref(v_toApplicative_2885_);
    v___f_2888_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2889_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2889_, 0, v_toPure_2887_);
    v___x_2890_ = lean_box(0);
    v___f_2891_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2891_, 0, v___x_2890_);
    lean_closure_set(v___f_2891_, 1, v_toPure_2887_);
    v___f_2892_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2892_, 0, v_toPure_2887_);
    lean_closure_set(v___f_2892_, 1, v___x_2890_);
    lean_closure_set(v___f_2892_, 2, v_f_2884_);
    lean_closure_set(v___f_2892_, 3, v_toBind_2886_);
    lean_closure_set(v___f_2892_, 4, v___f_2891_);
    lean_closure_set(v___f_2892_, 5, v___f_2889_);
    v___x_2893_ = lean_apply_6(
        v_inst_2882_,
        v___f_2888_,
        lean_box(0),
        lean_box(0),
        v_it_2883_,
        v___x_2890_,
        v___f_2892_,
    );
    return v___x_2893_;
}
pub unsafe fn l_Std_Iter_Partial_findM_x3f___boxed(
    mut v_00_u03b1_2894_: *mut LeanObject,
    mut v_00_u03b2_2895_: *mut LeanObject,
    mut v_m_2896_: *mut LeanObject,
    mut v_inst_2897_: *mut LeanObject,
    mut v_inst_2898_: *mut LeanObject,
    mut v_inst_2899_: *mut LeanObject,
    mut v_it_2900_: *mut LeanObject,
    mut v_f_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2902_: *mut LeanObject = core::ptr::null_mut();
    v_res_2902_ = l_Std_Iter_Partial_findM_x3f(
        v_00_u03b1_2894_,
        v_00_u03b2_2895_,
        v_m_2896_,
        v_inst_2897_,
        v_inst_2898_,
        v_inst_2899_,
        v_it_2900_,
        v_f_2901_,
    );
    lean_dec(v_inst_2898_);
    return v_res_2902_;
}
pub unsafe fn l_Std_Iter_Total_findM_x3f___redArg(
    mut v_inst_2903_: *mut LeanObject,
    mut v_inst_2904_: *mut LeanObject,
    mut v_it_2905_: *mut LeanObject,
    mut v_f_2906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2907_ = lean_ctor_get(v_inst_2903_, 0);
    lean_inc_ref(v_toApplicative_2907_);
    v_toBind_2908_ = lean_ctor_get(v_inst_2903_, 1);
    lean_inc(v_toBind_2908_);
    lean_dec_ref(v_inst_2903_);
    v_toPure_2909_ = lean_ctor_get(v_toApplicative_2907_, 1);
    lean_inc_n(v_toPure_2909_, 3);
    lean_dec_ref(v_toApplicative_2907_);
    v___f_2910_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2911_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2911_, 0, v_toPure_2909_);
    v___x_2912_ = lean_box(0);
    v___f_2913_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2913_, 0, v___x_2912_);
    lean_closure_set(v___f_2913_, 1, v_toPure_2909_);
    v___f_2914_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2914_, 0, v_toPure_2909_);
    lean_closure_set(v___f_2914_, 1, v___x_2912_);
    lean_closure_set(v___f_2914_, 2, v_f_2906_);
    lean_closure_set(v___f_2914_, 3, v_toBind_2908_);
    lean_closure_set(v___f_2914_, 4, v___f_2913_);
    lean_closure_set(v___f_2914_, 5, v___f_2911_);
    v___x_2915_ = lean_apply_6(
        v_inst_2904_,
        v___f_2910_,
        lean_box(0),
        lean_box(0),
        v_it_2905_,
        v___x_2912_,
        v___f_2914_,
    );
    return v___x_2915_;
}
pub unsafe fn l_Std_Iter_Total_findM_x3f(
    mut v_00_u03b1_2916_: *mut LeanObject,
    mut v_00_u03b2_2917_: *mut LeanObject,
    mut v_m_2918_: *mut LeanObject,
    mut v_inst_2919_: *mut LeanObject,
    mut v_inst_2920_: *mut LeanObject,
    mut v_inst_2921_: *mut LeanObject,
    mut v_inst_2922_: *mut LeanObject,
    mut v_it_2923_: *mut LeanObject,
    mut v_f_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2925_ = lean_ctor_get(v_inst_2919_, 0);
    lean_inc_ref(v_toApplicative_2925_);
    v_toBind_2926_ = lean_ctor_get(v_inst_2919_, 1);
    lean_inc(v_toBind_2926_);
    lean_dec_ref(v_inst_2919_);
    v_toPure_2927_ = lean_ctor_get(v_toApplicative_2925_, 1);
    lean_inc_n(v_toPure_2927_, 3);
    lean_dec_ref(v_toApplicative_2925_);
    v___f_2928_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___f_2929_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__1 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2929_, 0, v_toPure_2927_);
    v___x_2930_ = lean_box(0);
    v___f_2931_ = lean_alloc_closure(
        l_Std_Iter_findSomeM_x3f___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2931_, 0, v___x_2930_);
    lean_closure_set(v___f_2931_, 1, v_toPure_2927_);
    v___f_2932_ = lean_alloc_closure(
        l_Std_Iter_findM_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        6,
    );
    lean_closure_set(v___f_2932_, 0, v_toPure_2927_);
    lean_closure_set(v___f_2932_, 1, v___x_2930_);
    lean_closure_set(v___f_2932_, 2, v_f_2924_);
    lean_closure_set(v___f_2932_, 3, v_toBind_2926_);
    lean_closure_set(v___f_2932_, 4, v___f_2931_);
    lean_closure_set(v___f_2932_, 5, v___f_2929_);
    v___x_2933_ = lean_apply_6(
        v_inst_2921_,
        v___f_2928_,
        lean_box(0),
        lean_box(0),
        v_it_2923_,
        v___x_2930_,
        v___f_2932_,
    );
    return v___x_2933_;
}
pub unsafe fn l_Std_Iter_Total_findM_x3f___boxed(
    mut v_00_u03b1_2934_: *mut LeanObject,
    mut v_00_u03b2_2935_: *mut LeanObject,
    mut v_m_2936_: *mut LeanObject,
    mut v_inst_2937_: *mut LeanObject,
    mut v_inst_2938_: *mut LeanObject,
    mut v_inst_2939_: *mut LeanObject,
    mut v_inst_2940_: *mut LeanObject,
    mut v_it_2941_: *mut LeanObject,
    mut v_f_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ = l_Std_Iter_Total_findM_x3f(
        v_00_u03b1_2934_,
        v_00_u03b2_2935_,
        v_m_2936_,
        v_inst_2937_,
        v_inst_2938_,
        v_inst_2939_,
        v_inst_2940_,
        v_it_2941_,
        v_f_2942_,
    );
    lean_dec(v_inst_2938_);
    return v_res_2943_;
}
pub unsafe fn l_Std_Iter_find_x3f___redArg___lam__1(
    mut v_f_2944_: *mut LeanObject,
    mut v___x_2945_: *mut LeanObject,
    mut v_x1_2946_: *mut LeanObject,
    mut v_x2_2947_: *mut LeanObject,
    mut v_x3_2948_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: u8 = 0;
    lean_inc(v_x1_2946_);
    v___x_2949_ = lean_apply_1(v_f_2944_, v_x1_2946_);
    v___x_2950_ = (lean_unbox(v___x_2949_) as u8);
    if v___x_2950_ == 0 {
        let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x1_2946_);
        v___x_2951_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2951_, 0, v___x_2945_);
        return v___x_2951_;
    } else {
        let mut v___x_2952_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2953_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_2945_);
        v___x_2952_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2952_, 0, v_x1_2946_);
        v___x_2953_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2953_, 0, v___x_2952_);
        return v___x_2953_;
    }
}
pub unsafe fn l_Std_Iter_find_x3f___redArg___lam__1___boxed(
    mut v_f_2954_: *mut LeanObject,
    mut v___x_2955_: *mut LeanObject,
    mut v_x1_2956_: *mut LeanObject,
    mut v_x2_2957_: *mut LeanObject,
    mut v_x3_2958_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2959_: *mut LeanObject = core::ptr::null_mut();
    v_res_2959_ = l_Std_Iter_find_x3f___redArg___lam__1(
        v_f_2954_,
        v___x_2955_,
        v_x1_2956_,
        v_x2_2957_,
        v_x3_2958_,
    );
    lean_dec(v_x3_2958_);
    return v_res_2959_;
}
pub unsafe fn l_Std_Iter_find_x3f___redArg(
    mut v_inst_2960_: *mut LeanObject,
    mut v_it_2961_: *mut LeanObject,
    mut v_f_2962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    v___f_2963_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2964_ = lean_box(0);
    v___f_2965_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2965_, 0, v_f_2962_);
    lean_closure_set(v___f_2965_, 1, v___x_2964_);
    v___x_2966_ = lean_apply_6(
        v_inst_2960_,
        v___f_2963_,
        lean_box(0),
        lean_box(0),
        v_it_2961_,
        v___x_2964_,
        v___f_2965_,
    );
    return v___x_2966_;
}
pub unsafe fn l_Std_Iter_find_x3f(
    mut v_00_u03b1_2967_: *mut LeanObject,
    mut v_00_u03b2_2968_: *mut LeanObject,
    mut v_inst_2969_: *mut LeanObject,
    mut v_inst_2970_: *mut LeanObject,
    mut v_it_2971_: *mut LeanObject,
    mut v_f_2972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut LeanObject = core::ptr::null_mut();
    v___f_2973_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2974_ = lean_box(0);
    v___f_2975_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2975_, 0, v_f_2972_);
    lean_closure_set(v___f_2975_, 1, v___x_2974_);
    v___x_2976_ = lean_apply_6(
        v_inst_2970_,
        v___f_2973_,
        lean_box(0),
        lean_box(0),
        v_it_2971_,
        v___x_2974_,
        v___f_2975_,
    );
    return v___x_2976_;
}
pub unsafe fn l_Std_Iter_find_x3f___boxed(
    mut v_00_u03b1_2977_: *mut LeanObject,
    mut v_00_u03b2_2978_: *mut LeanObject,
    mut v_inst_2979_: *mut LeanObject,
    mut v_inst_2980_: *mut LeanObject,
    mut v_it_2981_: *mut LeanObject,
    mut v_f_2982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2983_: *mut LeanObject = core::ptr::null_mut();
    v_res_2983_ = l_Std_Iter_find_x3f(
        v_00_u03b1_2977_,
        v_00_u03b2_2978_,
        v_inst_2979_,
        v_inst_2980_,
        v_it_2981_,
        v_f_2982_,
    );
    lean_dec(v_inst_2979_);
    return v_res_2983_;
}
pub unsafe fn l_Std_Iter_Partial_find_x3f___redArg(
    mut v_inst_2984_: *mut LeanObject,
    mut v_it_2985_: *mut LeanObject,
    mut v_f_2986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut LeanObject = core::ptr::null_mut();
    v___f_2987_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2988_ = lean_box(0);
    v___f_2989_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2989_, 0, v_f_2986_);
    lean_closure_set(v___f_2989_, 1, v___x_2988_);
    v___x_2990_ = lean_apply_6(
        v_inst_2984_,
        v___f_2987_,
        lean_box(0),
        lean_box(0),
        v_it_2985_,
        v___x_2988_,
        v___f_2989_,
    );
    return v___x_2990_;
}
pub unsafe fn l_Std_Iter_Partial_find_x3f(
    mut v_00_u03b1_2991_: *mut LeanObject,
    mut v_00_u03b2_2992_: *mut LeanObject,
    mut v_inst_2993_: *mut LeanObject,
    mut v_inst_2994_: *mut LeanObject,
    mut v_it_2995_: *mut LeanObject,
    mut v_f_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
    v___f_2997_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_2998_ = lean_box(0);
    v___f_2999_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_2999_, 0, v_f_2996_);
    lean_closure_set(v___f_2999_, 1, v___x_2998_);
    v___x_3000_ = lean_apply_6(
        v_inst_2994_,
        v___f_2997_,
        lean_box(0),
        lean_box(0),
        v_it_2995_,
        v___x_2998_,
        v___f_2999_,
    );
    return v___x_3000_;
}
pub unsafe fn l_Std_Iter_Partial_find_x3f___boxed(
    mut v_00_u03b1_3001_: *mut LeanObject,
    mut v_00_u03b2_3002_: *mut LeanObject,
    mut v_inst_3003_: *mut LeanObject,
    mut v_inst_3004_: *mut LeanObject,
    mut v_it_3005_: *mut LeanObject,
    mut v_f_3006_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3007_: *mut LeanObject = core::ptr::null_mut();
    v_res_3007_ = l_Std_Iter_Partial_find_x3f(
        v_00_u03b1_3001_,
        v_00_u03b2_3002_,
        v_inst_3003_,
        v_inst_3004_,
        v_it_3005_,
        v_f_3006_,
    );
    lean_dec(v_inst_3003_);
    return v_res_3007_;
}
pub unsafe fn l_Std_Iter_Total_find_x3f___redArg(
    mut v_inst_3008_: *mut LeanObject,
    mut v_it_3009_: *mut LeanObject,
    mut v_f_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    v___f_3011_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_3012_ = lean_box(0);
    v___f_3013_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_3013_, 0, v_f_3010_);
    lean_closure_set(v___f_3013_, 1, v___x_3012_);
    v___x_3014_ = lean_apply_6(
        v_inst_3008_,
        v___f_3011_,
        lean_box(0),
        lean_box(0),
        v_it_3009_,
        v___x_3012_,
        v___f_3013_,
    );
    return v___x_3014_;
}
pub unsafe fn l_Std_Iter_Total_find_x3f(
    mut v_00_u03b1_3015_: *mut LeanObject,
    mut v_00_u03b2_3016_: *mut LeanObject,
    mut v_inst_3017_: *mut LeanObject,
    mut v_inst_3018_: *mut LeanObject,
    mut v_inst_3019_: *mut LeanObject,
    mut v_it_3020_: *mut LeanObject,
    mut v_f_3021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    v___f_3022_ = l_Std_Iter_instForIn_x27___redArg___closed__0;
    v___x_3023_ = lean_box(0);
    v___f_3024_ = lean_alloc_closure(
        l_Std_Iter_find_x3f___redArg___lam__1___boxed as *mut core::ffi::c_void,
        5,
        2,
    );
    lean_closure_set(v___f_3024_, 0, v_f_3021_);
    lean_closure_set(v___f_3024_, 1, v___x_3023_);
    v___x_3025_ = lean_apply_6(
        v_inst_3018_,
        v___f_3022_,
        lean_box(0),
        lean_box(0),
        v_it_3020_,
        v___x_3023_,
        v___f_3024_,
    );
    return v___x_3025_;
}
pub unsafe fn l_Std_Iter_Total_find_x3f___boxed(
    mut v_00_u03b1_3026_: *mut LeanObject,
    mut v_00_u03b2_3027_: *mut LeanObject,
    mut v_inst_3028_: *mut LeanObject,
    mut v_inst_3029_: *mut LeanObject,
    mut v_inst_3030_: *mut LeanObject,
    mut v_it_3031_: *mut LeanObject,
    mut v_f_3032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3033_: *mut LeanObject = core::ptr::null_mut();
    v_res_3033_ = l_Std_Iter_Total_find_x3f(
        v_00_u03b1_3026_,
        v_00_u03b2_3027_,
        v_inst_3028_,
        v_inst_3029_,
        v_inst_3030_,
        v_it_3031_,
        v_f_3032_,
    );
    lean_dec(v_inst_3028_);
    return v_res_3033_;
}
pub unsafe fn l_Std_Iter_first_x3f___redArg___lam__0(
    mut v_x_3034_: *mut LeanObject,
    mut v_x_3035_: *mut LeanObject,
    mut v___y_3036_: *mut LeanObject,
    mut v___y_3037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    v___x_3038_ = lean_apply_1(v___y_3036_, v___y_3037_);
    return v___x_3038_;
}
pub unsafe fn l_Std_Iter_first_x3f___redArg___lam__1(
    mut v_b_3039_: *mut LeanObject,
    mut v_x_3040_: *mut LeanObject,
    mut v_x_3041_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3043_: *mut LeanObject = core::ptr::null_mut();
    v___x_3042_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3042_, 0, v_b_3039_);
    v___x_3043_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3043_, 0, v___x_3042_);
    return v___x_3043_;
}
pub unsafe fn l_Std_Iter_first_x3f___redArg___lam__1___boxed(
    mut v_b_3044_: *mut LeanObject,
    mut v_x_3045_: *mut LeanObject,
    mut v_x_3046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3047_: *mut LeanObject = core::ptr::null_mut();
    v_res_3047_ = l_Std_Iter_first_x3f___redArg___lam__1(v_b_3044_, v_x_3045_, v_x_3046_);
    lean_dec(v_x_3046_);
    return v_res_3047_;
}
pub unsafe fn l_Std_Iter_first_x3f___redArg(
    mut v_inst_3050_: *mut LeanObject,
    mut v_it_3051_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    v___f_3052_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3053_ = l_Std_Iter_first_x3f___redArg___closed__1;
    v___x_3054_ = lean_box(0);
    v___x_3055_ = lean_apply_6(
        v_inst_3050_,
        v___f_3052_,
        lean_box(0),
        lean_box(0),
        v_it_3051_,
        v___x_3054_,
        v___f_3053_,
    );
    return v___x_3055_;
}
pub unsafe fn l_Std_Iter_first_x3f(
    mut v_00_u03b1_3056_: *mut LeanObject,
    mut v_00_u03b2_3057_: *mut LeanObject,
    mut v_inst_3058_: *mut LeanObject,
    mut v_inst_3059_: *mut LeanObject,
    mut v_it_3060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    v___f_3061_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3062_ = l_Std_Iter_first_x3f___redArg___closed__1;
    v___x_3063_ = lean_box(0);
    v___x_3064_ = lean_apply_6(
        v_inst_3059_,
        v___f_3061_,
        lean_box(0),
        lean_box(0),
        v_it_3060_,
        v___x_3063_,
        v___f_3062_,
    );
    return v___x_3064_;
}
pub unsafe fn l_Std_Iter_first_x3f___boxed(
    mut v_00_u03b1_3065_: *mut LeanObject,
    mut v_00_u03b2_3066_: *mut LeanObject,
    mut v_inst_3067_: *mut LeanObject,
    mut v_inst_3068_: *mut LeanObject,
    mut v_it_3069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3070_: *mut LeanObject = core::ptr::null_mut();
    v_res_3070_ = l_Std_Iter_first_x3f(
        v_00_u03b1_3065_,
        v_00_u03b2_3066_,
        v_inst_3067_,
        v_inst_3068_,
        v_it_3069_,
    );
    lean_dec(v_inst_3067_);
    return v_res_3070_;
}
pub unsafe fn l_Std_Iter_Total_first_x3f___redArg(
    mut v_inst_3071_: *mut LeanObject,
    mut v_it_3072_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    v___f_3073_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3074_ = l_Std_Iter_first_x3f___redArg___closed__1;
    v___x_3075_ = lean_box(0);
    v___x_3076_ = lean_apply_6(
        v_inst_3071_,
        v___f_3073_,
        lean_box(0),
        lean_box(0),
        v_it_3072_,
        v___x_3075_,
        v___f_3074_,
    );
    return v___x_3076_;
}
pub unsafe fn l_Std_Iter_Total_first_x3f(
    mut v_00_u03b1_3077_: *mut LeanObject,
    mut v_00_u03b2_3078_: *mut LeanObject,
    mut v_inst_3079_: *mut LeanObject,
    mut v_inst_3080_: *mut LeanObject,
    mut v_inst_3081_: *mut LeanObject,
    mut v_it_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    v___f_3083_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3084_ = l_Std_Iter_first_x3f___redArg___closed__1;
    v___x_3085_ = lean_box(0);
    v___x_3086_ = lean_apply_6(
        v_inst_3080_,
        v___f_3083_,
        lean_box(0),
        lean_box(0),
        v_it_3082_,
        v___x_3085_,
        v___f_3084_,
    );
    return v___x_3086_;
}
pub unsafe fn l_Std_Iter_Total_first_x3f___boxed(
    mut v_00_u03b1_3087_: *mut LeanObject,
    mut v_00_u03b2_3088_: *mut LeanObject,
    mut v_inst_3089_: *mut LeanObject,
    mut v_inst_3090_: *mut LeanObject,
    mut v_inst_3091_: *mut LeanObject,
    mut v_it_3092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3093_: *mut LeanObject = core::ptr::null_mut();
    v_res_3093_ = l_Std_Iter_Total_first_x3f(
        v_00_u03b1_3087_,
        v_00_u03b2_3088_,
        v_inst_3089_,
        v_inst_3090_,
        v_inst_3091_,
        v_it_3092_,
    );
    lean_dec(v_inst_3089_);
    return v_res_3093_;
}
pub unsafe fn l_Std_Iter_isEmpty___redArg___lam__1(
    mut v_x_3097_: *mut LeanObject,
    mut v_x_3098_: *mut LeanObject,
    mut v_x_3099_: u8,
) -> *mut LeanObject {
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    v___x_3100_ = l_Std_Iter_isEmpty___redArg___lam__1___closed__0;
    return v___x_3100_;
}
pub unsafe fn l_Std_Iter_isEmpty___redArg___lam__1___boxed(
    mut v_x_3101_: *mut LeanObject,
    mut v_x_3102_: *mut LeanObject,
    mut v_x_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_151__boxed_3104_: u8 = 0;
    let mut v_res_3105_: *mut LeanObject = core::ptr::null_mut();
    v_x_151__boxed_3104_ = (lean_unbox(v_x_3103_) as u8);
    v_res_3105_ = l_Std_Iter_isEmpty___redArg___lam__1(v_x_3101_, v_x_3102_, v_x_151__boxed_3104_);
    lean_dec(v_x_3101_);
    return v_res_3105_;
}
pub unsafe fn l_Std_Iter_isEmpty___redArg(
    mut v_inst_3107_: *mut LeanObject,
    mut v_it_3108_: *mut LeanObject,
) -> u8 {
    let mut v___f_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3111_: u8 = 0;
    let mut v___x_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: u8 = 0;
    v___f_3109_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3110_ = l_Std_Iter_isEmpty___redArg___closed__0;
    v___x_3111_ = 1;
    v___x_3112_ = lean_box((v___x_3111_) as usize);
    v___x_3113_ = lean_apply_6(
        v_inst_3107_,
        v___f_3109_,
        lean_box(0),
        lean_box(0),
        v_it_3108_,
        v___x_3112_,
        v___f_3110_,
    );
    v___x_3114_ = (lean_unbox(v___x_3113_) as u8);
    return v___x_3114_;
}
pub unsafe fn l_Std_Iter_isEmpty___redArg___boxed(
    mut v_inst_3115_: *mut LeanObject,
    mut v_it_3116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3117_: u8 = 0;
    let mut v_r_3118_: *mut LeanObject = core::ptr::null_mut();
    v_res_3117_ = l_Std_Iter_isEmpty___redArg(v_inst_3115_, v_it_3116_);
    v_r_3118_ = lean_box((v_res_3117_) as usize);
    return v_r_3118_;
}
pub unsafe fn l_Std_Iter_isEmpty(
    mut v_00_u03b1_3119_: *mut LeanObject,
    mut v_00_u03b2_3120_: *mut LeanObject,
    mut v_inst_3121_: *mut LeanObject,
    mut v_inst_3122_: *mut LeanObject,
    mut v_it_3123_: *mut LeanObject,
) -> u8 {
    let mut v___f_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3129_: u8 = 0;
    v___f_3124_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3125_ = l_Std_Iter_isEmpty___redArg___closed__0;
    v___x_3126_ = 1;
    v___x_3127_ = lean_box((v___x_3126_) as usize);
    v___x_3128_ = lean_apply_6(
        v_inst_3122_,
        v___f_3124_,
        lean_box(0),
        lean_box(0),
        v_it_3123_,
        v___x_3127_,
        v___f_3125_,
    );
    v___x_3129_ = (lean_unbox(v___x_3128_) as u8);
    return v___x_3129_;
}
pub unsafe fn l_Std_Iter_isEmpty___boxed(
    mut v_00_u03b1_3130_: *mut LeanObject,
    mut v_00_u03b2_3131_: *mut LeanObject,
    mut v_inst_3132_: *mut LeanObject,
    mut v_inst_3133_: *mut LeanObject,
    mut v_it_3134_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3135_: u8 = 0;
    let mut v_r_3136_: *mut LeanObject = core::ptr::null_mut();
    v_res_3135_ = l_Std_Iter_isEmpty(
        v_00_u03b1_3130_,
        v_00_u03b2_3131_,
        v_inst_3132_,
        v_inst_3133_,
        v_it_3134_,
    );
    lean_dec(v_inst_3132_);
    v_r_3136_ = lean_box((v_res_3135_) as usize);
    return v_r_3136_;
}
pub unsafe fn l_Std_Iter_Total_isEmpty___redArg(
    mut v_inst_3137_: *mut LeanObject,
    mut v_it_3138_: *mut LeanObject,
) -> u8 {
    let mut v___f_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3141_: u8 = 0;
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: u8 = 0;
    v___f_3139_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3140_ = l_Std_Iter_isEmpty___redArg___closed__0;
    v___x_3141_ = 1;
    v___x_3142_ = lean_box((v___x_3141_) as usize);
    v___x_3143_ = lean_apply_6(
        v_inst_3137_,
        v___f_3139_,
        lean_box(0),
        lean_box(0),
        v_it_3138_,
        v___x_3142_,
        v___f_3140_,
    );
    v___x_3144_ = (lean_unbox(v___x_3143_) as u8);
    return v___x_3144_;
}
pub unsafe fn l_Std_Iter_Total_isEmpty___redArg___boxed(
    mut v_inst_3145_: *mut LeanObject,
    mut v_it_3146_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3147_: u8 = 0;
    let mut v_r_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3147_ = l_Std_Iter_Total_isEmpty___redArg(v_inst_3145_, v_it_3146_);
    v_r_3148_ = lean_box((v_res_3147_) as usize);
    return v_r_3148_;
}
pub unsafe fn l_Std_Iter_Total_isEmpty(
    mut v_00_u03b1_3149_: *mut LeanObject,
    mut v_00_u03b2_3150_: *mut LeanObject,
    mut v_inst_3151_: *mut LeanObject,
    mut v_inst_3152_: *mut LeanObject,
    mut v_inst_3153_: *mut LeanObject,
    mut v_it_3154_: *mut LeanObject,
) -> u8 {
    let mut v___f_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: u8 = 0;
    let mut v___x_3158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: u8 = 0;
    v___f_3155_ = l_Std_Iter_first_x3f___redArg___closed__0;
    v___f_3156_ = l_Std_Iter_isEmpty___redArg___closed__0;
    v___x_3157_ = 1;
    v___x_3158_ = lean_box((v___x_3157_) as usize);
    v___x_3159_ = lean_apply_6(
        v_inst_3152_,
        v___f_3155_,
        lean_box(0),
        lean_box(0),
        v_it_3154_,
        v___x_3158_,
        v___f_3156_,
    );
    v___x_3160_ = (lean_unbox(v___x_3159_) as u8);
    return v___x_3160_;
}
pub unsafe fn l_Std_Iter_Total_isEmpty___boxed(
    mut v_00_u03b1_3161_: *mut LeanObject,
    mut v_00_u03b2_3162_: *mut LeanObject,
    mut v_inst_3163_: *mut LeanObject,
    mut v_inst_3164_: *mut LeanObject,
    mut v_inst_3165_: *mut LeanObject,
    mut v_it_3166_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3167_: u8 = 0;
    let mut v_r_3168_: *mut LeanObject = core::ptr::null_mut();
    v_res_3167_ = l_Std_Iter_Total_isEmpty(
        v_00_u03b1_3161_,
        v_00_u03b2_3162_,
        v_inst_3163_,
        v_inst_3164_,
        v_inst_3165_,
        v_it_3166_,
    );
    lean_dec(v_inst_3163_);
    v_r_3168_ = lean_box((v_res_3167_) as usize);
    return v_r_3168_;
}
pub unsafe fn l_Std_Iter_length___redArg___lam__0(
    mut v_x_3169_: *mut LeanObject,
    mut v_x_3170_: *mut LeanObject,
    mut v_f_3171_: *mut LeanObject,
    mut v_x_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    v___x_3173_ = lean_apply_1(v_f_3171_, v_x_3172_);
    return v___x_3173_;
}
pub unsafe fn l_Std_Iter_length___redArg___lam__1(
    mut v_x1_3174_: *mut LeanObject,
    mut v_x2_3175_: *mut LeanObject,
    mut v_x3_3176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    v___x_3177_ = lean_unsigned_to_nat(1);
    v___x_3178_ = lean_nat_add(v_x3_3176_, v___x_3177_);
    v___x_3179_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_3179_, 0, v___x_3178_);
    return v___x_3179_;
}
pub unsafe fn l_Std_Iter_length___redArg___lam__1___boxed(
    mut v_x1_3180_: *mut LeanObject,
    mut v_x2_3181_: *mut LeanObject,
    mut v_x3_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3183_: *mut LeanObject = core::ptr::null_mut();
    v_res_3183_ = l_Std_Iter_length___redArg___lam__1(v_x1_3180_, v_x2_3181_, v_x3_3182_);
    lean_dec(v_x3_3182_);
    lean_dec(v_x1_3180_);
    return v_res_3183_;
}
pub unsafe fn l_Std_Iter_length___redArg(
    mut v_inst_3186_: *mut LeanObject,
    mut v_it_3187_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    v___f_3188_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3189_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3190_ = lean_unsigned_to_nat(0);
    v___x_3191_ = lean_apply_6(
        v_inst_3186_,
        v___f_3188_,
        lean_box(0),
        lean_box(0),
        v_it_3187_,
        v___x_3190_,
        v___f_3189_,
    );
    return v___x_3191_;
}
pub unsafe fn l_Std_Iter_length(
    mut v_00_u03b1_3192_: *mut LeanObject,
    mut v_00_u03b2_3193_: *mut LeanObject,
    mut v_inst_3194_: *mut LeanObject,
    mut v_inst_3195_: *mut LeanObject,
    mut v_it_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    v___f_3197_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3198_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3199_ = lean_unsigned_to_nat(0);
    v___x_3200_ = lean_apply_6(
        v_inst_3195_,
        v___f_3197_,
        lean_box(0),
        lean_box(0),
        v_it_3196_,
        v___x_3199_,
        v___f_3198_,
    );
    return v___x_3200_;
}
pub unsafe fn l_Std_Iter_length___boxed(
    mut v_00_u03b1_3201_: *mut LeanObject,
    mut v_00_u03b2_3202_: *mut LeanObject,
    mut v_inst_3203_: *mut LeanObject,
    mut v_inst_3204_: *mut LeanObject,
    mut v_it_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3206_: *mut LeanObject = core::ptr::null_mut();
    v_res_3206_ = l_Std_Iter_length(
        v_00_u03b1_3201_,
        v_00_u03b2_3202_,
        v_inst_3203_,
        v_inst_3204_,
        v_it_3205_,
    );
    lean_dec(v_inst_3203_);
    return v_res_3206_;
}
pub unsafe fn l_Std_Iter_count___redArg(
    mut v_inst_3207_: *mut LeanObject,
    mut v_it_3208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    v___f_3209_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3210_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3211_ = lean_unsigned_to_nat(0);
    v___x_3212_ = lean_apply_6(
        v_inst_3207_,
        v___f_3209_,
        lean_box(0),
        lean_box(0),
        v_it_3208_,
        v___x_3211_,
        v___f_3210_,
    );
    return v___x_3212_;
}
pub unsafe fn l_Std_Iter_count(
    mut v_00_u03b1_3213_: *mut LeanObject,
    mut v_00_u03b2_3214_: *mut LeanObject,
    mut v_inst_3215_: *mut LeanObject,
    mut v_inst_3216_: *mut LeanObject,
    mut v_it_3217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    v___f_3218_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3219_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3220_ = lean_unsigned_to_nat(0);
    v___x_3221_ = lean_apply_6(
        v_inst_3216_,
        v___f_3218_,
        lean_box(0),
        lean_box(0),
        v_it_3217_,
        v___x_3220_,
        v___f_3219_,
    );
    return v___x_3221_;
}
pub unsafe fn l_Std_Iter_count___boxed(
    mut v_00_u03b1_3222_: *mut LeanObject,
    mut v_00_u03b2_3223_: *mut LeanObject,
    mut v_inst_3224_: *mut LeanObject,
    mut v_inst_3225_: *mut LeanObject,
    mut v_it_3226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3227_: *mut LeanObject = core::ptr::null_mut();
    v_res_3227_ = l_Std_Iter_count(
        v_00_u03b1_3222_,
        v_00_u03b2_3223_,
        v_inst_3224_,
        v_inst_3225_,
        v_it_3226_,
    );
    lean_dec(v_inst_3224_);
    return v_res_3227_;
}
pub unsafe fn l_Std_Iter_size___redArg(
    mut v_inst_3228_: *mut LeanObject,
    mut v_it_3229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    v___f_3230_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3231_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3232_ = lean_unsigned_to_nat(0);
    v___x_3233_ = lean_apply_6(
        v_inst_3228_,
        v___f_3230_,
        lean_box(0),
        lean_box(0),
        v_it_3229_,
        v___x_3232_,
        v___f_3231_,
    );
    return v___x_3233_;
}
pub unsafe fn l_Std_Iter_size(
    mut v_00_u03b1_3234_: *mut LeanObject,
    mut v_00_u03b2_3235_: *mut LeanObject,
    mut v_inst_3236_: *mut LeanObject,
    mut v_inst_3237_: *mut LeanObject,
    mut v_it_3238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    v___f_3239_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3240_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3241_ = lean_unsigned_to_nat(0);
    v___x_3242_ = lean_apply_6(
        v_inst_3237_,
        v___f_3239_,
        lean_box(0),
        lean_box(0),
        v_it_3238_,
        v___x_3241_,
        v___f_3240_,
    );
    return v___x_3242_;
}
pub unsafe fn l_Std_Iter_size___boxed(
    mut v_00_u03b1_3243_: *mut LeanObject,
    mut v_00_u03b2_3244_: *mut LeanObject,
    mut v_inst_3245_: *mut LeanObject,
    mut v_inst_3246_: *mut LeanObject,
    mut v_it_3247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3248_: *mut LeanObject = core::ptr::null_mut();
    v_res_3248_ = l_Std_Iter_size(
        v_00_u03b1_3243_,
        v_00_u03b2_3244_,
        v_inst_3245_,
        v_inst_3246_,
        v_it_3247_,
    );
    lean_dec(v_inst_3245_);
    return v_res_3248_;
}
pub unsafe fn l_Std_Iter_Partial_count___redArg(
    mut v_inst_3249_: *mut LeanObject,
    mut v_it_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    v___f_3251_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3252_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3253_ = lean_unsigned_to_nat(0);
    v___x_3254_ = lean_apply_6(
        v_inst_3249_,
        v___f_3251_,
        lean_box(0),
        lean_box(0),
        v_it_3250_,
        v___x_3253_,
        v___f_3252_,
    );
    return v___x_3254_;
}
pub unsafe fn l_Std_Iter_Partial_count(
    mut v_00_u03b1_3255_: *mut LeanObject,
    mut v_00_u03b2_3256_: *mut LeanObject,
    mut v_inst_3257_: *mut LeanObject,
    mut v_inst_3258_: *mut LeanObject,
    mut v_it_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    v___f_3260_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3261_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3262_ = lean_unsigned_to_nat(0);
    v___x_3263_ = lean_apply_6(
        v_inst_3258_,
        v___f_3260_,
        lean_box(0),
        lean_box(0),
        v_it_3259_,
        v___x_3262_,
        v___f_3261_,
    );
    return v___x_3263_;
}
pub unsafe fn l_Std_Iter_Partial_count___boxed(
    mut v_00_u03b1_3264_: *mut LeanObject,
    mut v_00_u03b2_3265_: *mut LeanObject,
    mut v_inst_3266_: *mut LeanObject,
    mut v_inst_3267_: *mut LeanObject,
    mut v_it_3268_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3269_: *mut LeanObject = core::ptr::null_mut();
    v_res_3269_ = l_Std_Iter_Partial_count(
        v_00_u03b1_3264_,
        v_00_u03b2_3265_,
        v_inst_3266_,
        v_inst_3267_,
        v_it_3268_,
    );
    lean_dec(v_inst_3266_);
    return v_res_3269_;
}
pub unsafe fn l_Std_Iter_Partial_size___redArg(
    mut v_inst_3270_: *mut LeanObject,
    mut v_it_3271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    v___f_3272_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3273_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3274_ = lean_unsigned_to_nat(0);
    v___x_3275_ = lean_apply_6(
        v_inst_3270_,
        v___f_3272_,
        lean_box(0),
        lean_box(0),
        v_it_3271_,
        v___x_3274_,
        v___f_3273_,
    );
    return v___x_3275_;
}
pub unsafe fn l_Std_Iter_Partial_size(
    mut v_00_u03b1_3276_: *mut LeanObject,
    mut v_00_u03b2_3277_: *mut LeanObject,
    mut v_inst_3278_: *mut LeanObject,
    mut v_inst_3279_: *mut LeanObject,
    mut v_it_3280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    v___f_3281_ = l_Std_Iter_length___redArg___closed__0;
    v___f_3282_ = l_Std_Iter_length___redArg___closed__1;
    v___x_3283_ = lean_unsigned_to_nat(0);
    v___x_3284_ = lean_apply_6(
        v_inst_3279_,
        v___f_3281_,
        lean_box(0),
        lean_box(0),
        v_it_3280_,
        v___x_3283_,
        v___f_3282_,
    );
    return v___x_3284_;
}
pub unsafe fn l_Std_Iter_Partial_size___boxed(
    mut v_00_u03b1_3285_: *mut LeanObject,
    mut v_00_u03b2_3286_: *mut LeanObject,
    mut v_inst_3287_: *mut LeanObject,
    mut v_inst_3288_: *mut LeanObject,
    mut v_it_3289_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3290_: *mut LeanObject = core::ptr::null_mut();
    v_res_3290_ = l_Std_Iter_Partial_size(
        v_00_u03b1_3285_,
        v_00_u03b2_3286_,
        v_inst_3287_,
        v_inst_3288_,
        v_it_3289_,
    );
    lean_dec(v_inst_3287_);
    return v_res_3290_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Iterators_Consumers_Loop(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Iterators_Consumers_Loop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Iterators_Consumers_Loop(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Partial(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Total(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Iterators_Consumers_Loop(builtin);
}

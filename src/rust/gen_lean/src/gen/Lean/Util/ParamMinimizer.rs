// Lean compiler output
// Module: Lean.Util.ParamMinimizer
// Imports: Init.While Init.Data.Range.Polymorphic
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push, lean_array_set,
    lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Control::Except::{
    l_ExceptT_bind, l_ExceptT_instMonad___redArg___lam__1, l_ExceptT_instMonad___redArg___lam__4,
    l_ExceptT_instMonad___redArg___lam__7, l_ExceptT_instMonad___redArg___lam__9, l_ExceptT_map,
    l_ExceptT_pure,
};
use crate::r#gen::Init::Control::State::{
    l_StateT_bind, l_StateT_instMonad___redArg___lam__1, l_StateT_instMonad___redArg___lam__4,
    l_StateT_instMonad___redArg___lam__7, l_StateT_instMonad___redArg___lam__9, l_StateT_map,
    l_StateT_pure,
};
use crate::r#gen::Init::Data::Range::Polymorphic::{
    initialize_Init_Data_Range_Polymorphic, runtime_initialize_Init_Data_Range_Polymorphic,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Prelude::l_ReaderT_instMonad___redArg;
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Init::While::{
    initialize_Init_While, l___private_Init_While_0__whileM_erased___redArg,
    runtime_initialize_Init_While,
};
pub static mut l_Lean_Util_ParamMinimizer_instInhabitedStatus_default: u8 = 0;
pub static mut l_Lean_Util_ParamMinimizer_instInhabitedStatus: u8 = 0;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105, 109,
        105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 109, 105, 115, 115, 105, 110, 103,
        0,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105, 109,
        105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 97, 112, 112, 114, 111, 120, 0,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105, 109,
        105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 112, 114, 101, 99, 105, 115, 101,
        0,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Util_ParamMinimizer_instReprStatus___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Util_ParamMinimizer_instReprStatus: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value:
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
static mut l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorIdx(
    mut v_x_1635_: u8,
) -> *mut leanh::LeanObject {
    match v_x_1635_ {
        0 => {
            let mut v___x_1636_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1636_ = leanh::lean_unsigned_to_nat(0);
            return v___x_1636_;
        }
        1 => {
            let mut v___x_1637_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1637_ = leanh::lean_unsigned_to_nat(1);
            return v___x_1637_;
        }
        _ => {
            let mut v___x_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1638_ = leanh::lean_unsigned_to_nat(2);
            return v___x_1638_;
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorIdx___boxed(
    mut v_x_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_1640_: u8 = 0;
    let mut v_res_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_1640_ = (leanh::lean_unbox(v_x_1639_) as u8);
    v_res_1641_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_boxed_1640_);
    return v_res_1641_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_toCtorIdx(
    mut v_x_1642_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_toCtorIdx___boxed(
    mut v_x_1644_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1645_ = (leanh::lean_unbox(v_x_1644_) as u8);
    v_res_1646_ = l_Lean_Util_ParamMinimizer_Status_toCtorIdx(v_x_4__boxed_1645_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(
    mut v_k_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1647_);
    return v_k_1647_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(
    mut v_k_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(v_k_1648_);
    leanh::lean_dec(v_k_1648_);
    return v_res_1649_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim(
    mut v_motive_1650_: *mut leanh::LeanObject,
    mut v_ctorIdx_1651_: *mut leanh::LeanObject,
    mut v_t_1652_: u8,
    mut v_h_1653_: *mut leanh::LeanObject,
    mut v_k_1654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_1654_);
    return v_k_1654_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(
    mut v_motive_1655_: *mut leanh::LeanObject,
    mut v_ctorIdx_1656_: *mut leanh::LeanObject,
    mut v_t_1657_: *mut leanh::LeanObject,
    mut v_h_1658_: *mut leanh::LeanObject,
    mut v_k_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1660_: u8 = 0;
    let mut v_res_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1660_ = (leanh::lean_unbox(v_t_1657_) as u8);
    v_res_1661_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(
        v_motive_1655_,
        v_ctorIdx_1656_,
        v_t_boxed_1660_,
        v_h_1658_,
        v_k_1659_,
    );
    leanh::lean_dec(v_k_1659_);
    leanh::lean_dec(v_ctorIdx_1656_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(
    mut v_missing_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_missing_1662_);
    return v_missing_1662_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(
    mut v_missing_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_1663_);
    leanh::lean_dec(v_missing_1663_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim(
    mut v_motive_1665_: *mut leanh::LeanObject,
    mut v_t_1666_: u8,
    mut v_h_1667_: *mut leanh::LeanObject,
    mut v_missing_1668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_missing_1668_);
    return v_missing_1668_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(
    mut v_motive_1669_: *mut leanh::LeanObject,
    mut v_t_1670_: *mut leanh::LeanObject,
    mut v_h_1671_: *mut leanh::LeanObject,
    mut v_missing_1672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1673_: u8 = 0;
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1673_ = (leanh::lean_unbox(v_t_1670_) as u8);
    v_res_1674_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(
        v_motive_1669_,
        v_t_boxed_1673_,
        v_h_1671_,
        v_missing_1672_,
    );
    leanh::lean_dec(v_missing_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(
    mut v_approx_1675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_approx_1675_);
    return v_approx_1675_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(
    mut v_approx_1676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_1676_);
    leanh::lean_dec(v_approx_1676_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim(
    mut v_motive_1678_: *mut leanh::LeanObject,
    mut v_t_1679_: u8,
    mut v_h_1680_: *mut leanh::LeanObject,
    mut v_approx_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_approx_1681_);
    return v_approx_1681_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(
    mut v_motive_1682_: *mut leanh::LeanObject,
    mut v_t_1683_: *mut leanh::LeanObject,
    mut v_h_1684_: *mut leanh::LeanObject,
    mut v_approx_1685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1686_: u8 = 0;
    let mut v_res_1687_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1686_ = (leanh::lean_unbox(v_t_1683_) as u8);
    v_res_1687_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(
        v_motive_1682_,
        v_t_boxed_1686_,
        v_h_1684_,
        v_approx_1685_,
    );
    leanh::lean_dec(v_approx_1685_);
    return v_res_1687_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(
    mut v_precise_1688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_precise_1688_);
    return v_precise_1688_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(
    mut v_precise_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_1689_);
    leanh::lean_dec(v_precise_1689_);
    return v_res_1690_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim(
    mut v_motive_1691_: *mut leanh::LeanObject,
    mut v_t_1692_: u8,
    mut v_h_1693_: *mut leanh::LeanObject,
    mut v_precise_1694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_precise_1694_);
    return v_precise_1694_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(
    mut v_motive_1695_: *mut leanh::LeanObject,
    mut v_t_1696_: *mut leanh::LeanObject,
    mut v_h_1697_: *mut leanh::LeanObject,
    mut v_precise_1698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_1699_: u8 = 0;
    let mut v_res_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_1699_ = (leanh::lean_unbox(v_t_1696_) as u8);
    v_res_1700_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(
        v_motive_1695_,
        v_t_boxed_1699_,
        v_h_1697_,
        v_precise_1698_,
    );
    leanh::lean_dec(v_precise_1698_);
    return v_res_1700_;
}
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default() -> u8 {
    let mut v___x_1701_: u8 = 0;
    v___x_1701_ = 0;
    return v___x_1701_;
}
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus() -> u8 {
    let mut v___x_1702_: u8 = 0;
    v___x_1702_ = 0;
    return v___x_1702_;
}
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1712_ = leanh::lean_unsigned_to_nat(2);
    v___x_1713_ = lean_nat_to_int(v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = leanh::lean_unsigned_to_nat(1);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_instReprStatus_repr(
    mut v_x_1716_: u8,
    mut v_prec_1717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1716_ {
                0 => {
                    v___x_1739_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_prec_1717_);
                    if v___x_1740_ == 0 {
                        v___x_1741_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6,
                        );
                        v___y_1719_ = v___x_1741_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1742_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7,
                        );
                        v___y_1719_ = v___x_1742_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_1743_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1744_ = lean_nat_dec_le(v___x_1743_, v_prec_1717_);
                    if v___x_1744_ == 0 {
                        v___x_1745_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6,
                        );
                        v___y_1726_ = v___x_1745_;
                        state = 2;
                        continue;
                    } else {
                        v___x_1746_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7,
                        );
                        v___y_1726_ = v___x_1746_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_1747_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_prec_1717_);
                    if v___x_1748_ == 0 {
                        v___x_1749_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6,
                        );
                        v___y_1733_ = v___x_1749_;
                        state = 3;
                        continue;
                    } else {
                        v___x_1750_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once
                            ),
                            _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7,
                        );
                        v___y_1733_ = v___x_1750_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_1720_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1;
                leanh::lean_inc(v___y_1719_);
                v___x_1721_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1721_, 0, v___y_1719_);
                leanh::lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                v___x_1722_ = 0;
                v___x_1723_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1723_, 0, v___x_1721_);
                leanh::lean_ctor_set_uint8(
                    v___x_1723_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1722_,
                );
                v___x_1724_ = l_Repr_addAppParen(v___x_1723_, v_prec_1717_);
                return v___x_1724_;
            }
            2 => {
                v___x_1727_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3;
                leanh::lean_inc(v___y_1726_);
                v___x_1728_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1728_, 0, v___y_1726_);
                leanh::lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                v___x_1729_ = 0;
                v___x_1730_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1730_, 0, v___x_1728_);
                leanh::lean_ctor_set_uint8(
                    v___x_1730_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1729_,
                );
                v___x_1731_ = l_Repr_addAppParen(v___x_1730_, v_prec_1717_);
                return v___x_1731_;
            }
            3 => {
                v___x_1734_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5;
                leanh::lean_inc(v___y_1733_);
                v___x_1735_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1735_, 0, v___y_1733_);
                leanh::lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                v___x_1736_ = 0;
                v___x_1737_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_1737_, 0, v___x_1735_);
                leanh::lean_ctor_set_uint8(
                    v___x_1737_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_1736_,
                );
                v___x_1738_ = l_Repr_addAppParen(v___x_1737_, v_prec_1717_);
                return v___x_1738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed(
    mut v_x_1751_: *mut leanh::LeanObject,
    mut v_prec_1752_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_1753_: u8 = 0;
    let mut v_res_1754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1753_ = (leanh::lean_unbox(v_x_1751_) as u8);
    v_res_1754_ =
        l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_177__boxed_1753_, v_prec_1752_);
    leanh::lean_dec(v_prec_1752_);
    return v_res_1754_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(
    mut v_toPure_1757_: *mut leanh::LeanObject,
    mut v_____x_1758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1759_ = leanh::lean_ctor_get(v_____x_1758_, 0);
                v_snd_1760_ = leanh::lean_ctor_get(v_____x_1758_, 1);
                v_isSharedCheck_1769_ = (!leanh::lean_is_exclusive(v_____x_1758_)) as u8;
                if v_isSharedCheck_1769_ == 0 {
                    v___x_1762_ = v_____x_1758_;
                    v_isShared_1763_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_1760_);
                    leanh::lean_inc(v_fst_1759_);
                    leanh::lean_dec(v_____x_1758_);
                    v___x_1762_ = leanh::lean_box(0);
                    v_isShared_1763_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1764_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1764_, 0, v_fst_1759_);
                if v_isShared_1763_ == 0 {
                    leanh::lean_ctor_set(v___x_1762_, 0, v___x_1764_);
                    v___x_1766_ = v___x_1762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1764_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1760_);
                    v___x_1766_ = v_reuseFailAlloc_1768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1767_ = leanh::lean_apply_2(
                    v_toPure_1757_,
                    leanh::lean_box(0),
                    v___x_1766_,
                );
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
    mut v_inst_1770_: *mut leanh::LeanObject,
    mut v_a_1771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v_toPure_1777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_1779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___f_1784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1772_ = leanh::lean_ctor_get(v_inst_1770_, 0);
                v_toBind_1773_ = leanh::lean_ctor_get(v_inst_1770_, 1);
                v_isSharedCheck_1796_ = (!leanh::lean_is_exclusive(v_inst_1770_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v___x_1775_ = v_inst_1770_;
                    v_isShared_1776_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1773_);
                    leanh::lean_inc(v_toApplicative_1772_);
                    leanh::lean_dec(v_inst_1770_);
                    v___x_1775_ = leanh::lean_box(0);
                    v_isShared_1776_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1777_ = leanh::lean_ctor_get(v_toApplicative_1772_, 1);
                leanh::lean_inc(v_toPure_1777_);
                leanh::lean_dec_ref(v_toApplicative_1772_);
                v_cur_1778_ = leanh::lean_ctor_get(v_a_1771_, 0);
                v_added_1779_ = leanh::lean_ctor_get(v_a_1771_, 1);
                v_numCalls_1780_ = leanh::lean_ctor_get(v_a_1771_, 2);
                v_isSharedCheck_1795_ = (!leanh::lean_is_exclusive(v_a_1771_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1782_ = v_a_1771_;
                    v_isShared_1783_ = v_isSharedCheck_1795_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_numCalls_1780_);
                    leanh::lean_inc(v_added_1779_);
                    leanh::lean_inc(v_cur_1778_);
                    leanh::lean_dec(v_a_1771_);
                    v___x_1782_ = leanh::lean_box(0);
                    v_isShared_1783_ = v_isSharedCheck_1795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toPure_1777_);
                v___f_1784_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1784_, 0, v_toPure_1777_);
                v___x_1785_ = leanh::lean_box(0);
                v___x_1786_ = 1;
                if v_isShared_1783_ == 0 {
                    v___x_1788_ = v___x_1782_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_cur_1778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_added_1779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_numCalls_1780_);
                    v___x_1788_ = v_reuseFailAlloc_1794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                leanh::lean_ctor_set_uint8(
                    v___x_1788_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_1786_,
                );
                if v_isShared_1776_ == 0 {
                    leanh::lean_ctor_set(v___x_1775_, 1, v___x_1788_);
                    leanh::lean_ctor_set(v___x_1775_, 0, v___x_1785_);
                    v___x_1790_ = v___x_1775_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1785_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1788_);
                    v___x_1790_ = v_reuseFailAlloc_1793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1791_ = leanh::lean_apply_2(
                    v_toPure_1777_,
                    leanh::lean_box(0),
                    v___x_1790_,
                );
                v___x_1792_ = leanh::lean_apply_4(
                    v_toBind_1773_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1791_,
                    v___f_1784_,
                );
                return v___x_1792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(
    mut v_m_1797_: *mut leanh::LeanObject,
    mut v_inst_1798_: *mut leanh::LeanObject,
    mut v_a_1799_: *mut leanh::LeanObject,
    mut v_a_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
            v_inst_1798_,
            v_a_1800_,
        );
    return v___x_1801_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(
    mut v_m_1802_: *mut leanh::LeanObject,
    mut v_inst_1803_: *mut leanh::LeanObject,
    mut v_a_1804_: *mut leanh::LeanObject,
    mut v_a_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1806_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(
        v_m_1802_,
        v_inst_1803_,
        v_a_1804_,
        v_a_1805_,
    );
    leanh::lean_dec_ref(v_a_1804_);
    return v_res_1806_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(
    mut v_inst_1807_: *mut leanh::LeanObject,
    mut v_a_1808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v_toPure_1814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1818_: u8 = 0;
    let mut v___x_1820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___f_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1809_ = leanh::lean_ctor_get(v_inst_1807_, 0);
                v_toBind_1810_ = leanh::lean_ctor_get(v_inst_1807_, 1);
                v_isSharedCheck_1835_ = (!leanh::lean_is_exclusive(v_inst_1807_)) as u8;
                if v_isSharedCheck_1835_ == 0 {
                    v___x_1812_ = v_inst_1807_;
                    v_isShared_1813_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1810_);
                    leanh::lean_inc(v_toApplicative_1809_);
                    leanh::lean_dec(v_inst_1807_);
                    v___x_1812_ = leanh::lean_box(0);
                    v_isShared_1813_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1814_ = leanh::lean_ctor_get(v_toApplicative_1809_, 1);
                leanh::lean_inc(v_toPure_1814_);
                leanh::lean_dec_ref(v_toApplicative_1809_);
                v_cur_1815_ = leanh::lean_ctor_get(v_a_1808_, 0);
                v_added_1816_ = leanh::lean_ctor_get(v_a_1808_, 1);
                v_numCalls_1817_ = leanh::lean_ctor_get(v_a_1808_, 2);
                v_found_1818_ = leanh::lean_ctor_get_uint8(
                    v_a_1808_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1834_ = (!leanh::lean_is_exclusive(v_a_1808_)) as u8;
                if v_isSharedCheck_1834_ == 0 {
                    v___x_1820_ = v_a_1808_;
                    v_isShared_1821_ = v_isSharedCheck_1834_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_numCalls_1817_);
                    leanh::lean_inc(v_added_1816_);
                    leanh::lean_inc(v_cur_1815_);
                    leanh::lean_dec(v_a_1808_);
                    v___x_1820_ = leanh::lean_box(0);
                    v_isShared_1821_ = v_isSharedCheck_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toPure_1814_);
                v___f_1822_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1822_, 0, v_toPure_1814_);
                v___x_1823_ = leanh::lean_box(0);
                v___x_1824_ = leanh::lean_unsigned_to_nat(1);
                v___x_1825_ = lean_nat_add(v_numCalls_1817_, v___x_1824_);
                leanh::lean_dec(v_numCalls_1817_);
                if v_isShared_1821_ == 0 {
                    leanh::lean_ctor_set(v___x_1820_, 2, v___x_1825_);
                    v___x_1827_ = v___x_1820_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_cur_1815_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_added_1816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1833_, 2, v___x_1825_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1833_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_found_1818_,
                    );
                    v___x_1827_ = v_reuseFailAlloc_1833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1813_ == 0 {
                    leanh::lean_ctor_set(v___x_1812_, 1, v___x_1827_);
                    leanh::lean_ctor_set(v___x_1812_, 0, v___x_1823_);
                    v___x_1829_ = v___x_1812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1823_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1827_);
                    v___x_1829_ = v_reuseFailAlloc_1832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1830_ = leanh::lean_apply_2(
                    v_toPure_1814_,
                    leanh::lean_box(0),
                    v___x_1829_,
                );
                v___x_1831_ = leanh::lean_apply_4(
                    v_toBind_1810_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1830_,
                    v___f_1822_,
                );
                return v___x_1831_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(
    mut v_m_1836_: *mut leanh::LeanObject,
    mut v_inst_1837_: *mut leanh::LeanObject,
    mut v_a_1838_: *mut leanh::LeanObject,
    mut v_a_1839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1840_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(
            v_inst_1837_,
            v_a_1839_,
        );
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(
    mut v_m_1841_: *mut leanh::LeanObject,
    mut v_inst_1842_: *mut leanh::LeanObject,
    mut v_a_1843_: *mut leanh::LeanObject,
    mut v_a_1844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1845_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1845_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(
        v_m_1841_,
        v_inst_1842_,
        v_a_1843_,
        v_a_1844_,
    );
    leanh::lean_dec_ref(v_a_1843_);
    return v_res_1845_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(
    mut v_i_1846_: *mut leanh::LeanObject,
    mut v_inst_1847_: *mut leanh::LeanObject,
    mut v_a_1848_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v_toPure_1854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_1856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1858_: u8 = 0;
    let mut v___x_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1861_: u8 = 0;
    let mut v___f_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1849_ = leanh::lean_ctor_get(v_inst_1847_, 0);
                v_toBind_1850_ = leanh::lean_ctor_get(v_inst_1847_, 1);
                v_isSharedCheck_1877_ = (!leanh::lean_is_exclusive(v_inst_1847_)) as u8;
                if v_isSharedCheck_1877_ == 0 {
                    v___x_1852_ = v_inst_1847_;
                    v_isShared_1853_ = v_isSharedCheck_1877_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1850_);
                    leanh::lean_inc(v_toApplicative_1849_);
                    leanh::lean_dec(v_inst_1847_);
                    v___x_1852_ = leanh::lean_box(0);
                    v_isShared_1853_ = v_isSharedCheck_1877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1854_ = leanh::lean_ctor_get(v_toApplicative_1849_, 1);
                leanh::lean_inc(v_toPure_1854_);
                leanh::lean_dec_ref(v_toApplicative_1849_);
                v_cur_1855_ = leanh::lean_ctor_get(v_a_1848_, 0);
                v_added_1856_ = leanh::lean_ctor_get(v_a_1848_, 1);
                v_numCalls_1857_ = leanh::lean_ctor_get(v_a_1848_, 2);
                v_found_1858_ = leanh::lean_ctor_get_uint8(
                    v_a_1848_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1876_ = (!leanh::lean_is_exclusive(v_a_1848_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v___x_1860_ = v_a_1848_;
                    v_isShared_1861_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_numCalls_1857_);
                    leanh::lean_inc(v_added_1856_);
                    leanh::lean_inc(v_cur_1855_);
                    leanh::lean_dec(v_a_1848_);
                    v___x_1860_ = leanh::lean_box(0);
                    v_isShared_1861_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toPure_1854_);
                v___f_1862_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1862_, 0, v_toPure_1854_);
                v___x_1863_ = leanh::lean_box(0);
                v___x_1864_ = 1;
                v___x_1865_ = leanh::lean_box((v___x_1864_) as usize);
                v___x_1866_ = lean_array_set(v_cur_1855_, v_i_1846_, v___x_1865_);
                v___x_1867_ = lean_array_push(v_added_1856_, v_i_1846_);
                if v_isShared_1861_ == 0 {
                    leanh::lean_ctor_set(v___x_1860_, 1, v___x_1867_);
                    leanh::lean_ctor_set(v___x_1860_, 0, v___x_1866_);
                    v___x_1869_ = v___x_1860_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1867_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_numCalls_1857_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1875_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_found_1858_,
                    );
                    v___x_1869_ = v_reuseFailAlloc_1875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1853_ == 0 {
                    leanh::lean_ctor_set(v___x_1852_, 1, v___x_1869_);
                    leanh::lean_ctor_set(v___x_1852_, 0, v___x_1863_);
                    v___x_1871_ = v___x_1852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1863_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1874_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1872_ = leanh::lean_apply_2(
                    v_toPure_1854_,
                    leanh::lean_box(0),
                    v___x_1871_,
                );
                v___x_1873_ = leanh::lean_apply_4(
                    v_toBind_1850_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1872_,
                    v___f_1862_,
                );
                return v___x_1873_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(
    mut v_m_1878_: *mut leanh::LeanObject,
    mut v_i_1879_: *mut leanh::LeanObject,
    mut v_inst_1880_: *mut leanh::LeanObject,
    mut v_a_1881_: *mut leanh::LeanObject,
    mut v_a_1882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1883_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(
        v_i_1879_,
        v_inst_1880_,
        v_a_1882_,
    );
    return v___x_1883_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(
    mut v_m_1884_: *mut leanh::LeanObject,
    mut v_i_1885_: *mut leanh::LeanObject,
    mut v_inst_1886_: *mut leanh::LeanObject,
    mut v_a_1887_: *mut leanh::LeanObject,
    mut v_a_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1889_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(
        v_m_1884_,
        v_i_1885_,
        v_inst_1886_,
        v_a_1887_,
        v_a_1888_,
    );
    leanh::lean_dec_ref(v_a_1887_);
    return v_res_1889_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
    mut v_i_1890_: *mut leanh::LeanObject,
    mut v_inst_1891_: *mut leanh::LeanObject,
    mut v_a_1892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v_toPure_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_1900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1902_: u8 = 0;
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___f_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1893_ = leanh::lean_ctor_get(v_inst_1891_, 0);
                v_toBind_1894_ = leanh::lean_ctor_get(v_inst_1891_, 1);
                v_isSharedCheck_1920_ = (!leanh::lean_is_exclusive(v_inst_1891_)) as u8;
                if v_isSharedCheck_1920_ == 0 {
                    v___x_1896_ = v_inst_1891_;
                    v_isShared_1897_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1894_);
                    leanh::lean_inc(v_toApplicative_1893_);
                    leanh::lean_dec(v_inst_1891_);
                    v___x_1896_ = leanh::lean_box(0);
                    v_isShared_1897_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1898_ = leanh::lean_ctor_get(v_toApplicative_1893_, 1);
                leanh::lean_inc(v_toPure_1898_);
                leanh::lean_dec_ref(v_toApplicative_1893_);
                v_cur_1899_ = leanh::lean_ctor_get(v_a_1892_, 0);
                v_added_1900_ = leanh::lean_ctor_get(v_a_1892_, 1);
                v_numCalls_1901_ = leanh::lean_ctor_get(v_a_1892_, 2);
                v_found_1902_ = leanh::lean_ctor_get_uint8(
                    v_a_1892_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1919_ = (!leanh::lean_is_exclusive(v_a_1892_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1904_ = v_a_1892_;
                    v_isShared_1905_ = v_isSharedCheck_1919_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_numCalls_1901_);
                    leanh::lean_inc(v_added_1900_);
                    leanh::lean_inc(v_cur_1899_);
                    leanh::lean_dec(v_a_1892_);
                    v___x_1904_ = leanh::lean_box(0);
                    v_isShared_1905_ = v_isSharedCheck_1919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toPure_1898_);
                v___f_1906_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1906_, 0, v_toPure_1898_);
                v___x_1907_ = leanh::lean_box(0);
                v___x_1908_ = 0;
                v___x_1909_ = leanh::lean_box((v___x_1908_) as usize);
                v___x_1910_ = lean_array_set(v_cur_1899_, v_i_1890_, v___x_1909_);
                if v_isShared_1905_ == 0 {
                    leanh::lean_ctor_set(v___x_1904_, 0, v___x_1910_);
                    v___x_1912_ = v___x_1904_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1910_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_added_1900_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_numCalls_1901_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1918_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_found_1902_,
                    );
                    v___x_1912_ = v_reuseFailAlloc_1918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1897_ == 0 {
                    leanh::lean_ctor_set(v___x_1896_, 1, v___x_1912_);
                    leanh::lean_ctor_set(v___x_1896_, 0, v___x_1907_);
                    v___x_1914_ = v___x_1896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1907_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1912_);
                    v___x_1914_ = v_reuseFailAlloc_1917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1915_ = leanh::lean_apply_2(
                    v_toPure_1898_,
                    leanh::lean_box(0),
                    v___x_1914_,
                );
                v___x_1916_ = leanh::lean_apply_4(
                    v_toBind_1894_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1915_,
                    v___f_1906_,
                );
                return v___x_1916_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg___boxed(
    mut v_i_1921_: *mut leanh::LeanObject,
    mut v_inst_1922_: *mut leanh::LeanObject,
    mut v_a_1923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1924_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
        v_i_1921_,
        v_inst_1922_,
        v_a_1923_,
    );
    leanh::lean_dec(v_i_1921_);
    return v_res_1924_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(
    mut v_m_1925_: *mut leanh::LeanObject,
    mut v_i_1926_: *mut leanh::LeanObject,
    mut v_inst_1927_: *mut leanh::LeanObject,
    mut v_a_1928_: *mut leanh::LeanObject,
    mut v_a_1929_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1930_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
        v_i_1926_,
        v_inst_1927_,
        v_a_1929_,
    );
    return v___x_1930_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(
    mut v_m_1931_: *mut leanh::LeanObject,
    mut v_i_1932_: *mut leanh::LeanObject,
    mut v_inst_1933_: *mut leanh::LeanObject,
    mut v_a_1934_: *mut leanh::LeanObject,
    mut v_a_1935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1936_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(
        v_m_1931_,
        v_i_1932_,
        v_inst_1933_,
        v_a_1934_,
        v_a_1935_,
    );
    leanh::lean_dec_ref(v_a_1934_);
    leanh::lean_dec(v_i_1932_);
    return v_res_1936_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
    mut v_i_1937_: *mut leanh::LeanObject,
    mut v_inst_1938_: *mut leanh::LeanObject,
    mut v_a_1939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v_toPure_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_1947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_1949_: u8 = 0;
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___f_1953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1940_ = leanh::lean_ctor_get(v_inst_1938_, 0);
                v_toBind_1941_ = leanh::lean_ctor_get(v_inst_1938_, 1);
                v_isSharedCheck_1967_ = (!leanh::lean_is_exclusive(v_inst_1938_)) as u8;
                if v_isSharedCheck_1967_ == 0 {
                    v___x_1943_ = v_inst_1938_;
                    v_isShared_1944_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_toBind_1941_);
                    leanh::lean_inc(v_toApplicative_1940_);
                    leanh::lean_dec(v_inst_1938_);
                    v___x_1943_ = leanh::lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1945_ = leanh::lean_ctor_get(v_toApplicative_1940_, 1);
                leanh::lean_inc(v_toPure_1945_);
                leanh::lean_dec_ref(v_toApplicative_1940_);
                v_cur_1946_ = leanh::lean_ctor_get(v_a_1939_, 0);
                v_added_1947_ = leanh::lean_ctor_get(v_a_1939_, 1);
                v_numCalls_1948_ = leanh::lean_ctor_get(v_a_1939_, 2);
                v_found_1949_ = leanh::lean_ctor_get_uint8(
                    v_a_1939_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1966_ = (!leanh::lean_is_exclusive(v_a_1939_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v___x_1951_ = v_a_1939_;
                    v_isShared_1952_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_numCalls_1948_);
                    leanh::lean_inc(v_added_1947_);
                    leanh::lean_inc(v_cur_1946_);
                    leanh::lean_dec(v_a_1939_);
                    v___x_1951_ = leanh::lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v_toPure_1945_);
                v___f_1953_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_1953_, 0, v_toPure_1945_);
                v___x_1954_ = leanh::lean_box(0);
                v___x_1955_ = 1;
                v___x_1956_ = leanh::lean_box((v___x_1955_) as usize);
                v___x_1957_ = lean_array_set(v_cur_1946_, v_i_1937_, v___x_1956_);
                if v_isShared_1952_ == 0 {
                    leanh::lean_ctor_set(v___x_1951_, 0, v___x_1957_);
                    v___x_1959_ = v___x_1951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1957_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_added_1947_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_numCalls_1948_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1965_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_found_1949_,
                    );
                    v___x_1959_ = v_reuseFailAlloc_1965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1944_ == 0 {
                    leanh::lean_ctor_set(v___x_1943_, 1, v___x_1959_);
                    leanh::lean_ctor_set(v___x_1943_, 0, v___x_1954_);
                    v___x_1961_ = v___x_1943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1954_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1959_);
                    v___x_1961_ = v_reuseFailAlloc_1964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1962_ = leanh::lean_apply_2(
                    v_toPure_1945_,
                    leanh::lean_box(0),
                    v___x_1961_,
                );
                v___x_1963_ = leanh::lean_apply_4(
                    v_toBind_1941_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_1962_,
                    v___f_1953_,
                );
                return v___x_1963_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg___boxed(
    mut v_i_1968_: *mut leanh::LeanObject,
    mut v_inst_1969_: *mut leanh::LeanObject,
    mut v_a_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1971_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
        v_i_1968_,
        v_inst_1969_,
        v_a_1970_,
    );
    leanh::lean_dec(v_i_1968_);
    return v_res_1971_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(
    mut v_m_1972_: *mut leanh::LeanObject,
    mut v_i_1973_: *mut leanh::LeanObject,
    mut v_inst_1974_: *mut leanh::LeanObject,
    mut v_a_1975_: *mut leanh::LeanObject,
    mut v_a_1976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
        v_i_1973_,
        v_inst_1974_,
        v_a_1976_,
    );
    return v___x_1977_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(
    mut v_m_1978_: *mut leanh::LeanObject,
    mut v_i_1979_: *mut leanh::LeanObject,
    mut v_inst_1980_: *mut leanh::LeanObject,
    mut v_a_1981_: *mut leanh::LeanObject,
    mut v_a_1982_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1983_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(
        v_m_1978_,
        v_i_1979_,
        v_inst_1980_,
        v_a_1981_,
        v_a_1982_,
    );
    leanh::lean_dec_ref(v_a_1981_);
    leanh::lean_dec(v_i_1979_);
    return v_res_1983_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(
    mut v_toPure_1984_: *mut leanh::LeanObject,
    mut v___x_1985_: u8,
    mut v_____x_1986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_1987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_a_1992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_unused_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_unused_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1987_ = leanh::lean_ctor_get(v_____x_1986_, 0);
                leanh::lean_inc(v_fst_1987_);
                if leanh::lean_obj_tag(v_fst_1987_) == 0 {
                    v_snd_1988_ = leanh::lean_ctor_get(v_____x_1986_, 1);
                    v_isSharedCheck_2004_ = (!leanh::lean_is_exclusive(v_____x_1986_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v_unused_2005_ = leanh::lean_ctor_get(v_____x_1986_, 0);
                        leanh::lean_dec(v_unused_2005_);
                        v___x_1990_ = v_____x_1986_;
                        v_isShared_1991_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1988_);
                        leanh::lean_dec(v_____x_1986_);
                        v___x_1990_ = leanh::lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2006_ = leanh::lean_ctor_get(v_____x_1986_, 1);
                    v_isSharedCheck_2023_ = (!leanh::lean_is_exclusive(v_____x_1986_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v_unused_2024_ = leanh::lean_ctor_get(v_____x_1986_, 0);
                        leanh::lean_dec(v_unused_2024_);
                        v___x_2008_ = v_____x_1986_;
                        v_isShared_2009_ = v_isSharedCheck_2023_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2006_);
                        leanh::lean_dec(v_____x_1986_);
                        v___x_2008_ = leanh::lean_box(0);
                        v_isShared_2009_ = v_isSharedCheck_2023_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1992_ = leanh::lean_ctor_get(v_fst_1987_, 0);
                v_isSharedCheck_2003_ = (!leanh::lean_is_exclusive(v_fst_1987_)) as u8;
                if v_isSharedCheck_2003_ == 0 {
                    v___x_1994_ = v_fst_1987_;
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1992_);
                    leanh::lean_dec(v_fst_1987_);
                    v___x_1994_ = leanh::lean_box(0);
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_1995_ == 0 {
                    v___x_1997_ = v___x_1994_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_2002_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1991_ == 0 {
                    leanh::lean_ctor_set(v___x_1990_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1990_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_snd_1988_);
                    v___x_1999_ = v_reuseFailAlloc_2001_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2000_ = leanh::lean_apply_2(
                    v_toPure_1984_,
                    leanh::lean_box(0),
                    v___x_1999_,
                );
                return v___x_2000_;
            }
            5 => {
                v_isSharedCheck_2021_ = (!leanh::lean_is_exclusive(v_fst_1987_)) as u8;
                if v_isSharedCheck_2021_ == 0 {
                    v_unused_2022_ = leanh::lean_ctor_get(v_fst_1987_, 0);
                    leanh::lean_dec(v_unused_2022_);
                    v___x_2011_ = v_fst_1987_;
                    v_isShared_2012_ = v_isSharedCheck_2021_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_1987_);
                    v___x_2011_ = leanh::lean_box(0);
                    v_isShared_2012_ = v_isSharedCheck_2021_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2013_ = leanh::lean_box((v___x_1985_) as usize);
                if v_isShared_2012_ == 0 {
                    leanh::lean_ctor_set(v___x_2011_, 0, v___x_2013_);
                    v___x_2015_ = v___x_2011_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2020_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2013_);
                    v___x_2015_ = v_reuseFailAlloc_2020_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2009_ == 0 {
                    leanh::lean_ctor_set(v___x_2008_, 0, v___x_2015_);
                    v___x_2017_ = v___x_2008_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2015_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_snd_2006_);
                    v___x_2017_ = v_reuseFailAlloc_2019_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2018_ = leanh::lean_apply_2(
                    v_toPure_1984_,
                    leanh::lean_box(0),
                    v___x_2017_,
                );
                return v___x_2018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(
    mut v_toPure_2025_: *mut leanh::LeanObject,
    mut v___x_2026_: *mut leanh::LeanObject,
    mut v_____x_2027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7305__boxed_2028_: u8 = 0;
    let mut v_res_2029_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7305__boxed_2028_ = (leanh::lean_unbox(v___x_2026_) as u8);
    v_res_2029_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(
            v_toPure_2025_,
            v___x_7305__boxed_2028_,
            v_____x_2027_,
        );
    return v_res_2029_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(
    mut v_toPure_2030_: *mut leanh::LeanObject,
    mut v_inst_2031_: *mut leanh::LeanObject,
    mut v_toBind_2032_: *mut leanh::LeanObject,
    mut v___f_2033_: *mut leanh::LeanObject,
    mut v_____x_2034_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2035_ = leanh::lean_ctor_get(v_____x_2034_, 0);
    if leanh::lean_obj_tag(v_fst_2035_) == 0 {
        let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_2033_);
        leanh::lean_dec(v_toBind_2032_);
        leanh::lean_dec_ref(v_inst_2031_);
        v___x_2036_ =
            leanh::lean_apply_2(v_toPure_2030_, leanh::lean_box(0), v_____x_2034_);
        return v___x_2036_;
    } else {
        let mut v_a_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: u8 = 0;
        v_a_2037_ = leanh::lean_ctor_get(v_fst_2035_, 0);
        v___x_2038_ = (leanh::lean_unbox(v_a_2037_) as u8);
        if v___x_2038_ == 0 {
            let mut v___x_2039_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___f_2033_);
            leanh::lean_dec(v_toBind_2032_);
            leanh::lean_dec_ref(v_inst_2031_);
            v___x_2039_ = leanh::lean_apply_2(
                v_toPure_2030_,
                leanh::lean_box(0),
                v_____x_2034_,
            );
            return v___x_2039_;
        } else {
            let mut v_snd_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_2030_);
            v_snd_2040_ = leanh::lean_ctor_get(v_____x_2034_, 1);
            leanh::lean_inc(v_snd_2040_);
            leanh::lean_dec_ref(v_____x_2034_);
            v___x_2041_ =
                l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
                    v_inst_2031_,
                    v_snd_2040_,
                );
            v___x_2042_ = leanh::lean_apply_4(
                v_toBind_2032_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_2041_,
                v___f_2033_,
            );
            return v___x_2042_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(
    mut v_toPure_2043_: *mut leanh::LeanObject,
    mut v_____x_2044_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2045_ = leanh::lean_ctor_get(v_____x_2044_, 0);
                v_snd_2046_ = leanh::lean_ctor_get(v_____x_2044_, 1);
                v_isSharedCheck_2055_ = (!leanh::lean_is_exclusive(v_____x_2044_)) as u8;
                if v_isSharedCheck_2055_ == 0 {
                    v___x_2048_ = v_____x_2044_;
                    v_isShared_2049_ = v_isSharedCheck_2055_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2046_);
                    leanh::lean_inc(v_fst_2045_);
                    leanh::lean_dec(v_____x_2044_);
                    v___x_2048_ = leanh::lean_box(0);
                    v_isShared_2049_ = v_isSharedCheck_2055_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2050_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2050_, 0, v_fst_2045_);
                if v_isShared_2049_ == 0 {
                    leanh::lean_ctor_set(v___x_2048_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2050_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_snd_2046_);
                    v___x_2052_ = v_reuseFailAlloc_2054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2053_ = leanh::lean_apply_2(
                    v_toPure_2043_,
                    leanh::lean_box(0),
                    v___x_2052_,
                );
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(
    mut v_snd_2056_: *mut leanh::LeanObject,
    mut v_toPure_2057_: *mut leanh::LeanObject,
    mut v_a_2058_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2059_ = leanh::lean_box((v_a_2058_) as usize);
    v___x_2060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    leanh::lean_ctor_set(v___x_2060_, 1, v_snd_2056_);
    v___x_2061_ =
        leanh::lean_apply_2(v_toPure_2057_, leanh::lean_box(0), v___x_2060_);
    return v___x_2061_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(
    mut v_snd_2062_: *mut leanh::LeanObject,
    mut v_toPure_2063_: *mut leanh::LeanObject,
    mut v_a_2064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_2065_: u8 = 0;
    let mut v_res_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_2065_ = (leanh::lean_unbox(v_a_2064_) as u8);
    v_res_2066_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(
            v_snd_2062_,
            v_toPure_2063_,
            v_a_boxed_2065_,
        );
    return v_res_2066_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(
    mut v_toPure_2067_: *mut leanh::LeanObject,
    mut v_a_2068_: *mut leanh::LeanObject,
    mut v_toBind_2069_: *mut leanh::LeanObject,
    mut v___f_2070_: *mut leanh::LeanObject,
    mut v_____x_2071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v_a_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_test_2093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2072_ = leanh::lean_ctor_get(v_____x_2071_, 0);
                leanh::lean_inc(v_fst_2072_);
                if leanh::lean_obj_tag(v_fst_2072_) == 0 {
                    leanh::lean_dec(v___f_2070_);
                    leanh::lean_dec(v_toBind_2069_);
                    leanh::lean_dec_ref(v_a_2068_);
                    v_snd_2073_ = leanh::lean_ctor_get(v_____x_2071_, 1);
                    v_isSharedCheck_2089_ = (!leanh::lean_is_exclusive(v_____x_2071_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v_unused_2090_ = leanh::lean_ctor_get(v_____x_2071_, 0);
                        leanh::lean_dec(v_unused_2090_);
                        v___x_2075_ = v_____x_2071_;
                        v_isShared_2076_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2073_);
                        leanh::lean_dec(v_____x_2071_);
                        v___x_2075_ = leanh::lean_box(0);
                        v_isShared_2076_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2091_ = leanh::lean_ctor_get(v_fst_2072_, 0);
                    leanh::lean_inc(v_a_2091_);
                    leanh::lean_dec_ref_known(v_fst_2072_, 1);
                    v_snd_2092_ = leanh::lean_ctor_get(v_____x_2071_, 1);
                    leanh::lean_inc(v_snd_2092_);
                    leanh::lean_dec_ref(v_____x_2071_);
                    v_test_2093_ = leanh::lean_ctor_get(v_a_2068_, 1);
                    leanh::lean_inc(v_test_2093_);
                    leanh::lean_dec_ref(v_a_2068_);
                    v_cur_2094_ = leanh::lean_ctor_get(v_a_2091_, 0);
                    leanh::lean_inc_ref(v_cur_2094_);
                    leanh::lean_dec(v_a_2091_);
                    v___x_2095_ = leanh::lean_apply_1(v_test_2093_, v_cur_2094_);
                    leanh::lean_inc(v_toPure_2067_);
                    v___f_2096_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                    leanh::lean_closure_set(v___f_2096_, 0, v_toPure_2067_);
                    v___f_2097_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2097_, 0, v_snd_2092_);
                    leanh::lean_closure_set(v___f_2097_, 1, v_toPure_2067_);
                    leanh::lean_inc_n(v_toBind_2069_, 2);
                    v___x_2098_ = leanh::lean_apply_4(
                        v_toBind_2069_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2095_,
                        v___f_2097_,
                    );
                    v___x_2099_ = leanh::lean_apply_4(
                        v_toBind_2069_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2098_,
                        v___f_2096_,
                    );
                    v___x_2100_ = leanh::lean_apply_4(
                        v_toBind_2069_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2099_,
                        v___f_2070_,
                    );
                    return v___x_2100_;
                }
            }
            1 => {
                v_a_2077_ = leanh::lean_ctor_get(v_fst_2072_, 0);
                v_isSharedCheck_2088_ = (!leanh::lean_is_exclusive(v_fst_2072_)) as u8;
                if v_isSharedCheck_2088_ == 0 {
                    v___x_2079_ = v_fst_2072_;
                    v_isShared_2080_ = v_isSharedCheck_2088_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2077_);
                    leanh::lean_dec(v_fst_2072_);
                    v___x_2079_ = leanh::lean_box(0);
                    v_isShared_2080_ = v_isSharedCheck_2088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2080_ == 0 {
                    v___x_2082_ = v___x_2079_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2087_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2087_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2076_ == 0 {
                    leanh::lean_ctor_set(v___x_2075_, 0, v___x_2082_);
                    v___x_2084_ = v___x_2075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_snd_2073_);
                    v___x_2084_ = v_reuseFailAlloc_2086_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2085_ = leanh::lean_apply_2(
                    v_toPure_2067_,
                    leanh::lean_box(0),
                    v___x_2084_,
                );
                return v___x_2085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(
    mut v_toPure_2101_: *mut leanh::LeanObject,
    mut v_____x_2102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2103_ = leanh::lean_ctor_get(v_____x_2102_, 0);
                v_snd_2104_ = leanh::lean_ctor_get(v_____x_2102_, 1);
                v_isSharedCheck_2113_ = (!leanh::lean_is_exclusive(v_____x_2102_)) as u8;
                if v_isSharedCheck_2113_ == 0 {
                    v___x_2106_ = v_____x_2102_;
                    v_isShared_2107_ = v_isSharedCheck_2113_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2104_);
                    leanh::lean_inc(v_fst_2103_);
                    leanh::lean_dec(v_____x_2102_);
                    v___x_2106_ = leanh::lean_box(0);
                    v_isShared_2107_ = v_isSharedCheck_2113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2108_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2108_, 0, v_fst_2103_);
                if v_isShared_2107_ == 0 {
                    leanh::lean_ctor_set(v___x_2106_, 0, v___x_2108_);
                    v___x_2110_ = v___x_2106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2108_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_snd_2104_);
                    v___x_2110_ = v_reuseFailAlloc_2112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2111_ = leanh::lean_apply_2(
                    v_toPure_2101_,
                    leanh::lean_box(0),
                    v___x_2110_,
                );
                return v___x_2111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(
    mut v_toPure_2114_: *mut leanh::LeanObject,
    mut v_toBind_2115_: *mut leanh::LeanObject,
    mut v___f_2116_: *mut leanh::LeanObject,
    mut v_____x_2117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v_a_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_a_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_unused_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2118_ = leanh::lean_ctor_get(v_____x_2117_, 0);
                leanh::lean_inc(v_fst_2118_);
                if leanh::lean_obj_tag(v_fst_2118_) == 0 {
                    leanh::lean_dec(v___f_2116_);
                    leanh::lean_dec(v_toBind_2115_);
                    v_snd_2119_ = leanh::lean_ctor_get(v_____x_2117_, 1);
                    v_isSharedCheck_2135_ = (!leanh::lean_is_exclusive(v_____x_2117_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v_unused_2136_ = leanh::lean_ctor_get(v_____x_2117_, 0);
                        leanh::lean_dec(v_unused_2136_);
                        v___x_2121_ = v_____x_2117_;
                        v_isShared_2122_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2119_);
                        leanh::lean_dec(v_____x_2117_);
                        v___x_2121_ = leanh::lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2137_ = leanh::lean_ctor_get(v_____x_2117_, 1);
                    v_isSharedCheck_2150_ = (!leanh::lean_is_exclusive(v_____x_2117_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v_unused_2151_ = leanh::lean_ctor_get(v_____x_2117_, 0);
                        leanh::lean_dec(v_unused_2151_);
                        v___x_2139_ = v_____x_2117_;
                        v_isShared_2140_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2137_);
                        leanh::lean_dec(v_____x_2117_);
                        v___x_2139_ = leanh::lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2123_ = leanh::lean_ctor_get(v_fst_2118_, 0);
                v_isSharedCheck_2134_ = (!leanh::lean_is_exclusive(v_fst_2118_)) as u8;
                if v_isSharedCheck_2134_ == 0 {
                    v___x_2125_ = v_fst_2118_;
                    v_isShared_2126_ = v_isSharedCheck_2134_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2123_);
                    leanh::lean_dec(v_fst_2118_);
                    v___x_2125_ = leanh::lean_box(0);
                    v_isShared_2126_ = v_isSharedCheck_2134_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2126_ == 0 {
                    v___x_2128_ = v___x_2125_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2133_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2122_ == 0 {
                    leanh::lean_ctor_set(v___x_2121_, 0, v___x_2128_);
                    v___x_2130_ = v___x_2121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_snd_2119_);
                    v___x_2130_ = v_reuseFailAlloc_2132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2131_ = leanh::lean_apply_2(
                    v_toPure_2114_,
                    leanh::lean_box(0),
                    v___x_2130_,
                );
                return v___x_2131_;
            }
            5 => {
                v_a_2141_ = leanh::lean_ctor_get(v_fst_2118_, 0);
                leanh::lean_inc(v_a_2141_);
                leanh::lean_dec_ref_known(v_fst_2118_, 1);
                leanh::lean_inc(v_toBind_2115_);
                leanh::lean_inc_n(v_toPure_2114_, 2);
                v___f_2142_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4 as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___f_2142_, 0, v_toPure_2114_);
                leanh::lean_closure_set(v___f_2142_, 1, v_a_2141_);
                leanh::lean_closure_set(v___f_2142_, 2, v_toBind_2115_);
                leanh::lean_closure_set(v___f_2142_, 3, v___f_2116_);
                v___f_2143_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_2143_, 0, v_toPure_2114_);
                leanh::lean_inc(v_snd_2137_);
                if v_isShared_2140_ == 0 {
                    leanh::lean_ctor_set(v___x_2139_, 0, v_snd_2137_);
                    v___x_2145_ = v___x_2139_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2137_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2137_);
                    v___x_2145_ = v_reuseFailAlloc_2149_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2146_ = leanh::lean_apply_2(
                    v_toPure_2114_,
                    leanh::lean_box(0),
                    v___x_2145_,
                );
                leanh::lean_inc(v_toBind_2115_);
                v___x_2147_ = leanh::lean_apply_4(
                    v_toBind_2115_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2146_,
                    v___f_2143_,
                );
                v___x_2148_ = leanh::lean_apply_4(
                    v_toBind_2115_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2147_,
                    v___f_2142_,
                );
                return v___x_2148_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(
    mut v_toPure_2152_: *mut leanh::LeanObject,
    mut v_a_2153_: *mut leanh::LeanObject,
    mut v_toBind_2154_: *mut leanh::LeanObject,
    mut v___f_2155_: *mut leanh::LeanObject,
    mut v_____x_2156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_a_2162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut v_unused_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_unused_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_unused_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2157_ = leanh::lean_ctor_get(v_____x_2156_, 0);
                leanh::lean_inc(v_fst_2157_);
                if leanh::lean_obj_tag(v_fst_2157_) == 0 {
                    leanh::lean_dec(v___f_2155_);
                    leanh::lean_dec(v_toBind_2154_);
                    v_snd_2158_ = leanh::lean_ctor_get(v_____x_2156_, 1);
                    v_isSharedCheck_2174_ = (!leanh::lean_is_exclusive(v_____x_2156_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v_unused_2175_ = leanh::lean_ctor_get(v_____x_2156_, 0);
                        leanh::lean_dec(v_unused_2175_);
                        v___x_2160_ = v_____x_2156_;
                        v_isShared_2161_ = v_isSharedCheck_2174_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2158_);
                        leanh::lean_dec(v_____x_2156_);
                        v___x_2160_ = leanh::lean_box(0);
                        v_isShared_2161_ = v_isSharedCheck_2174_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2176_ = leanh::lean_ctor_get(v_____x_2156_, 1);
                    v_isSharedCheck_2193_ = (!leanh::lean_is_exclusive(v_____x_2156_)) as u8;
                    if v_isSharedCheck_2193_ == 0 {
                        v_unused_2194_ = leanh::lean_ctor_get(v_____x_2156_, 0);
                        leanh::lean_dec(v_unused_2194_);
                        v___x_2178_ = v_____x_2156_;
                        v_isShared_2179_ = v_isSharedCheck_2193_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2176_);
                        leanh::lean_dec(v_____x_2156_);
                        v___x_2178_ = leanh::lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2193_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2162_ = leanh::lean_ctor_get(v_fst_2157_, 0);
                v_isSharedCheck_2173_ = (!leanh::lean_is_exclusive(v_fst_2157_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v___x_2164_ = v_fst_2157_;
                    v_isShared_2165_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2162_);
                    leanh::lean_dec(v_fst_2157_);
                    v___x_2164_ = leanh::lean_box(0);
                    v_isShared_2165_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2161_ == 0 {
                    leanh::lean_ctor_set(v___x_2160_, 0, v___x_2167_);
                    v___x_2169_ = v___x_2160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2158_);
                    v___x_2169_ = v_reuseFailAlloc_2171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2170_ = leanh::lean_apply_2(
                    v_toPure_2152_,
                    leanh::lean_box(0),
                    v___x_2169_,
                );
                return v___x_2170_;
            }
            5 => {
                v_isSharedCheck_2191_ = (!leanh::lean_is_exclusive(v_fst_2157_)) as u8;
                if v_isSharedCheck_2191_ == 0 {
                    v_unused_2192_ = leanh::lean_ctor_get(v_fst_2157_, 0);
                    leanh::lean_dec(v_unused_2192_);
                    v___x_2181_ = v_fst_2157_;
                    v_isShared_2182_ = v_isSharedCheck_2191_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2157_);
                    v___x_2181_ = leanh::lean_box(0);
                    v_isShared_2182_ = v_isSharedCheck_2191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                leanh::lean_inc_ref(v_a_2153_);
                if v_isShared_2182_ == 0 {
                    leanh::lean_ctor_set(v___x_2181_, 0, v_a_2153_);
                    v___x_2184_ = v___x_2181_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2153_);
                    v___x_2184_ = v_reuseFailAlloc_2190_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2179_ == 0 {
                    leanh::lean_ctor_set(v___x_2178_, 0, v___x_2184_);
                    v___x_2186_ = v___x_2178_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2184_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_snd_2176_);
                    v___x_2186_ = v_reuseFailAlloc_2189_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2187_ = leanh::lean_apply_2(
                    v_toPure_2152_,
                    leanh::lean_box(0),
                    v___x_2186_,
                );
                v___x_2188_ = leanh::lean_apply_4(
                    v_toBind_2154_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2187_,
                    v___f_2155_,
                );
                return v___x_2188_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed(
    mut v_toPure_2195_: *mut leanh::LeanObject,
    mut v_a_2196_: *mut leanh::LeanObject,
    mut v_toBind_2197_: *mut leanh::LeanObject,
    mut v___f_2198_: *mut leanh::LeanObject,
    mut v_____x_2199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2200_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(
            v_toPure_2195_,
            v_a_2196_,
            v_toBind_2197_,
            v___f_2198_,
            v_____x_2199_,
        );
    leanh::lean_dec_ref(v_a_2196_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(
    mut v_toPure_2203_: *mut leanh::LeanObject,
    mut v_inst_2204_: *mut leanh::LeanObject,
    mut v_toBind_2205_: *mut leanh::LeanObject,
    mut v_a_2206_: *mut leanh::LeanObject,
    mut v_maxCalls_2207_: *mut leanh::LeanObject,
    mut v_____x_2208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___y_2215_: u8 = 0;
    let mut v_cur_2216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_2217_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_2218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_2219_: u8 = 0;
    let mut v___x_2221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v___x_2243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2251_: u8 = 0;
    let mut v___x_2253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_a_2258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v_numCalls_2261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2209_ = leanh::lean_ctor_get(v_____x_2208_, 0);
                v_snd_2210_ = leanh::lean_ctor_get(v_____x_2208_, 1);
                v_isSharedCheck_2263_ = (!leanh::lean_is_exclusive(v_____x_2208_)) as u8;
                if v_isSharedCheck_2263_ == 0 {
                    v___x_2212_ = v_____x_2208_;
                    v_isShared_2213_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2210_);
                    leanh::lean_inc(v_fst_2209_);
                    leanh::lean_dec(v_____x_2208_);
                    v___x_2212_ = leanh::lean_box(0);
                    v_isShared_2213_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_fst_2209_) == 0 {
                    leanh::lean_del_object(v___x_2212_);
                    leanh::lean_dec(v_toBind_2205_);
                    leanh::lean_dec_ref(v_inst_2204_);
                    v_a_2248_ = leanh::lean_ctor_get(v_fst_2209_, 0);
                    v_isSharedCheck_2257_ = (!leanh::lean_is_exclusive(v_fst_2209_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v___x_2250_ = v_fst_2209_;
                        v_isShared_2251_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2248_);
                        leanh::lean_dec(v_fst_2209_);
                        v___x_2250_ = leanh::lean_box(0);
                        v_isShared_2251_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2258_ = leanh::lean_ctor_get(v_fst_2209_, 0);
                    leanh::lean_inc(v_a_2258_);
                    leanh::lean_dec_ref_known(v_fst_2209_, 1);
                    v___x_2259_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2260_ = lean_nat_dec_lt(v___x_2259_, v_maxCalls_2207_);
                    if v___x_2260_ == 0 {
                        leanh::lean_dec(v_a_2258_);
                        v___y_2215_ = v___x_2260_;
                        state = 2;
                        continue;
                    } else {
                        v_numCalls_2261_ = leanh::lean_ctor_get(v_a_2258_, 2);
                        leanh::lean_inc(v_numCalls_2261_);
                        leanh::lean_dec(v_a_2258_);
                        v___x_2262_ = lean_nat_dec_le(v_maxCalls_2207_, v_numCalls_2261_);
                        leanh::lean_dec(v_numCalls_2261_);
                        v___y_2215_ = v___x_2262_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_2215_ == 0 {
                    v_cur_2216_ = leanh::lean_ctor_get(v_snd_2210_, 0);
                    v_added_2217_ = leanh::lean_ctor_get(v_snd_2210_, 1);
                    v_numCalls_2218_ = leanh::lean_ctor_get(v_snd_2210_, 2);
                    v_found_2219_ = leanh::lean_ctor_get_uint8(
                        v_snd_2210_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    v_isSharedCheck_2242_ = (!leanh::lean_is_exclusive(v_snd_2210_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2221_ = v_snd_2210_;
                        v_isShared_2222_ = v_isSharedCheck_2242_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_numCalls_2218_);
                        leanh::lean_inc(v_added_2217_);
                        leanh::lean_inc(v_cur_2216_);
                        leanh::lean_dec(v_snd_2210_);
                        v___x_2221_ = leanh::lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2242_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toBind_2205_);
                    leanh::lean_dec_ref(v_inst_2204_);
                    v___x_2243_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0;
                    if v_isShared_2213_ == 0 {
                        leanh::lean_ctor_set(v___x_2212_, 0, v___x_2243_);
                        v___x_2245_ = v___x_2212_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2247_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_snd_2210_);
                        v___x_2245_ = v_reuseFailAlloc_2247_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2223_ = 1;
                v___x_2224_ = leanh::lean_box((v___x_2223_) as usize);
                leanh::lean_inc_n(v_toPure_2203_, 5);
                v___f_2225_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                leanh::lean_closure_set(v___f_2225_, 0, v_toPure_2203_);
                leanh::lean_closure_set(v___f_2225_, 1, v___x_2224_);
                leanh::lean_inc_n(v_toBind_2205_, 3);
                v___f_2226_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___f_2226_, 0, v_toPure_2203_);
                leanh::lean_closure_set(v___f_2226_, 1, v_inst_2204_);
                leanh::lean_closure_set(v___f_2226_, 2, v_toBind_2205_);
                leanh::lean_closure_set(v___f_2226_, 3, v___f_2225_);
                v___f_2227_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6 as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_2227_, 0, v_toPure_2203_);
                leanh::lean_closure_set(v___f_2227_, 1, v_toBind_2205_);
                leanh::lean_closure_set(v___f_2227_, 2, v___f_2226_);
                leanh::lean_inc_ref(v_a_2206_);
                v___f_2228_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed as *mut core::ffi::c_void, 5, 4);
                leanh::lean_closure_set(v___f_2228_, 0, v_toPure_2203_);
                leanh::lean_closure_set(v___f_2228_, 1, v_a_2206_);
                leanh::lean_closure_set(v___f_2228_, 2, v_toBind_2205_);
                leanh::lean_closure_set(v___f_2228_, 3, v___f_2227_);
                v___f_2229_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_2229_, 0, v_toPure_2203_);
                v___x_2230_ = leanh::lean_box(0);
                v___x_2231_ = leanh::lean_unsigned_to_nat(1);
                v___x_2232_ = lean_nat_add(v_numCalls_2218_, v___x_2231_);
                leanh::lean_dec(v_numCalls_2218_);
                if v_isShared_2222_ == 0 {
                    leanh::lean_ctor_set(v___x_2221_, 2, v___x_2232_);
                    v___x_2234_ = v___x_2221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_cur_2216_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_added_2217_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2241_, 2, v___x_2232_);
                    leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v_found_2219_,
                    );
                    v___x_2234_ = v_reuseFailAlloc_2241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2213_ == 0 {
                    leanh::lean_ctor_set(v___x_2212_, 1, v___x_2234_);
                    leanh::lean_ctor_set(v___x_2212_, 0, v___x_2230_);
                    v___x_2236_ = v___x_2212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2230_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2234_);
                    v___x_2236_ = v_reuseFailAlloc_2240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2237_ = leanh::lean_apply_2(
                    v_toPure_2203_,
                    leanh::lean_box(0),
                    v___x_2236_,
                );
                leanh::lean_inc(v_toBind_2205_);
                v___x_2238_ = leanh::lean_apply_4(
                    v_toBind_2205_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2237_,
                    v___f_2229_,
                );
                v___x_2239_ = leanh::lean_apply_4(
                    v_toBind_2205_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2238_,
                    v___f_2228_,
                );
                return v___x_2239_;
            }
            6 => {
                v___x_2246_ = leanh::lean_apply_2(
                    v_toPure_2203_,
                    leanh::lean_box(0),
                    v___x_2245_,
                );
                return v___x_2246_;
            }
            7 => {
                if v_isShared_2251_ == 0 {
                    v___x_2253_ = v___x_2250_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2256_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2248_);
                    v___x_2253_ = v_reuseFailAlloc_2256_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2254_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2254_, 0, v___x_2253_);
                leanh::lean_ctor_set(v___x_2254_, 1, v_snd_2210_);
                v___x_2255_ = leanh::lean_apply_2(
                    v_toPure_2203_,
                    leanh::lean_box(0),
                    v___x_2254_,
                );
                return v___x_2255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(
    mut v_toPure_2264_: *mut leanh::LeanObject,
    mut v_inst_2265_: *mut leanh::LeanObject,
    mut v_toBind_2266_: *mut leanh::LeanObject,
    mut v_a_2267_: *mut leanh::LeanObject,
    mut v_maxCalls_2268_: *mut leanh::LeanObject,
    mut v_____x_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2270_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(
            v_toPure_2264_,
            v_inst_2265_,
            v_toBind_2266_,
            v_a_2267_,
            v_maxCalls_2268_,
            v_____x_2269_,
        );
    leanh::lean_dec(v_maxCalls_2268_);
    leanh::lean_dec_ref(v_a_2267_);
    return v_res_2270_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(
    mut v_toPure_2271_: *mut leanh::LeanObject,
    mut v_inst_2272_: *mut leanh::LeanObject,
    mut v_toBind_2273_: *mut leanh::LeanObject,
    mut v_a_2274_: *mut leanh::LeanObject,
    mut v_____x_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v_a_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut v_isSharedCheck_2293_: u8 = 0;
    let mut v_unused_2294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v_maxCalls_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_unused_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2276_ = leanh::lean_ctor_get(v_____x_2275_, 0);
                leanh::lean_inc(v_fst_2276_);
                if leanh::lean_obj_tag(v_fst_2276_) == 0 {
                    leanh::lean_dec(v_toBind_2273_);
                    leanh::lean_dec_ref(v_inst_2272_);
                    v_snd_2277_ = leanh::lean_ctor_get(v_____x_2275_, 1);
                    v_isSharedCheck_2293_ = (!leanh::lean_is_exclusive(v_____x_2275_)) as u8;
                    if v_isSharedCheck_2293_ == 0 {
                        v_unused_2294_ = leanh::lean_ctor_get(v_____x_2275_, 0);
                        leanh::lean_dec(v_unused_2294_);
                        v___x_2279_ = v_____x_2275_;
                        v_isShared_2280_ = v_isSharedCheck_2293_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2277_);
                        leanh::lean_dec(v_____x_2275_);
                        v___x_2279_ = leanh::lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2295_ = leanh::lean_ctor_get(v_fst_2276_, 0);
                    leanh::lean_inc(v_a_2295_);
                    leanh::lean_dec_ref_known(v_fst_2276_, 1);
                    v_snd_2296_ = leanh::lean_ctor_get(v_____x_2275_, 1);
                    v_isSharedCheck_2309_ = (!leanh::lean_is_exclusive(v_____x_2275_)) as u8;
                    if v_isSharedCheck_2309_ == 0 {
                        v_unused_2310_ = leanh::lean_ctor_get(v_____x_2275_, 0);
                        leanh::lean_dec(v_unused_2310_);
                        v___x_2298_ = v_____x_2275_;
                        v_isShared_2299_ = v_isSharedCheck_2309_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2296_);
                        leanh::lean_dec(v_____x_2275_);
                        v___x_2298_ = leanh::lean_box(0);
                        v_isShared_2299_ = v_isSharedCheck_2309_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2281_ = leanh::lean_ctor_get(v_fst_2276_, 0);
                v_isSharedCheck_2292_ = (!leanh::lean_is_exclusive(v_fst_2276_)) as u8;
                if v_isSharedCheck_2292_ == 0 {
                    v___x_2283_ = v_fst_2276_;
                    v_isShared_2284_ = v_isSharedCheck_2292_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2281_);
                    leanh::lean_dec(v_fst_2276_);
                    v___x_2283_ = leanh::lean_box(0);
                    v_isShared_2284_ = v_isSharedCheck_2292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2284_ == 0 {
                    v___x_2286_ = v___x_2283_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2291_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2280_ == 0 {
                    leanh::lean_ctor_set(v___x_2279_, 0, v___x_2286_);
                    v___x_2288_ = v___x_2279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2290_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2286_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_snd_2277_);
                    v___x_2288_ = v_reuseFailAlloc_2290_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2289_ = leanh::lean_apply_2(
                    v_toPure_2271_,
                    leanh::lean_box(0),
                    v___x_2288_,
                );
                return v___x_2289_;
            }
            5 => {
                v_maxCalls_2300_ = leanh::lean_ctor_get(v_a_2295_, 2);
                leanh::lean_inc(v_maxCalls_2300_);
                leanh::lean_dec(v_a_2295_);
                leanh::lean_inc_ref(v_a_2274_);
                leanh::lean_inc(v_toBind_2273_);
                leanh::lean_inc_n(v_toPure_2271_, 2);
                v___f_2301_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed as *mut core::ffi::c_void, 6, 5);
                leanh::lean_closure_set(v___f_2301_, 0, v_toPure_2271_);
                leanh::lean_closure_set(v___f_2301_, 1, v_inst_2272_);
                leanh::lean_closure_set(v___f_2301_, 2, v_toBind_2273_);
                leanh::lean_closure_set(v___f_2301_, 3, v_a_2274_);
                leanh::lean_closure_set(v___f_2301_, 4, v_maxCalls_2300_);
                v___f_2302_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_2302_, 0, v_toPure_2271_);
                leanh::lean_inc(v_snd_2296_);
                if v_isShared_2299_ == 0 {
                    leanh::lean_ctor_set(v___x_2298_, 0, v_snd_2296_);
                    v___x_2304_ = v___x_2298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_snd_2296_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_snd_2296_);
                    v___x_2304_ = v_reuseFailAlloc_2308_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2305_ = leanh::lean_apply_2(
                    v_toPure_2271_,
                    leanh::lean_box(0),
                    v___x_2304_,
                );
                leanh::lean_inc(v_toBind_2273_);
                v___x_2306_ = leanh::lean_apply_4(
                    v_toBind_2273_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2305_,
                    v___f_2302_,
                );
                v___x_2307_ = leanh::lean_apply_4(
                    v_toBind_2273_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2306_,
                    v___f_2301_,
                );
                return v___x_2307_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed(
    mut v_toPure_2311_: *mut leanh::LeanObject,
    mut v_inst_2312_: *mut leanh::LeanObject,
    mut v_toBind_2313_: *mut leanh::LeanObject,
    mut v_a_2314_: *mut leanh::LeanObject,
    mut v_____x_2315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2316_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(
            v_toPure_2311_,
            v_inst_2312_,
            v_toBind_2313_,
            v_a_2314_,
            v_____x_2315_,
        );
    leanh::lean_dec_ref(v_a_2314_);
    return v_res_2316_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
    mut v_inst_2317_: *mut leanh::LeanObject,
    mut v_a_2318_: *mut leanh::LeanObject,
    mut v_a_2319_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2320_ = leanh::lean_ctor_get(v_inst_2317_, 0);
    v_toBind_2321_ = leanh::lean_ctor_get(v_inst_2317_, 1);
    leanh::lean_inc_n(v_toBind_2321_, 2);
    v_toPure_2322_ = leanh::lean_ctor_get(v_toApplicative_2320_, 1);
    leanh::lean_inc_n(v_toPure_2322_, 2);
    leanh::lean_inc_ref_n(v_a_2318_, 2);
    v___f_2323_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed as *mut core::ffi::c_void, 5, 4);
    leanh::lean_closure_set(v___f_2323_, 0, v_toPure_2322_);
    leanh::lean_closure_set(v___f_2323_, 1, v_inst_2317_);
    leanh::lean_closure_set(v___f_2323_, 2, v_toBind_2321_);
    leanh::lean_closure_set(v___f_2323_, 3, v_a_2318_);
    v___x_2324_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2324_, 0, v_a_2318_);
    v___x_2325_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    leanh::lean_ctor_set(v___x_2325_, 1, v_a_2319_);
    v___x_2326_ =
        leanh::lean_apply_2(v_toPure_2322_, leanh::lean_box(0), v___x_2325_);
    v___x_2327_ = leanh::lean_apply_4(
        v_toBind_2321_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2326_,
        v___f_2323_,
    );
    return v___x_2327_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(
    mut v_inst_2328_: *mut leanh::LeanObject,
    mut v_a_2329_: *mut leanh::LeanObject,
    mut v_a_2330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2328_,
        v_a_2329_,
        v_a_2330_,
    );
    leanh::lean_dec_ref(v_a_2329_);
    return v_res_2331_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(
    mut v_m_2332_: *mut leanh::LeanObject,
    mut v_inst_2333_: *mut leanh::LeanObject,
    mut v_a_2334_: *mut leanh::LeanObject,
    mut v_a_2335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2333_,
        v_a_2334_,
        v_a_2335_,
    );
    return v___x_2336_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(
    mut v_m_2337_: *mut leanh::LeanObject,
    mut v_inst_2338_: *mut leanh::LeanObject,
    mut v_a_2339_: *mut leanh::LeanObject,
    mut v_a_2340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2341_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(
        v_m_2337_,
        v_inst_2338_,
        v_a_2339_,
        v_a_2340_,
    );
    leanh::lean_dec_ref(v_a_2339_);
    return v_res_2341_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(
    mut v_toPure_2342_: *mut leanh::LeanObject,
    mut v_____x_2343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v_a_2349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v_unused_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v_a_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_unused_2380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2344_ = leanh::lean_ctor_get(v_____x_2343_, 0);
                leanh::lean_inc(v_fst_2344_);
                if leanh::lean_obj_tag(v_fst_2344_) == 0 {
                    v_snd_2345_ = leanh::lean_ctor_get(v_____x_2343_, 1);
                    v_isSharedCheck_2361_ = (!leanh::lean_is_exclusive(v_____x_2343_)) as u8;
                    if v_isSharedCheck_2361_ == 0 {
                        v_unused_2362_ = leanh::lean_ctor_get(v_____x_2343_, 0);
                        leanh::lean_dec(v_unused_2362_);
                        v___x_2347_ = v_____x_2343_;
                        v_isShared_2348_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2345_);
                        leanh::lean_dec(v_____x_2343_);
                        v___x_2347_ = leanh::lean_box(0);
                        v_isShared_2348_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2363_ = leanh::lean_ctor_get(v_____x_2343_, 1);
                    v_isSharedCheck_2379_ = (!leanh::lean_is_exclusive(v_____x_2343_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v_unused_2380_ = leanh::lean_ctor_get(v_____x_2343_, 0);
                        leanh::lean_dec(v_unused_2380_);
                        v___x_2365_ = v_____x_2343_;
                        v_isShared_2366_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2363_);
                        leanh::lean_dec(v_____x_2343_);
                        v___x_2365_ = leanh::lean_box(0);
                        v_isShared_2366_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2349_ = leanh::lean_ctor_get(v_fst_2344_, 0);
                v_isSharedCheck_2360_ = (!leanh::lean_is_exclusive(v_fst_2344_)) as u8;
                if v_isSharedCheck_2360_ == 0 {
                    v___x_2351_ = v_fst_2344_;
                    v_isShared_2352_ = v_isSharedCheck_2360_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2349_);
                    leanh::lean_dec(v_fst_2344_);
                    v___x_2351_ = leanh::lean_box(0);
                    v_isShared_2352_ = v_isSharedCheck_2360_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2352_ == 0 {
                    v___x_2354_ = v___x_2351_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2359_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2348_ == 0 {
                    leanh::lean_ctor_set(v___x_2347_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_snd_2345_);
                    v___x_2356_ = v_reuseFailAlloc_2358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2357_ = leanh::lean_apply_2(
                    v_toPure_2342_,
                    leanh::lean_box(0),
                    v___x_2356_,
                );
                return v___x_2357_;
            }
            5 => {
                v_a_2367_ = leanh::lean_ctor_get(v_fst_2344_, 0);
                v_isSharedCheck_2378_ = (!leanh::lean_is_exclusive(v_fst_2344_)) as u8;
                if v_isSharedCheck_2378_ == 0 {
                    v___x_2369_ = v_fst_2344_;
                    v_isShared_2370_ = v_isSharedCheck_2378_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2367_);
                    leanh::lean_dec(v_fst_2344_);
                    v___x_2369_ = leanh::lean_box(0);
                    v_isShared_2370_ = v_isSharedCheck_2378_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2370_ == 0 {
                    v___x_2372_ = v___x_2369_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2367_);
                    v___x_2372_ = v_reuseFailAlloc_2377_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2366_ == 0 {
                    leanh::lean_ctor_set(v___x_2365_, 0, v___x_2372_);
                    v___x_2374_ = v___x_2365_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2372_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_snd_2363_);
                    v___x_2374_ = v_reuseFailAlloc_2376_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2375_ = leanh::lean_apply_2(
                    v_toPure_2342_,
                    leanh::lean_box(0),
                    v___x_2374_,
                );
                return v___x_2375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(
    mut v_toPure_2381_: *mut leanh::LeanObject,
    mut v___x_2382_: *mut leanh::LeanObject,
    mut v_____x_2383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v_a_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_unused_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v_fst_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v_snd_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_unused_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2384_ = leanh::lean_ctor_get(v_____x_2383_, 0);
                leanh::lean_inc(v_fst_2384_);
                if leanh::lean_obj_tag(v_fst_2384_) == 0 {
                    v_snd_2385_ = leanh::lean_ctor_get(v_____x_2383_, 1);
                    v_isSharedCheck_2401_ = (!leanh::lean_is_exclusive(v_____x_2383_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v_unused_2402_ = leanh::lean_ctor_get(v_____x_2383_, 0);
                        leanh::lean_dec(v_unused_2402_);
                        v___x_2387_ = v_____x_2383_;
                        v_isShared_2388_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2385_);
                        leanh::lean_dec(v_____x_2383_);
                        v___x_2387_ = leanh::lean_box(0);
                        v_isShared_2388_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2403_ = leanh::lean_ctor_get(v_fst_2384_, 0);
                    v_isSharedCheck_2430_ = (!leanh::lean_is_exclusive(v_fst_2384_)) as u8;
                    if v_isSharedCheck_2430_ == 0 {
                        v___x_2405_ = v_fst_2384_;
                        v_isShared_2406_ = v_isSharedCheck_2430_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2403_);
                        leanh::lean_dec(v_fst_2384_);
                        v___x_2405_ = leanh::lean_box(0);
                        v_isShared_2406_ = v_isSharedCheck_2430_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2389_ = leanh::lean_ctor_get(v_fst_2384_, 0);
                v_isSharedCheck_2400_ = (!leanh::lean_is_exclusive(v_fst_2384_)) as u8;
                if v_isSharedCheck_2400_ == 0 {
                    v___x_2391_ = v_fst_2384_;
                    v_isShared_2392_ = v_isSharedCheck_2400_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2389_);
                    leanh::lean_dec(v_fst_2384_);
                    v___x_2391_ = leanh::lean_box(0);
                    v_isShared_2392_ = v_isSharedCheck_2400_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2392_ == 0 {
                    v___x_2394_ = v___x_2391_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2399_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2389_);
                    v___x_2394_ = v_reuseFailAlloc_2399_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2388_ == 0 {
                    leanh::lean_ctor_set(v___x_2387_, 0, v___x_2394_);
                    v___x_2396_ = v___x_2387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2394_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_snd_2385_);
                    v___x_2396_ = v_reuseFailAlloc_2398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2397_ = leanh::lean_apply_2(
                    v_toPure_2381_,
                    leanh::lean_box(0),
                    v___x_2396_,
                );
                return v___x_2397_;
            }
            5 => {
                v_fst_2407_ = leanh::lean_ctor_get(v_a_2403_, 0);
                v_isSharedCheck_2428_ = (!leanh::lean_is_exclusive(v_a_2403_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v_unused_2429_ = leanh::lean_ctor_get(v_a_2403_, 1);
                    leanh::lean_dec(v_unused_2429_);
                    v___x_2409_ = v_a_2403_;
                    v_isShared_2410_ = v_isSharedCheck_2428_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2407_);
                    leanh::lean_dec(v_a_2403_);
                    v___x_2409_ = leanh::lean_box(0);
                    v_isShared_2410_ = v_isSharedCheck_2428_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if leanh::lean_obj_tag(v_fst_2407_) == 0 {
                    v_snd_2411_ = leanh::lean_ctor_get(v_____x_2383_, 1);
                    leanh::lean_inc(v_snd_2411_);
                    leanh::lean_dec_ref(v_____x_2383_);
                    if v_isShared_2406_ == 0 {
                        leanh::lean_ctor_set(v___x_2405_, 0, v___x_2382_);
                        v___x_2413_ = v___x_2405_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2382_);
                        v___x_2413_ = v_reuseFailAlloc_2418_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_snd_2419_ = leanh::lean_ctor_get(v_____x_2383_, 1);
                    leanh::lean_inc(v_snd_2419_);
                    leanh::lean_dec_ref(v_____x_2383_);
                    v_val_2420_ = leanh::lean_ctor_get(v_fst_2407_, 0);
                    leanh::lean_inc(v_val_2420_);
                    leanh::lean_dec_ref_known(v_fst_2407_, 1);
                    if v_isShared_2406_ == 0 {
                        leanh::lean_ctor_set(v___x_2405_, 0, v_val_2420_);
                        v___x_2422_ = v___x_2405_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2427_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_val_2420_);
                        v___x_2422_ = v_reuseFailAlloc_2427_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2410_ == 0 {
                    leanh::lean_ctor_set(v___x_2409_, 1, v_snd_2411_);
                    leanh::lean_ctor_set(v___x_2409_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2409_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_snd_2411_);
                    v___x_2415_ = v_reuseFailAlloc_2417_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2416_ = leanh::lean_apply_2(
                    v_toPure_2381_,
                    leanh::lean_box(0),
                    v___x_2415_,
                );
                return v___x_2416_;
            }
            9 => {
                if v_isShared_2410_ == 0 {
                    leanh::lean_ctor_set(v___x_2409_, 1, v_snd_2419_);
                    leanh::lean_ctor_set(v___x_2409_, 0, v___x_2422_);
                    v___x_2424_ = v___x_2409_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_snd_2419_);
                    v___x_2424_ = v_reuseFailAlloc_2426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2425_ = leanh::lean_apply_2(
                    v_toPure_2381_,
                    leanh::lean_box(0),
                    v___x_2424_,
                );
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(
    mut v_toPure_2431_: *mut leanh::LeanObject,
    mut v___x_2432_: *mut leanh::LeanObject,
    mut v___x_2433_: *mut leanh::LeanObject,
    mut v_____x_2434_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v_a_2440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_unused_2453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v_snd_2459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_unused_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_unused_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2435_ = leanh::lean_ctor_get(v_____x_2434_, 0);
                leanh::lean_inc(v_fst_2435_);
                if leanh::lean_obj_tag(v_fst_2435_) == 0 {
                    leanh::lean_dec_ref(v___x_2432_);
                    v_snd_2436_ = leanh::lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2452_ = (!leanh::lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2452_ == 0 {
                        v_unused_2453_ = leanh::lean_ctor_get(v_____x_2434_, 0);
                        leanh::lean_dec(v_unused_2453_);
                        v___x_2438_ = v_____x_2434_;
                        v_isShared_2439_ = v_isSharedCheck_2452_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2436_);
                        leanh::lean_dec(v_____x_2434_);
                        v___x_2438_ = leanh::lean_box(0);
                        v_isShared_2439_ = v_isSharedCheck_2452_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2454_ = leanh::lean_ctor_get(v_fst_2435_, 0);
                    v_isSharedCheck_2489_ = (!leanh::lean_is_exclusive(v_fst_2435_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2456_ = v_fst_2435_;
                        v_isShared_2457_ = v_isSharedCheck_2489_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2454_);
                        leanh::lean_dec(v_fst_2435_);
                        v___x_2456_ = leanh::lean_box(0);
                        v_isShared_2457_ = v_isSharedCheck_2489_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2440_ = leanh::lean_ctor_get(v_fst_2435_, 0);
                v_isSharedCheck_2451_ = (!leanh::lean_is_exclusive(v_fst_2435_)) as u8;
                if v_isSharedCheck_2451_ == 0 {
                    v___x_2442_ = v_fst_2435_;
                    v_isShared_2443_ = v_isSharedCheck_2451_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2440_);
                    leanh::lean_dec(v_fst_2435_);
                    v___x_2442_ = leanh::lean_box(0);
                    v_isShared_2443_ = v_isSharedCheck_2451_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2443_ == 0 {
                    v___x_2445_ = v___x_2442_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2450_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2440_);
                    v___x_2445_ = v_reuseFailAlloc_2450_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2439_ == 0 {
                    leanh::lean_ctor_set(v___x_2438_, 0, v___x_2445_);
                    v___x_2447_ = v___x_2438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_snd_2436_);
                    v___x_2447_ = v_reuseFailAlloc_2449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2448_ = leanh::lean_apply_2(
                    v_toPure_2431_,
                    leanh::lean_box(0),
                    v___x_2447_,
                );
                return v___x_2448_;
            }
            5 => {
                v___x_2458_ = (leanh::lean_unbox(v_a_2454_) as u8);
                leanh::lean_dec(v_a_2454_);
                if v___x_2458_ == 0 {
                    v_snd_2459_ = leanh::lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2471_ = (!leanh::lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2471_ == 0 {
                        v_unused_2472_ = leanh::lean_ctor_get(v_____x_2434_, 0);
                        leanh::lean_dec(v_unused_2472_);
                        v___x_2461_ = v_____x_2434_;
                        v_isShared_2462_ = v_isSharedCheck_2471_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2459_);
                        leanh::lean_dec(v_____x_2434_);
                        v___x_2461_ = leanh::lean_box(0);
                        v_isShared_2462_ = v_isSharedCheck_2471_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_2432_);
                    v_snd_2473_ = leanh::lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2487_ = (!leanh::lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2487_ == 0 {
                        v_unused_2488_ = leanh::lean_ctor_get(v_____x_2434_, 0);
                        leanh::lean_dec(v_unused_2488_);
                        v___x_2475_ = v_____x_2434_;
                        v_isShared_2476_ = v_isSharedCheck_2487_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2473_);
                        leanh::lean_dec(v_____x_2434_);
                        v___x_2475_ = leanh::lean_box(0);
                        v_isShared_2476_ = v_isSharedCheck_2487_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2463_, 0, v___x_2432_);
                if v_isShared_2457_ == 0 {
                    leanh::lean_ctor_set(v___x_2456_, 0, v___x_2463_);
                    v___x_2465_ = v___x_2456_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2463_);
                    v___x_2465_ = v_reuseFailAlloc_2470_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2462_ == 0 {
                    leanh::lean_ctor_set(v___x_2461_, 0, v___x_2465_);
                    v___x_2467_ = v___x_2461_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2465_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_snd_2459_);
                    v___x_2467_ = v_reuseFailAlloc_2469_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2468_ = leanh::lean_apply_2(
                    v_toPure_2431_,
                    leanh::lean_box(0),
                    v___x_2467_,
                );
                return v___x_2468_;
            }
            9 => {
                v___x_2477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2477_, 0, v___x_2433_);
                if v_isShared_2476_ == 0 {
                    leanh::lean_ctor_set(v___x_2475_, 1, v___x_2433_);
                    leanh::lean_ctor_set(v___x_2475_, 0, v___x_2477_);
                    v___x_2479_ = v___x_2475_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2433_);
                    v___x_2479_ = v_reuseFailAlloc_2486_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2480_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                if v_isShared_2457_ == 0 {
                    leanh::lean_ctor_set(v___x_2456_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2456_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2480_);
                    v___x_2482_ = v_reuseFailAlloc_2485_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2483_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                leanh::lean_ctor_set(v___x_2483_, 1, v_snd_2473_);
                v___x_2484_ = leanh::lean_apply_2(
                    v_toPure_2431_,
                    leanh::lean_box(0),
                    v___x_2483_,
                );
                return v___x_2484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(
    mut v_inst_2490_: *mut leanh::LeanObject,
    mut v_toBind_2491_: *mut leanh::LeanObject,
    mut v___f_2492_: *mut leanh::LeanObject,
    mut v_____r_2493_: *mut leanh::LeanObject,
    mut v___y_2494_: *mut leanh::LeanObject,
    mut v___y_2495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2496_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2490_,
        v___y_2494_,
        v___y_2495_,
    );
    v___x_2497_ = leanh::lean_apply_4(
        v_toBind_2491_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2496_,
        v___f_2492_,
    );
    return v___x_2497_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(
    mut v_inst_2498_: *mut leanh::LeanObject,
    mut v_toBind_2499_: *mut leanh::LeanObject,
    mut v___f_2500_: *mut leanh::LeanObject,
    mut v_____r_2501_: *mut leanh::LeanObject,
    mut v___y_2502_: *mut leanh::LeanObject,
    mut v___y_2503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2504_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2504_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(
            v_inst_2498_,
            v_toBind_2499_,
            v___f_2500_,
            v_____r_2501_,
            v___y_2502_,
            v___y_2503_,
        );
    leanh::lean_dec_ref(v___y_2502_);
    return v_res_2504_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(
    mut v_toPure_2505_: *mut leanh::LeanObject,
    mut v_next_2506_: *mut leanh::LeanObject,
    mut v_G_2507_: *mut leanh::LeanObject,
    mut v___y_2508_: *mut leanh::LeanObject,
    mut v_____x_2509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_a_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_isSharedCheck_2527_: u8 = 0;
    let mut v_unused_2528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v_snd_2533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v_a_2537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut v_unused_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2510_ = leanh::lean_ctor_get(v_____x_2509_, 0);
                leanh::lean_inc(v_fst_2510_);
                if leanh::lean_obj_tag(v_fst_2510_) == 0 {
                    leanh::lean_dec(v_G_2507_);
                    v_snd_2511_ = leanh::lean_ctor_get(v_____x_2509_, 1);
                    v_isSharedCheck_2527_ = (!leanh::lean_is_exclusive(v_____x_2509_)) as u8;
                    if v_isSharedCheck_2527_ == 0 {
                        v_unused_2528_ = leanh::lean_ctor_get(v_____x_2509_, 0);
                        leanh::lean_dec(v_unused_2528_);
                        v___x_2513_ = v_____x_2509_;
                        v_isShared_2514_ = v_isSharedCheck_2527_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2511_);
                        leanh::lean_dec(v_____x_2509_);
                        v___x_2513_ = leanh::lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2527_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2529_ = leanh::lean_ctor_get(v_fst_2510_, 0);
                    v_isSharedCheck_2552_ = (!leanh::lean_is_exclusive(v_fst_2510_)) as u8;
                    if v_isSharedCheck_2552_ == 0 {
                        v___x_2531_ = v_fst_2510_;
                        v_isShared_2532_ = v_isSharedCheck_2552_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2529_);
                        leanh::lean_dec(v_fst_2510_);
                        v___x_2531_ = leanh::lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2552_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2515_ = leanh::lean_ctor_get(v_fst_2510_, 0);
                v_isSharedCheck_2526_ = (!leanh::lean_is_exclusive(v_fst_2510_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v___x_2517_ = v_fst_2510_;
                    v_isShared_2518_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2515_);
                    leanh::lean_dec(v_fst_2510_);
                    v___x_2517_ = leanh::lean_box(0);
                    v_isShared_2518_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2518_ == 0 {
                    v___x_2520_ = v___x_2517_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2525_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2515_);
                    v___x_2520_ = v_reuseFailAlloc_2525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2514_ == 0 {
                    leanh::lean_ctor_set(v___x_2513_, 0, v___x_2520_);
                    v___x_2522_ = v___x_2513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2520_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_snd_2511_);
                    v___x_2522_ = v_reuseFailAlloc_2524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2523_ = leanh::lean_apply_2(
                    v_toPure_2505_,
                    leanh::lean_box(0),
                    v___x_2522_,
                );
                return v___x_2523_;
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2529_) == 0 {
                    leanh::lean_dec(v_G_2507_);
                    v_snd_2533_ = leanh::lean_ctor_get(v_____x_2509_, 1);
                    v_isSharedCheck_2545_ = (!leanh::lean_is_exclusive(v_____x_2509_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v_unused_2546_ = leanh::lean_ctor_get(v_____x_2509_, 0);
                        leanh::lean_dec(v_unused_2546_);
                        v___x_2535_ = v_____x_2509_;
                        v_isShared_2536_ = v_isSharedCheck_2545_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2533_);
                        leanh::lean_dec(v_____x_2509_);
                        v___x_2535_ = leanh::lean_box(0);
                        v_isShared_2536_ = v_isSharedCheck_2545_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_2531_);
                    leanh::lean_dec(v_toPure_2505_);
                    v_snd_2547_ = leanh::lean_ctor_get(v_____x_2509_, 1);
                    leanh::lean_inc(v_snd_2547_);
                    leanh::lean_dec_ref(v_____x_2509_);
                    v_a_2548_ = leanh::lean_ctor_get(v_a_2529_, 0);
                    leanh::lean_inc(v_a_2548_);
                    leanh::lean_dec_ref_known(v_a_2529_, 1);
                    v___x_2549_ = leanh::lean_unsigned_to_nat(1);
                    v___x_2550_ = lean_nat_add(v_next_2506_, v___x_2549_);
                    leanh::lean_inc_ref(v___y_2508_);
                    v___x_2551_ = leanh::lean_apply_6(
                        v_G_2507_,
                        v___x_2550_,
                        v_a_2548_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___y_2508_,
                        v_snd_2547_,
                    );
                    return v___x_2551_;
                }
            }
            6 => {
                v_a_2537_ = leanh::lean_ctor_get(v_a_2529_, 0);
                leanh::lean_inc(v_a_2537_);
                leanh::lean_dec_ref_known(v_a_2529_, 1);
                if v_isShared_2532_ == 0 {
                    leanh::lean_ctor_set(v___x_2531_, 0, v_a_2537_);
                    v___x_2539_ = v___x_2531_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2544_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2536_ == 0 {
                    leanh::lean_ctor_set(v___x_2535_, 0, v___x_2539_);
                    v___x_2541_ = v___x_2535_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_snd_2533_);
                    v___x_2541_ = v_reuseFailAlloc_2543_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2542_ = leanh::lean_apply_2(
                    v_toPure_2505_,
                    leanh::lean_box(0),
                    v___x_2541_,
                );
                return v___x_2542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(
    mut v_toPure_2553_: *mut leanh::LeanObject,
    mut v_next_2554_: *mut leanh::LeanObject,
    mut v_G_2555_: *mut leanh::LeanObject,
    mut v___y_2556_: *mut leanh::LeanObject,
    mut v_____x_2557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2558_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(
            v_toPure_2553_,
            v_next_2554_,
            v_G_2555_,
            v___y_2556_,
            v_____x_2557_,
        );
    leanh::lean_dec_ref(v___y_2556_);
    leanh::lean_dec(v_next_2554_);
    return v_res_2558_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(
    mut v_toPure_2559_: *mut leanh::LeanObject,
    mut v___f_2560_: *mut leanh::LeanObject,
    mut v___y_2561_: *mut leanh::LeanObject,
    mut v_____x_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_a_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v_unused_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2563_ = leanh::lean_ctor_get(v_____x_2562_, 0);
                leanh::lean_inc(v_fst_2563_);
                if leanh::lean_obj_tag(v_fst_2563_) == 0 {
                    leanh::lean_dec(v___f_2560_);
                    v_snd_2564_ = leanh::lean_ctor_get(v_____x_2562_, 1);
                    v_isSharedCheck_2580_ = (!leanh::lean_is_exclusive(v_____x_2562_)) as u8;
                    if v_isSharedCheck_2580_ == 0 {
                        v_unused_2581_ = leanh::lean_ctor_get(v_____x_2562_, 0);
                        leanh::lean_dec(v_unused_2581_);
                        v___x_2566_ = v_____x_2562_;
                        v_isShared_2567_ = v_isSharedCheck_2580_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2564_);
                        leanh::lean_dec(v_____x_2562_);
                        v___x_2566_ = leanh::lean_box(0);
                        v_isShared_2567_ = v_isSharedCheck_2580_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_toPure_2559_);
                    v_snd_2582_ = leanh::lean_ctor_get(v_____x_2562_, 1);
                    leanh::lean_inc(v_snd_2582_);
                    leanh::lean_dec_ref(v_____x_2562_);
                    v_a_2583_ = leanh::lean_ctor_get(v_fst_2563_, 0);
                    leanh::lean_inc(v_a_2583_);
                    leanh::lean_dec_ref_known(v_fst_2563_, 1);
                    leanh::lean_inc_ref(v___y_2561_);
                    v___x_2584_ = leanh::lean_apply_3(
                        v___f_2560_,
                        v_a_2583_,
                        v___y_2561_,
                        v_snd_2582_,
                    );
                    return v___x_2584_;
                }
            }
            1 => {
                v_a_2568_ = leanh::lean_ctor_get(v_fst_2563_, 0);
                v_isSharedCheck_2579_ = (!leanh::lean_is_exclusive(v_fst_2563_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v___x_2570_ = v_fst_2563_;
                    v_isShared_2571_ = v_isSharedCheck_2579_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2568_);
                    leanh::lean_dec(v_fst_2563_);
                    v___x_2570_ = leanh::lean_box(0);
                    v_isShared_2571_ = v_isSharedCheck_2579_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2571_ == 0 {
                    v___x_2573_ = v___x_2570_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2578_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2568_);
                    v___x_2573_ = v_reuseFailAlloc_2578_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2567_ == 0 {
                    leanh::lean_ctor_set(v___x_2566_, 0, v___x_2573_);
                    v___x_2575_ = v___x_2566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2573_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2564_);
                    v___x_2575_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2576_ = leanh::lean_apply_2(
                    v_toPure_2559_,
                    leanh::lean_box(0),
                    v___x_2575_,
                );
                return v___x_2576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(
    mut v_toPure_2585_: *mut leanh::LeanObject,
    mut v___f_2586_: *mut leanh::LeanObject,
    mut v___y_2587_: *mut leanh::LeanObject,
    mut v_____x_2588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2589_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(
            v_toPure_2585_,
            v___f_2586_,
            v___y_2587_,
            v_____x_2588_,
        );
    leanh::lean_dec_ref(v___y_2587_);
    return v_res_2589_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(
    mut v___x_2590_: *mut leanh::LeanObject,
    mut v_toPure_2591_: *mut leanh::LeanObject,
    mut v_toBind_2592_: *mut leanh::LeanObject,
    mut v___f_2593_: *mut leanh::LeanObject,
    mut v_initialMask_2594_: *mut leanh::LeanObject,
    mut v___f_2595_: *mut leanh::LeanObject,
    mut v_inst_2596_: *mut leanh::LeanObject,
    mut v___x_2597_: *mut leanh::LeanObject,
    mut v_next_2598_: *mut leanh::LeanObject,
    mut v_acc_2599_: *mut leanh::LeanObject,
    mut v_h_2600_: *mut leanh::LeanObject,
    mut v_G_2601_: *mut leanh::LeanObject,
    mut v___y_2602_: *mut leanh::LeanObject,
    mut v___y_2603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v___f_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ = lean_nat_dec_lt(v_next_2598_, v___x_2590_);
                if v___x_2604_ == 0 {
                    leanh::lean_dec(v_G_2601_);
                    leanh::lean_dec(v_next_2598_);
                    leanh::lean_dec_ref(v_inst_2596_);
                    leanh::lean_dec(v___f_2595_);
                    leanh::lean_dec(v___f_2593_);
                    leanh::lean_dec(v_toBind_2592_);
                    v___x_2605_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2605_, 0, v_acc_2599_);
                    v___x_2606_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2606_, 0, v___x_2605_);
                    leanh::lean_ctor_set(v___x_2606_, 1, v___y_2603_);
                    v___x_2607_ = leanh::lean_apply_2(
                        v_toPure_2591_,
                        leanh::lean_box(0),
                        v___x_2606_,
                    );
                    return v___x_2607_;
                } else {
                    leanh::lean_dec_ref(v_acc_2599_);
                    leanh::lean_inc_ref(v___y_2602_);
                    leanh::lean_inc(v_next_2598_);
                    leanh::lean_inc(v_toPure_2591_);
                    v___f_2608_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 4);
                    leanh::lean_closure_set(v___f_2608_, 0, v_toPure_2591_);
                    leanh::lean_closure_set(v___f_2608_, 1, v_next_2598_);
                    leanh::lean_closure_set(v___f_2608_, 2, v_G_2601_);
                    leanh::lean_closure_set(v___f_2608_, 3, v___y_2602_);
                    v___x_2613_ = lean_array_fget_borrowed(v_initialMask_2594_, v_next_2598_);
                    v___x_2614_ = (leanh::lean_unbox(v___x_2613_) as u8);
                    if v___x_2614_ == 0 {
                        leanh::lean_inc_ref(v___y_2602_);
                        v___f_2615_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed as *mut core::ffi::c_void, 4, 3);
                        leanh::lean_closure_set(v___f_2615_, 0, v_toPure_2591_);
                        leanh::lean_closure_set(v___f_2615_, 1, v___f_2595_);
                        leanh::lean_closure_set(v___f_2615_, 2, v___y_2602_);
                        v___x_2616_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_2598_, v_inst_2596_, v___y_2603_);
                        leanh::lean_inc(v_toBind_2592_);
                        v___x_2617_ = leanh::lean_apply_4(
                            v_toBind_2592_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___x_2616_,
                            v___f_2615_,
                        );
                        v___y_2610_ = v___x_2617_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_next_2598_);
                        leanh::lean_dec_ref(v_inst_2596_);
                        leanh::lean_dec(v_toPure_2591_);
                        leanh::lean_inc_ref(v___y_2602_);
                        v___x_2618_ = leanh::lean_apply_3(
                            v___f_2595_,
                            v___x_2597_,
                            v___y_2602_,
                            v___y_2603_,
                        );
                        v___y_2610_ = v___x_2618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_toBind_2592_);
                v___x_2611_ = leanh::lean_apply_4(
                    v_toBind_2592_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___y_2610_,
                    v___f_2593_,
                );
                v___x_2612_ = leanh::lean_apply_4(
                    v_toBind_2592_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_2611_,
                    v___f_2608_,
                );
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed(
    mut v___x_2619_: *mut leanh::LeanObject,
    mut v_toPure_2620_: *mut leanh::LeanObject,
    mut v_toBind_2621_: *mut leanh::LeanObject,
    mut v___f_2622_: *mut leanh::LeanObject,
    mut v_initialMask_2623_: *mut leanh::LeanObject,
    mut v___f_2624_: *mut leanh::LeanObject,
    mut v_inst_2625_: *mut leanh::LeanObject,
    mut v___x_2626_: *mut leanh::LeanObject,
    mut v_next_2627_: *mut leanh::LeanObject,
    mut v_acc_2628_: *mut leanh::LeanObject,
    mut v_h_2629_: *mut leanh::LeanObject,
    mut v_G_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
    mut v___y_2632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2633_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(
            v___x_2619_,
            v_toPure_2620_,
            v_toBind_2621_,
            v___f_2622_,
            v_initialMask_2623_,
            v___f_2624_,
            v_inst_2625_,
            v___x_2626_,
            v_next_2627_,
            v_acc_2628_,
            v_h_2629_,
            v_G_2630_,
            v___y_2631_,
            v___y_2632_,
        );
    leanh::lean_dec_ref(v___y_2631_);
    leanh::lean_dec_ref(v_initialMask_2623_);
    leanh::lean_dec(v___x_2619_);
    return v_res_2633_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(
    mut v_toPure_2637_: *mut leanh::LeanObject,
    mut v_inst_2638_: *mut leanh::LeanObject,
    mut v_toBind_2639_: *mut leanh::LeanObject,
    mut v___f_2640_: *mut leanh::LeanObject,
    mut v_a_2641_: *mut leanh::LeanObject,
    mut v_____x_2642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v_a_2648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2651_: u8 = 0;
    let mut v___x_2653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_unused_2661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initialMask_2664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6334__overap_2673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2643_ = leanh::lean_ctor_get(v_____x_2642_, 0);
                leanh::lean_inc(v_fst_2643_);
                if leanh::lean_obj_tag(v_fst_2643_) == 0 {
                    leanh::lean_dec(v___f_2640_);
                    leanh::lean_dec(v_toBind_2639_);
                    leanh::lean_dec_ref(v_inst_2638_);
                    v_snd_2644_ = leanh::lean_ctor_get(v_____x_2642_, 1);
                    v_isSharedCheck_2660_ = (!leanh::lean_is_exclusive(v_____x_2642_)) as u8;
                    if v_isSharedCheck_2660_ == 0 {
                        v_unused_2661_ = leanh::lean_ctor_get(v_____x_2642_, 0);
                        leanh::lean_dec(v_unused_2661_);
                        v___x_2646_ = v_____x_2642_;
                        v_isShared_2647_ = v_isSharedCheck_2660_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2644_);
                        leanh::lean_dec(v_____x_2642_);
                        v___x_2646_ = leanh::lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2660_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2662_ = leanh::lean_ctor_get(v_fst_2643_, 0);
                    leanh::lean_inc(v_a_2662_);
                    leanh::lean_dec_ref_known(v_fst_2643_, 1);
                    v_snd_2663_ = leanh::lean_ctor_get(v_____x_2642_, 1);
                    leanh::lean_inc(v_snd_2663_);
                    leanh::lean_dec_ref(v_____x_2642_);
                    v_initialMask_2664_ = leanh::lean_ctor_get(v_a_2662_, 0);
                    leanh::lean_inc_ref(v_initialMask_2664_);
                    leanh::lean_dec(v_a_2662_);
                    v___x_2665_ = lean_array_get_size(v_initialMask_2664_);
                    v___x_2666_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2667_ = leanh::lean_box(0);
                    leanh::lean_inc_n(v_toPure_2637_, 2);
                    v___f_2668_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
                    leanh::lean_closure_set(v___f_2668_, 0, v_toPure_2637_);
                    leanh::lean_closure_set(v___f_2668_, 1, v___x_2667_);
                    v___x_2669_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0;
                    v___f_2670_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2 as *mut core::ffi::c_void, 4, 3);
                    leanh::lean_closure_set(v___f_2670_, 0, v_toPure_2637_);
                    leanh::lean_closure_set(v___f_2670_, 1, v___x_2669_);
                    leanh::lean_closure_set(v___f_2670_, 2, v___x_2667_);
                    leanh::lean_inc_n(v_toBind_2639_, 2);
                    leanh::lean_inc_ref(v_inst_2638_);
                    v___f_2671_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                    leanh::lean_closure_set(v___f_2671_, 0, v_inst_2638_);
                    leanh::lean_closure_set(v___f_2671_, 1, v_toBind_2639_);
                    leanh::lean_closure_set(v___f_2671_, 2, v___f_2670_);
                    v___f_2672_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed as *mut core::ffi::c_void, 14, 8);
                    leanh::lean_closure_set(v___f_2672_, 0, v___x_2665_);
                    leanh::lean_closure_set(v___f_2672_, 1, v_toPure_2637_);
                    leanh::lean_closure_set(v___f_2672_, 2, v_toBind_2639_);
                    leanh::lean_closure_set(v___f_2672_, 3, v___f_2640_);
                    leanh::lean_closure_set(v___f_2672_, 4, v_initialMask_2664_);
                    leanh::lean_closure_set(v___f_2672_, 5, v___f_2671_);
                    leanh::lean_closure_set(v___f_2672_, 6, v_inst_2638_);
                    leanh::lean_closure_set(v___f_2672_, 7, v___x_2667_);
                    v___x_6334__overap_2673_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2672_,
                        v___x_2666_,
                        v___x_2669_,
                        leanh::lean_box(0),
                    );
                    leanh::lean_inc_ref(v_a_2641_);
                    v___x_2674_ = leanh::lean_apply_2(
                        v___x_6334__overap_2673_,
                        v_a_2641_,
                        v_snd_2663_,
                    );
                    v___x_2675_ = leanh::lean_apply_4(
                        v_toBind_2639_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2674_,
                        v___f_2668_,
                    );
                    return v___x_2675_;
                }
            }
            1 => {
                v_a_2648_ = leanh::lean_ctor_get(v_fst_2643_, 0);
                v_isSharedCheck_2659_ = (!leanh::lean_is_exclusive(v_fst_2643_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v___x_2650_ = v_fst_2643_;
                    v_isShared_2651_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2648_);
                    leanh::lean_dec(v_fst_2643_);
                    v___x_2650_ = leanh::lean_box(0);
                    v_isShared_2651_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2651_ == 0 {
                    v___x_2653_ = v___x_2650_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2658_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2648_);
                    v___x_2653_ = v_reuseFailAlloc_2658_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2647_ == 0 {
                    leanh::lean_ctor_set(v___x_2646_, 0, v___x_2653_);
                    v___x_2655_ = v___x_2646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2653_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_snd_2644_);
                    v___x_2655_ = v_reuseFailAlloc_2657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2656_ = leanh::lean_apply_2(
                    v_toPure_2637_,
                    leanh::lean_box(0),
                    v___x_2655_,
                );
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(
    mut v_toPure_2676_: *mut leanh::LeanObject,
    mut v_inst_2677_: *mut leanh::LeanObject,
    mut v_toBind_2678_: *mut leanh::LeanObject,
    mut v___f_2679_: *mut leanh::LeanObject,
    mut v_a_2680_: *mut leanh::LeanObject,
    mut v_____x_2681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2682_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(
            v_toPure_2676_,
            v_inst_2677_,
            v_toBind_2678_,
            v___f_2679_,
            v_a_2680_,
            v_____x_2681_,
        );
    leanh::lean_dec_ref(v_a_2680_);
    return v_res_2682_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
    mut v_inst_2683_: *mut leanh::LeanObject,
    mut v_a_2684_: *mut leanh::LeanObject,
    mut v_a_2685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_2686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_2687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_2688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_2686_ = leanh::lean_ctor_get(v_inst_2683_, 0);
    v_toBind_2687_ = leanh::lean_ctor_get(v_inst_2683_, 1);
    leanh::lean_inc_n(v_toBind_2687_, 2);
    v_toPure_2688_ = leanh::lean_ctor_get(v_toApplicative_2686_, 1);
    leanh::lean_inc_n(v_toPure_2688_, 3);
    v___f_2689_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_2689_, 0, v_toPure_2688_);
    leanh::lean_inc_ref_n(v_a_2684_, 2);
    v___f_2690_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 5);
    leanh::lean_closure_set(v___f_2690_, 0, v_toPure_2688_);
    leanh::lean_closure_set(v___f_2690_, 1, v_inst_2683_);
    leanh::lean_closure_set(v___f_2690_, 2, v_toBind_2687_);
    leanh::lean_closure_set(v___f_2690_, 3, v___f_2689_);
    leanh::lean_closure_set(v___f_2690_, 4, v_a_2684_);
    v___x_2691_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2691_, 0, v_a_2684_);
    v___x_2692_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2692_, 0, v___x_2691_);
    leanh::lean_ctor_set(v___x_2692_, 1, v_a_2685_);
    v___x_2693_ =
        leanh::lean_apply_2(v_toPure_2688_, leanh::lean_box(0), v___x_2692_);
    v___x_2694_ = leanh::lean_apply_4(
        v_toBind_2687_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_2693_,
        v___f_2690_,
    );
    return v___x_2694_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(
    mut v_inst_2695_: *mut leanh::LeanObject,
    mut v_a_2696_: *mut leanh::LeanObject,
    mut v_a_2697_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2698_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2698_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_2695_,
        v_a_2696_,
        v_a_2697_,
    );
    leanh::lean_dec_ref(v_a_2696_);
    return v_res_2698_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(
    mut v_m_2699_: *mut leanh::LeanObject,
    mut v_inst_2700_: *mut leanh::LeanObject,
    mut v_a_2701_: *mut leanh::LeanObject,
    mut v_a_2702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2703_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_2700_,
        v_a_2701_,
        v_a_2702_,
    );
    return v___x_2703_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(
    mut v_m_2704_: *mut leanh::LeanObject,
    mut v_inst_2705_: *mut leanh::LeanObject,
    mut v_a_2706_: *mut leanh::LeanObject,
    mut v_a_2707_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2708_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(
        v_m_2704_,
        v_inst_2705_,
        v_a_2706_,
        v_a_2707_,
    );
    leanh::lean_dec_ref(v_a_2706_);
    return v_res_2708_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(
    mut v_toPure_2711_: *mut leanh::LeanObject,
    mut v_____x_2712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v_a_2718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v___x_2723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_unused_2731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut v_unused_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2713_ = leanh::lean_ctor_get(v_____x_2712_, 0);
                leanh::lean_inc(v_fst_2713_);
                if leanh::lean_obj_tag(v_fst_2713_) == 0 {
                    v_snd_2714_ = leanh::lean_ctor_get(v_____x_2712_, 1);
                    v_isSharedCheck_2730_ = (!leanh::lean_is_exclusive(v_____x_2712_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v_unused_2731_ = leanh::lean_ctor_get(v_____x_2712_, 0);
                        leanh::lean_dec(v_unused_2731_);
                        v___x_2716_ = v_____x_2712_;
                        v_isShared_2717_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2714_);
                        leanh::lean_dec(v_____x_2712_);
                        v___x_2716_ = leanh::lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_fst_2713_, 1);
                    v_snd_2732_ = leanh::lean_ctor_get(v_____x_2712_, 1);
                    v_isSharedCheck_2741_ = (!leanh::lean_is_exclusive(v_____x_2712_)) as u8;
                    if v_isSharedCheck_2741_ == 0 {
                        v_unused_2742_ = leanh::lean_ctor_get(v_____x_2712_, 0);
                        leanh::lean_dec(v_unused_2742_);
                        v___x_2734_ = v_____x_2712_;
                        v_isShared_2735_ = v_isSharedCheck_2741_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2732_);
                        leanh::lean_dec(v_____x_2712_);
                        v___x_2734_ = leanh::lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2741_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2718_ = leanh::lean_ctor_get(v_fst_2713_, 0);
                v_isSharedCheck_2729_ = (!leanh::lean_is_exclusive(v_fst_2713_)) as u8;
                if v_isSharedCheck_2729_ == 0 {
                    v___x_2720_ = v_fst_2713_;
                    v_isShared_2721_ = v_isSharedCheck_2729_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2718_);
                    leanh::lean_dec(v_fst_2713_);
                    v___x_2720_ = leanh::lean_box(0);
                    v_isShared_2721_ = v_isSharedCheck_2729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2721_ == 0 {
                    v___x_2723_ = v___x_2720_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2728_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2718_);
                    v___x_2723_ = v_reuseFailAlloc_2728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2717_ == 0 {
                    leanh::lean_ctor_set(v___x_2716_, 0, v___x_2723_);
                    v___x_2725_ = v___x_2716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2723_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_snd_2714_);
                    v___x_2725_ = v_reuseFailAlloc_2727_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2726_ = leanh::lean_apply_2(
                    v_toPure_2711_,
                    leanh::lean_box(0),
                    v___x_2725_,
                );
                return v___x_2726_;
            }
            5 => {
                v___x_2736_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0;
                if v_isShared_2735_ == 0 {
                    leanh::lean_ctor_set(v___x_2734_, 0, v___x_2736_);
                    v___x_2738_ = v___x_2734_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2736_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_snd_2732_);
                    v___x_2738_ = v_reuseFailAlloc_2740_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2739_ = leanh::lean_apply_2(
                    v_toPure_2711_,
                    leanh::lean_box(0),
                    v___x_2738_,
                );
                return v___x_2739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(
    mut v_toPure_2743_: *mut leanh::LeanObject,
    mut v_____x_2744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v_a_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v___x_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_unused_2763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v_snd_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v_a_2772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2786_: u8 = 0;
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v_a_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v___x_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v_unused_2809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2745_ = leanh::lean_ctor_get(v_____x_2744_, 0);
                leanh::lean_inc(v_fst_2745_);
                if leanh::lean_obj_tag(v_fst_2745_) == 0 {
                    v_snd_2746_ = leanh::lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2762_ = (!leanh::lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v_unused_2763_ = leanh::lean_ctor_get(v_____x_2744_, 0);
                        leanh::lean_dec(v_unused_2763_);
                        v___x_2748_ = v_____x_2744_;
                        v_isShared_2749_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2746_);
                        leanh::lean_dec(v_____x_2744_);
                        v___x_2748_ = leanh::lean_box(0);
                        v_isShared_2749_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2764_ = leanh::lean_ctor_get(v_fst_2745_, 0);
                    v_isSharedCheck_2810_ = (!leanh::lean_is_exclusive(v_fst_2745_)) as u8;
                    if v_isSharedCheck_2810_ == 0 {
                        v___x_2766_ = v_fst_2745_;
                        v_isShared_2767_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2764_);
                        leanh::lean_dec(v_fst_2745_);
                        v___x_2766_ = leanh::lean_box(0);
                        v_isShared_2767_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2750_ = leanh::lean_ctor_get(v_fst_2745_, 0);
                v_isSharedCheck_2761_ = (!leanh::lean_is_exclusive(v_fst_2745_)) as u8;
                if v_isSharedCheck_2761_ == 0 {
                    v___x_2752_ = v_fst_2745_;
                    v_isShared_2753_ = v_isSharedCheck_2761_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2750_);
                    leanh::lean_dec(v_fst_2745_);
                    v___x_2752_ = leanh::lean_box(0);
                    v_isShared_2753_ = v_isSharedCheck_2761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2753_ == 0 {
                    v___x_2755_ = v___x_2752_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2750_);
                    v___x_2755_ = v_reuseFailAlloc_2760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2749_ == 0 {
                    leanh::lean_ctor_set(v___x_2748_, 0, v___x_2755_);
                    v___x_2757_ = v___x_2748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_snd_2746_);
                    v___x_2757_ = v_reuseFailAlloc_2759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2758_ = leanh::lean_apply_2(
                    v_toPure_2743_,
                    leanh::lean_box(0),
                    v___x_2757_,
                );
                return v___x_2758_;
            }
            5 => {
                if leanh::lean_obj_tag(v_a_2764_) == 0 {
                    v_snd_2768_ = leanh::lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2787_ = (!leanh::lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v_unused_2788_ = leanh::lean_ctor_get(v_____x_2744_, 0);
                        leanh::lean_dec(v_unused_2788_);
                        v___x_2770_ = v_____x_2744_;
                        v_isShared_2771_ = v_isSharedCheck_2787_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2768_);
                        leanh::lean_dec(v_____x_2744_);
                        v___x_2770_ = leanh::lean_box(0);
                        v_isShared_2771_ = v_isSharedCheck_2787_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_snd_2789_ = leanh::lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2808_ = (!leanh::lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2808_ == 0 {
                        v_unused_2809_ = leanh::lean_ctor_get(v_____x_2744_, 0);
                        leanh::lean_dec(v_unused_2809_);
                        v___x_2791_ = v_____x_2744_;
                        v_isShared_2792_ = v_isSharedCheck_2808_;
                        state = 11;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2789_);
                        leanh::lean_dec(v_____x_2744_);
                        v___x_2791_ = leanh::lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2808_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v_a_2772_ = leanh::lean_ctor_get(v_a_2764_, 0);
                v_isSharedCheck_2786_ = (!leanh::lean_is_exclusive(v_a_2764_)) as u8;
                if v_isSharedCheck_2786_ == 0 {
                    v___x_2774_ = v_a_2764_;
                    v_isShared_2775_ = v_isSharedCheck_2786_;
                    state = 7;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2772_);
                    leanh::lean_dec(v_a_2764_);
                    v___x_2774_ = leanh::lean_box(0);
                    v_isShared_2775_ = v_isSharedCheck_2786_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2775_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2774_, 1);
                    v___x_2777_ = v___x_2774_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2785_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2785_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2767_ == 0 {
                    leanh::lean_ctor_set(v___x_2766_, 0, v___x_2777_);
                    v___x_2779_ = v___x_2766_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2777_);
                    v___x_2779_ = v_reuseFailAlloc_2784_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2771_ == 0 {
                    leanh::lean_ctor_set(v___x_2770_, 0, v___x_2779_);
                    v___x_2781_ = v___x_2770_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_snd_2768_);
                    v___x_2781_ = v_reuseFailAlloc_2783_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2782_ = leanh::lean_apply_2(
                    v_toPure_2743_,
                    leanh::lean_box(0),
                    v___x_2781_,
                );
                return v___x_2782_;
            }
            11 => {
                v_a_2793_ = leanh::lean_ctor_get(v_a_2764_, 0);
                v_isSharedCheck_2807_ = (!leanh::lean_is_exclusive(v_a_2764_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2795_ = v_a_2764_;
                    v_isShared_2796_ = v_isSharedCheck_2807_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2793_);
                    leanh::lean_dec(v_a_2764_);
                    v___x_2795_ = leanh::lean_box(0);
                    v_isShared_2796_ = v_isSharedCheck_2807_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2796_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2795_, 0);
                    v___x_2798_ = v___x_2795_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2793_);
                    v___x_2798_ = v_reuseFailAlloc_2806_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2767_ == 0 {
                    leanh::lean_ctor_set(v___x_2766_, 0, v___x_2798_);
                    v___x_2800_ = v___x_2766_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2798_);
                    v___x_2800_ = v_reuseFailAlloc_2805_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2792_ == 0 {
                    leanh::lean_ctor_set(v___x_2791_, 0, v___x_2800_);
                    v___x_2802_ = v___x_2791_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2800_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_snd_2789_);
                    v___x_2802_ = v_reuseFailAlloc_2804_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2803_ = leanh::lean_apply_2(
                    v_toPure_2743_,
                    leanh::lean_box(0),
                    v___x_2802_,
                );
                return v___x_2803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(
    mut v_toPure_2811_: *mut leanh::LeanObject,
    mut v___x_2812_: *mut leanh::LeanObject,
    mut v_____x_2813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v_a_2819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v_unused_2832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2814_ = leanh::lean_ctor_get(v_____x_2813_, 0);
                leanh::lean_inc(v_fst_2814_);
                if leanh::lean_obj_tag(v_fst_2814_) == 0 {
                    leanh::lean_dec(v___x_2812_);
                    v_snd_2815_ = leanh::lean_ctor_get(v_____x_2813_, 1);
                    v_isSharedCheck_2831_ = (!leanh::lean_is_exclusive(v_____x_2813_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v_unused_2832_ = leanh::lean_ctor_get(v_____x_2813_, 0);
                        leanh::lean_dec(v_unused_2832_);
                        v___x_2817_ = v_____x_2813_;
                        v_isShared_2818_ = v_isSharedCheck_2831_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2815_);
                        leanh::lean_dec(v_____x_2813_);
                        v___x_2817_ = leanh::lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2833_ = leanh::lean_ctor_get(v_____x_2813_, 1);
                    v_isSharedCheck_2850_ = (!leanh::lean_is_exclusive(v_____x_2813_)) as u8;
                    if v_isSharedCheck_2850_ == 0 {
                        v_unused_2851_ = leanh::lean_ctor_get(v_____x_2813_, 0);
                        leanh::lean_dec(v_unused_2851_);
                        v___x_2835_ = v_____x_2813_;
                        v_isShared_2836_ = v_isSharedCheck_2850_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2833_);
                        leanh::lean_dec(v_____x_2813_);
                        v___x_2835_ = leanh::lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2850_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2819_ = leanh::lean_ctor_get(v_fst_2814_, 0);
                v_isSharedCheck_2830_ = (!leanh::lean_is_exclusive(v_fst_2814_)) as u8;
                if v_isSharedCheck_2830_ == 0 {
                    v___x_2821_ = v_fst_2814_;
                    v_isShared_2822_ = v_isSharedCheck_2830_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2819_);
                    leanh::lean_dec(v_fst_2814_);
                    v___x_2821_ = leanh::lean_box(0);
                    v_isShared_2822_ = v_isSharedCheck_2830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2822_ == 0 {
                    v___x_2824_ = v___x_2821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2829_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2829_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2818_ == 0 {
                    leanh::lean_ctor_set(v___x_2817_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2824_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2815_);
                    v___x_2826_ = v_reuseFailAlloc_2828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2827_ = leanh::lean_apply_2(
                    v_toPure_2811_,
                    leanh::lean_box(0),
                    v___x_2826_,
                );
                return v___x_2827_;
            }
            5 => {
                v_isSharedCheck_2848_ = (!leanh::lean_is_exclusive(v_fst_2814_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v_unused_2849_ = leanh::lean_ctor_get(v_fst_2814_, 0);
                    leanh::lean_dec(v_unused_2849_);
                    v___x_2838_ = v_fst_2814_;
                    v_isShared_2839_ = v_isSharedCheck_2848_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_2814_);
                    v___x_2838_ = leanh::lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2848_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2840_, 0, v___x_2812_);
                if v_isShared_2839_ == 0 {
                    leanh::lean_ctor_set(v___x_2838_, 0, v___x_2840_);
                    v___x_2842_ = v___x_2838_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2840_);
                    v___x_2842_ = v_reuseFailAlloc_2847_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2836_ == 0 {
                    leanh::lean_ctor_set(v___x_2835_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2835_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2842_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_snd_2833_);
                    v___x_2844_ = v_reuseFailAlloc_2846_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2845_ = leanh::lean_apply_2(
                    v_toPure_2811_,
                    leanh::lean_box(0),
                    v___x_2844_,
                );
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(
    mut v_toPure_2852_: *mut leanh::LeanObject,
    mut v___x_2853_: *mut leanh::LeanObject,
    mut v_inst_2854_: *mut leanh::LeanObject,
    mut v_toBind_2855_: *mut leanh::LeanObject,
    mut v___f_2856_: *mut leanh::LeanObject,
    mut v___x_2857_: *mut leanh::LeanObject,
    mut v_____x_2858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_a_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2867_: u8 = 0;
    let mut v___x_2869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: u8 = 0;
    let mut v_snd_2883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut v_unused_2899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2859_ = leanh::lean_ctor_get(v_____x_2858_, 0);
                leanh::lean_inc(v_fst_2859_);
                if leanh::lean_obj_tag(v_fst_2859_) == 0 {
                    leanh::lean_dec(v___x_2857_);
                    leanh::lean_dec(v___f_2856_);
                    leanh::lean_dec(v_toBind_2855_);
                    leanh::lean_dec_ref(v_inst_2854_);
                    v_snd_2860_ = leanh::lean_ctor_get(v_____x_2858_, 1);
                    v_isSharedCheck_2876_ = (!leanh::lean_is_exclusive(v_____x_2858_)) as u8;
                    if v_isSharedCheck_2876_ == 0 {
                        v_unused_2877_ = leanh::lean_ctor_get(v_____x_2858_, 0);
                        leanh::lean_dec(v_unused_2877_);
                        v___x_2862_ = v_____x_2858_;
                        v_isShared_2863_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2860_);
                        leanh::lean_dec(v_____x_2858_);
                        v___x_2862_ = leanh::lean_box(0);
                        v_isShared_2863_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2878_ = leanh::lean_ctor_get(v_fst_2859_, 0);
                    v_isSharedCheck_2900_ = (!leanh::lean_is_exclusive(v_fst_2859_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2880_ = v_fst_2859_;
                        v_isShared_2881_ = v_isSharedCheck_2900_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2878_);
                        leanh::lean_dec(v_fst_2859_);
                        v___x_2880_ = leanh::lean_box(0);
                        v_isShared_2881_ = v_isSharedCheck_2900_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2864_ = leanh::lean_ctor_get(v_fst_2859_, 0);
                v_isSharedCheck_2875_ = (!leanh::lean_is_exclusive(v_fst_2859_)) as u8;
                if v_isSharedCheck_2875_ == 0 {
                    v___x_2866_ = v_fst_2859_;
                    v_isShared_2867_ = v_isSharedCheck_2875_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2864_);
                    leanh::lean_dec(v_fst_2859_);
                    v___x_2866_ = leanh::lean_box(0);
                    v_isShared_2867_ = v_isSharedCheck_2875_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2867_ == 0 {
                    v___x_2869_ = v___x_2866_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2874_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2864_);
                    v___x_2869_ = v_reuseFailAlloc_2874_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2863_ == 0 {
                    leanh::lean_ctor_set(v___x_2862_, 0, v___x_2869_);
                    v___x_2871_ = v___x_2862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2873_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2869_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2860_);
                    v___x_2871_ = v_reuseFailAlloc_2873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2872_ = leanh::lean_apply_2(
                    v_toPure_2852_,
                    leanh::lean_box(0),
                    v___x_2871_,
                );
                return v___x_2872_;
            }
            5 => {
                v___x_2882_ = (leanh::lean_unbox(v_a_2878_) as u8);
                leanh::lean_dec(v_a_2878_);
                if v___x_2882_ == 0 {
                    leanh::lean_del_object(v___x_2880_);
                    leanh::lean_dec(v___x_2857_);
                    leanh::lean_dec(v_toPure_2852_);
                    v_snd_2883_ = leanh::lean_ctor_get(v_____x_2858_, 1);
                    leanh::lean_inc(v_snd_2883_);
                    leanh::lean_dec_ref(v_____x_2858_);
                    v___x_2884_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_2853_, v_inst_2854_, v_snd_2883_);
                    v___x_2885_ = leanh::lean_apply_4(
                        v_toBind_2855_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2884_,
                        v___f_2856_,
                    );
                    return v___x_2885_;
                } else {
                    leanh::lean_dec(v___f_2856_);
                    leanh::lean_dec(v_toBind_2855_);
                    leanh::lean_dec_ref(v_inst_2854_);
                    v_snd_2886_ = leanh::lean_ctor_get(v_____x_2858_, 1);
                    v_isSharedCheck_2898_ = (!leanh::lean_is_exclusive(v_____x_2858_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v_unused_2899_ = leanh::lean_ctor_get(v_____x_2858_, 0);
                        leanh::lean_dec(v_unused_2899_);
                        v___x_2888_ = v_____x_2858_;
                        v_isShared_2889_ = v_isSharedCheck_2898_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2886_);
                        leanh::lean_dec(v_____x_2858_);
                        v___x_2888_ = leanh::lean_box(0);
                        v_isShared_2889_ = v_isSharedCheck_2898_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2890_, 0, v___x_2857_);
                if v_isShared_2881_ == 0 {
                    leanh::lean_ctor_set(v___x_2880_, 0, v___x_2890_);
                    v___x_2892_ = v___x_2880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2890_);
                    v___x_2892_ = v_reuseFailAlloc_2897_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2889_ == 0 {
                    leanh::lean_ctor_set(v___x_2888_, 0, v___x_2892_);
                    v___x_2894_ = v___x_2888_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2892_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_snd_2886_);
                    v___x_2894_ = v_reuseFailAlloc_2896_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2895_ = leanh::lean_apply_2(
                    v_toPure_2852_,
                    leanh::lean_box(0),
                    v___x_2894_,
                );
                return v___x_2895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(
    mut v_toPure_2901_: *mut leanh::LeanObject,
    mut v___x_2902_: *mut leanh::LeanObject,
    mut v_inst_2903_: *mut leanh::LeanObject,
    mut v_toBind_2904_: *mut leanh::LeanObject,
    mut v___f_2905_: *mut leanh::LeanObject,
    mut v___x_2906_: *mut leanh::LeanObject,
    mut v_____x_2907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2908_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(
            v_toPure_2901_,
            v___x_2902_,
            v_inst_2903_,
            v_toBind_2904_,
            v___f_2905_,
            v___x_2906_,
            v_____x_2907_,
        );
    leanh::lean_dec(v___x_2902_);
    return v_res_2908_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(
    mut v_toPure_2909_: *mut leanh::LeanObject,
    mut v_inst_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
    mut v_toBind_2912_: *mut leanh::LeanObject,
    mut v___f_2913_: *mut leanh::LeanObject,
    mut v_____x_2914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v_a_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_unused_2933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2915_ = leanh::lean_ctor_get(v_____x_2914_, 0);
                leanh::lean_inc(v_fst_2915_);
                if leanh::lean_obj_tag(v_fst_2915_) == 0 {
                    leanh::lean_dec(v___f_2913_);
                    leanh::lean_dec(v_toBind_2912_);
                    leanh::lean_dec_ref(v_inst_2910_);
                    v_snd_2916_ = leanh::lean_ctor_get(v_____x_2914_, 1);
                    v_isSharedCheck_2932_ = (!leanh::lean_is_exclusive(v_____x_2914_)) as u8;
                    if v_isSharedCheck_2932_ == 0 {
                        v_unused_2933_ = leanh::lean_ctor_get(v_____x_2914_, 0);
                        leanh::lean_dec(v_unused_2933_);
                        v___x_2918_ = v_____x_2914_;
                        v_isShared_2919_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2916_);
                        leanh::lean_dec(v_____x_2914_);
                        v___x_2918_ = leanh::lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_fst_2915_, 1);
                    leanh::lean_dec(v_toPure_2909_);
                    v_snd_2934_ = leanh::lean_ctor_get(v_____x_2914_, 1);
                    leanh::lean_inc(v_snd_2934_);
                    leanh::lean_dec_ref(v_____x_2914_);
                    v___x_2935_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_2910_, v___y_2911_, v_snd_2934_);
                    v___x_2936_ = leanh::lean_apply_4(
                        v_toBind_2912_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2935_,
                        v___f_2913_,
                    );
                    return v___x_2936_;
                }
            }
            1 => {
                v_a_2920_ = leanh::lean_ctor_get(v_fst_2915_, 0);
                v_isSharedCheck_2931_ = (!leanh::lean_is_exclusive(v_fst_2915_)) as u8;
                if v_isSharedCheck_2931_ == 0 {
                    v___x_2922_ = v_fst_2915_;
                    v_isShared_2923_ = v_isSharedCheck_2931_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2920_);
                    leanh::lean_dec(v_fst_2915_);
                    v___x_2922_ = leanh::lean_box(0);
                    v_isShared_2923_ = v_isSharedCheck_2931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2923_ == 0 {
                    v___x_2925_ = v___x_2922_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2930_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2920_);
                    v___x_2925_ = v_reuseFailAlloc_2930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2919_ == 0 {
                    leanh::lean_ctor_set(v___x_2918_, 0, v___x_2925_);
                    v___x_2927_ = v___x_2918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_snd_2916_);
                    v___x_2927_ = v_reuseFailAlloc_2929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2928_ = leanh::lean_apply_2(
                    v_toPure_2909_,
                    leanh::lean_box(0),
                    v___x_2927_,
                );
                return v___x_2928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(
    mut v_toPure_2937_: *mut leanh::LeanObject,
    mut v_inst_2938_: *mut leanh::LeanObject,
    mut v___y_2939_: *mut leanh::LeanObject,
    mut v_toBind_2940_: *mut leanh::LeanObject,
    mut v___f_2941_: *mut leanh::LeanObject,
    mut v_____x_2942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2943_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(
            v_toPure_2937_,
            v_inst_2938_,
            v___y_2939_,
            v_toBind_2940_,
            v___f_2941_,
            v_____x_2942_,
        );
    leanh::lean_dec_ref(v___y_2939_);
    return v_res_2943_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(
    mut v_toPure_2944_: *mut leanh::LeanObject,
    mut v___x_2945_: *mut leanh::LeanObject,
    mut v_inst_2946_: *mut leanh::LeanObject,
    mut v_toBind_2947_: *mut leanh::LeanObject,
    mut v___f_2948_: *mut leanh::LeanObject,
    mut v___y_2949_: *mut leanh::LeanObject,
    mut v_____x_2950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v_a_2956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_2972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2951_ = leanh::lean_ctor_get(v_____x_2950_, 0);
                leanh::lean_inc(v_fst_2951_);
                if leanh::lean_obj_tag(v_fst_2951_) == 0 {
                    leanh::lean_dec(v___f_2948_);
                    leanh::lean_dec(v_toBind_2947_);
                    leanh::lean_dec_ref(v_inst_2946_);
                    leanh::lean_dec(v___x_2945_);
                    v_snd_2952_ = leanh::lean_ctor_get(v_____x_2950_, 1);
                    v_isSharedCheck_2968_ = (!leanh::lean_is_exclusive(v_____x_2950_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v_unused_2969_ = leanh::lean_ctor_get(v_____x_2950_, 0);
                        leanh::lean_dec(v_unused_2969_);
                        v___x_2954_ = v_____x_2950_;
                        v_isShared_2955_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_2952_);
                        leanh::lean_dec(v_____x_2950_);
                        v___x_2954_ = leanh::lean_box(0);
                        v_isShared_2955_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2970_ = leanh::lean_ctor_get(v_fst_2951_, 0);
                    leanh::lean_inc(v_a_2970_);
                    leanh::lean_dec_ref_known(v_fst_2951_, 1);
                    v_snd_2971_ = leanh::lean_ctor_get(v_____x_2950_, 1);
                    leanh::lean_inc(v_snd_2971_);
                    leanh::lean_dec_ref(v_____x_2950_);
                    v_added_2972_ = leanh::lean_ctor_get(v_a_2970_, 1);
                    leanh::lean_inc_ref(v_added_2972_);
                    leanh::lean_dec(v_a_2970_);
                    v___x_2973_ = leanh::lean_unsigned_to_nat(0);
                    v___x_2974_ = lean_array_get(v___x_2973_, v_added_2972_, v___x_2945_);
                    leanh::lean_dec_ref(v_added_2972_);
                    leanh::lean_inc_n(v_toBind_2947_, 2);
                    leanh::lean_inc_ref_n(v_inst_2946_, 2);
                    leanh::lean_inc(v___x_2974_);
                    leanh::lean_inc(v_toPure_2944_);
                    v___f_2975_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed as *mut core::ffi::c_void, 7, 6);
                    leanh::lean_closure_set(v___f_2975_, 0, v_toPure_2944_);
                    leanh::lean_closure_set(v___f_2975_, 1, v___x_2974_);
                    leanh::lean_closure_set(v___f_2975_, 2, v_inst_2946_);
                    leanh::lean_closure_set(v___f_2975_, 3, v_toBind_2947_);
                    leanh::lean_closure_set(v___f_2975_, 4, v___f_2948_);
                    leanh::lean_closure_set(v___f_2975_, 5, v___x_2945_);
                    leanh::lean_inc_ref(v___y_2949_);
                    v___f_2976_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 5);
                    leanh::lean_closure_set(v___f_2976_, 0, v_toPure_2944_);
                    leanh::lean_closure_set(v___f_2976_, 1, v_inst_2946_);
                    leanh::lean_closure_set(v___f_2976_, 2, v___y_2949_);
                    leanh::lean_closure_set(v___f_2976_, 3, v_toBind_2947_);
                    leanh::lean_closure_set(v___f_2976_, 4, v___f_2975_);
                    v___x_2977_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_2974_, v_inst_2946_, v_snd_2971_);
                    leanh::lean_dec(v___x_2974_);
                    v___x_2978_ = leanh::lean_apply_4(
                        v_toBind_2947_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_2977_,
                        v___f_2976_,
                    );
                    return v___x_2978_;
                }
            }
            1 => {
                v_a_2956_ = leanh::lean_ctor_get(v_fst_2951_, 0);
                v_isSharedCheck_2967_ = (!leanh::lean_is_exclusive(v_fst_2951_)) as u8;
                if v_isSharedCheck_2967_ == 0 {
                    v___x_2958_ = v_fst_2951_;
                    v_isShared_2959_ = v_isSharedCheck_2967_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2956_);
                    leanh::lean_dec(v_fst_2951_);
                    v___x_2958_ = leanh::lean_box(0);
                    v_isShared_2959_ = v_isSharedCheck_2967_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2959_ == 0 {
                    v___x_2961_ = v___x_2958_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2956_);
                    v___x_2961_ = v_reuseFailAlloc_2966_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2955_ == 0 {
                    leanh::lean_ctor_set(v___x_2954_, 0, v___x_2961_);
                    v___x_2963_ = v___x_2954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2965_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2961_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2952_);
                    v___x_2963_ = v_reuseFailAlloc_2965_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2964_ = leanh::lean_apply_2(
                    v_toPure_2944_,
                    leanh::lean_box(0),
                    v___x_2963_,
                );
                return v___x_2964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(
    mut v_toPure_2979_: *mut leanh::LeanObject,
    mut v___x_2980_: *mut leanh::LeanObject,
    mut v_inst_2981_: *mut leanh::LeanObject,
    mut v_toBind_2982_: *mut leanh::LeanObject,
    mut v___f_2983_: *mut leanh::LeanObject,
    mut v___y_2984_: *mut leanh::LeanObject,
    mut v_____x_2985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2986_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2986_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(
            v_toPure_2979_,
            v___x_2980_,
            v_inst_2981_,
            v_toBind_2982_,
            v___f_2983_,
            v___y_2984_,
            v_____x_2985_,
        );
    leanh::lean_dec_ref(v___y_2984_);
    return v_res_2986_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(
    mut v_toPure_2987_: *mut leanh::LeanObject,
    mut v_toBind_2988_: *mut leanh::LeanObject,
    mut v___f_2989_: *mut leanh::LeanObject,
    mut v___x_2990_: *mut leanh::LeanObject,
    mut v_inst_2991_: *mut leanh::LeanObject,
    mut v_b_2992_: *mut leanh::LeanObject,
    mut v___y_2993_: *mut leanh::LeanObject,
    mut v___y_2994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    v___x_2995_ = leanh::lean_unsigned_to_nat(0);
    v___x_2996_ = lean_nat_dec_lt(v___x_2995_, v_b_2992_);
    if v___x_2996_ == 0 {
        let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2999_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_inst_2991_);
        v___x_2997_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2997_, 0, v_b_2992_);
        v___x_2998_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_2998_, 0, v___x_2997_);
        v___x_2999_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_2999_, 0, v___x_2998_);
        leanh::lean_ctor_set(v___x_2999_, 1, v___y_2994_);
        v___x_3000_ =
            leanh::lean_apply_2(v_toPure_2987_, leanh::lean_box(0), v___x_2999_);
        v___x_3001_ = leanh::lean_apply_4(
            v_toBind_2988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3000_,
            v___f_2989_,
        );
        return v___x_3001_;
    } else {
        let mut v___x_3002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3010_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3002_ = lean_nat_sub(v_b_2992_, v___x_2990_);
        leanh::lean_dec(v_b_2992_);
        leanh::lean_inc(v___x_3002_);
        leanh::lean_inc_n(v_toPure_2987_, 3);
        v___f_3003_ = leanh::lean_alloc_closure(
            l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2
                as *mut core::ffi::c_void,
            3,
            2,
        );
        leanh::lean_closure_set(v___f_3003_, 0, v_toPure_2987_);
        leanh::lean_closure_set(v___f_3003_, 1, v___x_3002_);
        leanh::lean_inc_ref(v___y_2993_);
        leanh::lean_inc_n(v_toBind_2988_, 3);
        v___f_3004_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed as *mut core::ffi::c_void, 7, 6);
        leanh::lean_closure_set(v___f_3004_, 0, v_toPure_2987_);
        leanh::lean_closure_set(v___f_3004_, 1, v___x_3002_);
        leanh::lean_closure_set(v___f_3004_, 2, v_inst_2991_);
        leanh::lean_closure_set(v___f_3004_, 3, v_toBind_2988_);
        leanh::lean_closure_set(v___f_3004_, 4, v___f_3003_);
        leanh::lean_closure_set(v___f_3004_, 5, v___y_2993_);
        v___f_3005_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
        leanh::lean_closure_set(v___f_3005_, 0, v_toPure_2987_);
        leanh::lean_inc_ref(v___y_2994_);
        v___x_3006_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_3006_, 0, v___y_2994_);
        leanh::lean_ctor_set(v___x_3006_, 1, v___y_2994_);
        v___x_3007_ =
            leanh::lean_apply_2(v_toPure_2987_, leanh::lean_box(0), v___x_3006_);
        v___x_3008_ = leanh::lean_apply_4(
            v_toBind_2988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3007_,
            v___f_3005_,
        );
        v___x_3009_ = leanh::lean_apply_4(
            v_toBind_2988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3008_,
            v___f_3004_,
        );
        v___x_3010_ = leanh::lean_apply_4(
            v_toBind_2988_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3009_,
            v___f_2989_,
        );
        return v___x_3010_;
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(
    mut v_toPure_3011_: *mut leanh::LeanObject,
    mut v_toBind_3012_: *mut leanh::LeanObject,
    mut v___f_3013_: *mut leanh::LeanObject,
    mut v___x_3014_: *mut leanh::LeanObject,
    mut v_inst_3015_: *mut leanh::LeanObject,
    mut v_b_3016_: *mut leanh::LeanObject,
    mut v___y_3017_: *mut leanh::LeanObject,
    mut v___y_3018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3019_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(
            v_toPure_3011_,
            v_toBind_3012_,
            v___f_3013_,
            v___x_3014_,
            v_inst_3015_,
            v_b_3016_,
            v___y_3017_,
            v___y_3018_,
        );
    leanh::lean_dec_ref(v___y_3017_);
    leanh::lean_dec(v___x_3014_);
    return v_res_3019_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(
    mut v_toPure_3020_: *mut leanh::LeanObject,
    mut v_toBind_3021_: *mut leanh::LeanObject,
    mut v___f_3022_: *mut leanh::LeanObject,
    mut v_inst_3023_: *mut leanh::LeanObject,
    mut v___x_3024_: *mut leanh::LeanObject,
    mut v_a_3025_: *mut leanh::LeanObject,
    mut v___f_3026_: *mut leanh::LeanObject,
    mut v_____x_3027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3032_: u8 = 0;
    let mut v_a_3033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v___x_3038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_unused_3046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_added_3049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143__overap_3054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3028_ = leanh::lean_ctor_get(v_____x_3027_, 0);
                leanh::lean_inc(v_fst_3028_);
                if leanh::lean_obj_tag(v_fst_3028_) == 0 {
                    leanh::lean_dec(v___f_3026_);
                    leanh::lean_dec_ref(v___x_3024_);
                    leanh::lean_dec_ref(v_inst_3023_);
                    leanh::lean_dec(v___f_3022_);
                    leanh::lean_dec(v_toBind_3021_);
                    v_snd_3029_ = leanh::lean_ctor_get(v_____x_3027_, 1);
                    v_isSharedCheck_3045_ = (!leanh::lean_is_exclusive(v_____x_3027_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v_unused_3046_ = leanh::lean_ctor_get(v_____x_3027_, 0);
                        leanh::lean_dec(v_unused_3046_);
                        v___x_3031_ = v_____x_3027_;
                        v_isShared_3032_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3029_);
                        leanh::lean_dec(v_____x_3027_);
                        v___x_3031_ = leanh::lean_box(0);
                        v_isShared_3032_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3047_ = leanh::lean_ctor_get(v_fst_3028_, 0);
                    leanh::lean_inc(v_a_3047_);
                    leanh::lean_dec_ref_known(v_fst_3028_, 1);
                    v_snd_3048_ = leanh::lean_ctor_get(v_____x_3027_, 1);
                    leanh::lean_inc(v_snd_3048_);
                    leanh::lean_dec_ref(v_____x_3027_);
                    v_added_3049_ = leanh::lean_ctor_get(v_a_3047_, 1);
                    leanh::lean_inc_ref(v_added_3049_);
                    leanh::lean_dec(v_a_3047_);
                    v___x_3050_ = lean_array_get_size(v_added_3049_);
                    leanh::lean_dec_ref(v_added_3049_);
                    v___x_3051_ = leanh::lean_unsigned_to_nat(1);
                    leanh::lean_inc(v_toBind_3021_);
                    v___f_3052_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed as *mut core::ffi::c_void, 8, 5);
                    leanh::lean_closure_set(v___f_3052_, 0, v_toPure_3020_);
                    leanh::lean_closure_set(v___f_3052_, 1, v_toBind_3021_);
                    leanh::lean_closure_set(v___f_3052_, 2, v___f_3022_);
                    leanh::lean_closure_set(v___f_3052_, 3, v___x_3051_);
                    leanh::lean_closure_set(v___f_3052_, 4, v_inst_3023_);
                    v___x_3053_ = lean_nat_sub(v___x_3050_, v___x_3051_);
                    v___x_6143__overap_3054_ = l___private_Init_While_0__whileM_erased___redArg(
                        v___x_3024_,
                        v___f_3052_,
                        v___x_3053_,
                    );
                    leanh::lean_inc_ref(v_a_3025_);
                    v___x_3055_ = leanh::lean_apply_2(
                        v___x_6143__overap_3054_,
                        v_a_3025_,
                        v_snd_3048_,
                    );
                    v___x_3056_ = leanh::lean_apply_4(
                        v_toBind_3021_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___x_3055_,
                        v___f_3026_,
                    );
                    return v___x_3056_;
                }
            }
            1 => {
                v_a_3033_ = leanh::lean_ctor_get(v_fst_3028_, 0);
                v_isSharedCheck_3044_ = (!leanh::lean_is_exclusive(v_fst_3028_)) as u8;
                if v_isSharedCheck_3044_ == 0 {
                    v___x_3035_ = v_fst_3028_;
                    v_isShared_3036_ = v_isSharedCheck_3044_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3033_);
                    leanh::lean_dec(v_fst_3028_);
                    v___x_3035_ = leanh::lean_box(0);
                    v_isShared_3036_ = v_isSharedCheck_3044_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_3036_ == 0 {
                    v___x_3038_ = v___x_3035_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3043_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3033_);
                    v___x_3038_ = v_reuseFailAlloc_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3032_ == 0 {
                    leanh::lean_ctor_set(v___x_3031_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3038_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_snd_3029_);
                    v___x_3040_ = v_reuseFailAlloc_3042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3041_ = leanh::lean_apply_2(
                    v_toPure_3020_,
                    leanh::lean_box(0),
                    v___x_3040_,
                );
                return v___x_3041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(
    mut v_toPure_3057_: *mut leanh::LeanObject,
    mut v_toBind_3058_: *mut leanh::LeanObject,
    mut v___f_3059_: *mut leanh::LeanObject,
    mut v_inst_3060_: *mut leanh::LeanObject,
    mut v___x_3061_: *mut leanh::LeanObject,
    mut v_a_3062_: *mut leanh::LeanObject,
    mut v___f_3063_: *mut leanh::LeanObject,
    mut v_____x_3064_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3065_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(
            v_toPure_3057_,
            v_toBind_3058_,
            v___f_3059_,
            v_inst_3060_,
            v___x_3061_,
            v_a_3062_,
            v___f_3063_,
            v_____x_3064_,
        );
    leanh::lean_dec_ref(v_a_3062_);
    return v_res_3065_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
    mut v_inst_3066_: *mut leanh::LeanObject,
    mut v_a_3067_: *mut leanh::LeanObject,
    mut v_a_3068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_inst_3066_, 7);
    v___f_3069_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3069_, 0, v_inst_3066_);
    v___f_3070_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3070_, 0, v_inst_3066_);
    v___f_3071_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3071_, 0, v_inst_3066_);
    v___f_3072_ = leanh::lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    leanh::lean_closure_set(v___f_3072_, 0, v_inst_3066_);
    v___x_3073_ = leanh::lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3073_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3073_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3073_, 2, v_inst_3066_);
    v___x_3074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3074_, 0, v___x_3073_);
    leanh::lean_ctor_set(v___x_3074_, 1, v___f_3069_);
    v___x_3075_ = leanh::lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    leanh::lean_closure_set(v___x_3075_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3075_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3075_, 2, v_inst_3066_);
    v___x_3076_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3076_, 0, v___x_3074_);
    leanh::lean_ctor_set(v___x_3076_, 1, v___x_3075_);
    leanh::lean_ctor_set(v___x_3076_, 2, v___f_3070_);
    leanh::lean_ctor_set(v___x_3076_, 3, v___f_3071_);
    leanh::lean_ctor_set(v___x_3076_, 4, v___f_3072_);
    v___x_3077_ = leanh::lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    leanh::lean_closure_set(v___x_3077_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3077_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3077_, 2, v_inst_3066_);
    v___x_3078_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3078_, 0, v___x_3076_);
    leanh::lean_ctor_set(v___x_3078_, 1, v___x_3077_);
    leanh::lean_inc_ref_n(v___x_3078_, 6);
    v___f_3079_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3079_, 0, v___x_3078_);
    v___f_3080_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3080_, 0, v___x_3078_);
    v___f_3081_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3081_, 0, v___x_3078_);
    v___f_3082_ = leanh::lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    leanh::lean_closure_set(v___f_3082_, 0, v___x_3078_);
    v___x_3083_ = leanh::lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_3083_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3083_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3083_, 2, v___x_3078_);
    v___x_3084_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3084_, 0, v___x_3083_);
    leanh::lean_ctor_set(v___x_3084_, 1, v___f_3079_);
    v___x_3085_ = leanh::lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    leanh::lean_closure_set(v___x_3085_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3085_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3085_, 2, v___x_3078_);
    v___x_3086_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_3086_, 0, v___x_3084_);
    leanh::lean_ctor_set(v___x_3086_, 1, v___x_3085_);
    leanh::lean_ctor_set(v___x_3086_, 2, v___f_3080_);
    leanh::lean_ctor_set(v___x_3086_, 3, v___f_3081_);
    leanh::lean_ctor_set(v___x_3086_, 4, v___f_3082_);
    v___x_3087_ = leanh::lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    leanh::lean_closure_set(v___x_3087_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3087_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_3087_, 2, v___x_3078_);
    v___x_3088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3088_, 0, v___x_3086_);
    leanh::lean_ctor_set(v___x_3088_, 1, v___x_3087_);
    v___x_3089_ = l_ReaderT_instMonad___redArg(v___x_3088_);
    v_toApplicative_3090_ = leanh::lean_ctor_get(v_inst_3066_, 0);
    v_toBind_3091_ = leanh::lean_ctor_get(v_inst_3066_, 1);
    leanh::lean_inc_n(v_toBind_3091_, 3);
    v_toPure_3092_ = leanh::lean_ctor_get(v_toApplicative_3090_, 1);
    leanh::lean_inc_n(v_toPure_3092_, 5);
    v___f_3093_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3093_, 0, v_toPure_3092_);
    v___f_3094_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3094_, 0, v_toPure_3092_);
    leanh::lean_inc_ref(v_a_3067_);
    v___f_3095_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed as *mut core::ffi::c_void, 8, 7);
    leanh::lean_closure_set(v___f_3095_, 0, v_toPure_3092_);
    leanh::lean_closure_set(v___f_3095_, 1, v_toBind_3091_);
    leanh::lean_closure_set(v___f_3095_, 2, v___f_3094_);
    leanh::lean_closure_set(v___f_3095_, 3, v_inst_3066_);
    leanh::lean_closure_set(v___f_3095_, 4, v___x_3089_);
    leanh::lean_closure_set(v___f_3095_, 5, v_a_3067_);
    leanh::lean_closure_set(v___f_3095_, 6, v___f_3093_);
    v___f_3096_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3096_, 0, v_toPure_3092_);
    leanh::lean_inc_ref(v_a_3068_);
    v___x_3097_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3097_, 0, v_a_3068_);
    leanh::lean_ctor_set(v___x_3097_, 1, v_a_3068_);
    v___x_3098_ =
        leanh::lean_apply_2(v_toPure_3092_, leanh::lean_box(0), v___x_3097_);
    v___x_3099_ = leanh::lean_apply_4(
        v_toBind_3091_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3098_,
        v___f_3096_,
    );
    v___x_3100_ = leanh::lean_apply_4(
        v_toBind_3091_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3099_,
        v___f_3095_,
    );
    return v___x_3100_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(
    mut v_inst_3101_: *mut leanh::LeanObject,
    mut v_a_3102_: *mut leanh::LeanObject,
    mut v_a_3103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3104_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
        v_inst_3101_,
        v_a_3102_,
        v_a_3103_,
    );
    leanh::lean_dec_ref(v_a_3102_);
    return v_res_3104_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(
    mut v_m_3105_: *mut leanh::LeanObject,
    mut v_inst_3106_: *mut leanh::LeanObject,
    mut v_a_3107_: *mut leanh::LeanObject,
    mut v_a_3108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3109_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
        v_inst_3106_,
        v_a_3107_,
        v_a_3108_,
    );
    return v___x_3109_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(
    mut v_m_3110_: *mut leanh::LeanObject,
    mut v_inst_3111_: *mut leanh::LeanObject,
    mut v_a_3112_: *mut leanh::LeanObject,
    mut v_a_3113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3114_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(
        v_m_3110_,
        v_inst_3111_,
        v_a_3112_,
        v_a_3113_,
    );
    leanh::lean_dec_ref(v_a_3112_);
    return v_res_3114_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(
    mut v_toApplicative_3115_: *mut leanh::LeanObject,
    mut v_inst_3116_: *mut leanh::LeanObject,
    mut v_a_3117_: *mut leanh::LeanObject,
    mut v_____x_3118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v_a_3124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v_toPure_3128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_unused_3138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_3140_: u8 = 0;
    let mut v_snd_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v_toPure_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3119_ = leanh::lean_ctor_get(v_____x_3118_, 0);
                leanh::lean_inc(v_fst_3119_);
                if leanh::lean_obj_tag(v_fst_3119_) == 0 {
                    leanh::lean_dec_ref(v_inst_3116_);
                    v_snd_3120_ = leanh::lean_ctor_get(v_____x_3118_, 1);
                    v_isSharedCheck_3137_ = (!leanh::lean_is_exclusive(v_____x_3118_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v_unused_3138_ = leanh::lean_ctor_get(v_____x_3118_, 0);
                        leanh::lean_dec(v_unused_3138_);
                        v___x_3122_ = v_____x_3118_;
                        v_isShared_3123_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3120_);
                        leanh::lean_dec(v_____x_3118_);
                        v___x_3122_ = leanh::lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3139_ = leanh::lean_ctor_get(v_fst_3119_, 0);
                    leanh::lean_inc(v_a_3139_);
                    leanh::lean_dec_ref_known(v_fst_3119_, 1);
                    v_found_3140_ = leanh::lean_ctor_get_uint8(
                        v_a_3139_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    );
                    leanh::lean_dec(v_a_3139_);
                    if v_found_3140_ == 0 {
                        leanh::lean_dec_ref(v_inst_3116_);
                        v_snd_3141_ = leanh::lean_ctor_get(v_____x_3118_, 1);
                        v_isSharedCheck_3151_ =
                            (!leanh::lean_is_exclusive(v_____x_3118_)) as u8;
                        if v_isSharedCheck_3151_ == 0 {
                            v_unused_3152_ = leanh::lean_ctor_get(v_____x_3118_, 0);
                            leanh::lean_dec(v_unused_3152_);
                            v___x_3143_ = v_____x_3118_;
                            v_isShared_3144_ = v_isSharedCheck_3151_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_3141_);
                            leanh::lean_dec(v_____x_3118_);
                            v___x_3143_ = leanh::lean_box(0);
                            v_isShared_3144_ = v_isSharedCheck_3151_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_toApplicative_3115_);
                        v_snd_3153_ = leanh::lean_ctor_get(v_____x_3118_, 1);
                        leanh::lean_inc(v_snd_3153_);
                        leanh::lean_dec_ref(v_____x_3118_);
                        v___x_3154_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_3116_, v_a_3117_, v_snd_3153_);
                        return v___x_3154_;
                    }
                }
            }
            1 => {
                v_a_3124_ = leanh::lean_ctor_get(v_fst_3119_, 0);
                v_isSharedCheck_3136_ = (!leanh::lean_is_exclusive(v_fst_3119_)) as u8;
                if v_isSharedCheck_3136_ == 0 {
                    v___x_3126_ = v_fst_3119_;
                    v_isShared_3127_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_a_3124_);
                    leanh::lean_dec(v_fst_3119_);
                    v___x_3126_ = leanh::lean_box(0);
                    v_isShared_3127_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_3128_ = leanh::lean_ctor_get(v_toApplicative_3115_, 1);
                leanh::lean_inc(v_toPure_3128_);
                leanh::lean_dec_ref(v_toApplicative_3115_);
                if v_isShared_3127_ == 0 {
                    v___x_3130_ = v___x_3126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3124_);
                    v___x_3130_ = v_reuseFailAlloc_3135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3123_ == 0 {
                    leanh::lean_ctor_set(v___x_3122_, 0, v___x_3130_);
                    v___x_3132_ = v___x_3122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3130_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_snd_3120_);
                    v___x_3132_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3133_ = leanh::lean_apply_2(
                    v_toPure_3128_,
                    leanh::lean_box(0),
                    v___x_3132_,
                );
                return v___x_3133_;
            }
            5 => {
                v_toPure_3145_ = leanh::lean_ctor_get(v_toApplicative_3115_, 1);
                leanh::lean_inc(v_toPure_3145_);
                leanh::lean_dec_ref(v_toApplicative_3115_);
                v___x_3146_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0;
                if v_isShared_3144_ == 0 {
                    leanh::lean_ctor_set(v___x_3143_, 0, v___x_3146_);
                    v___x_3148_ = v___x_3143_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3146_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_snd_3141_);
                    v___x_3148_ = v_reuseFailAlloc_3150_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3149_ = leanh::lean_apply_2(
                    v_toPure_3145_,
                    leanh::lean_box(0),
                    v___x_3148_,
                );
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(
    mut v_toApplicative_3155_: *mut leanh::LeanObject,
    mut v_inst_3156_: *mut leanh::LeanObject,
    mut v_a_3157_: *mut leanh::LeanObject,
    mut v_____x_3158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3159_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(
            v_toApplicative_3155_,
            v_inst_3156_,
            v_a_3157_,
            v_____x_3158_,
        );
    leanh::lean_dec_ref(v_a_3157_);
    return v_res_3159_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(
    mut v_toApplicative_3160_: *mut leanh::LeanObject,
    mut v_toBind_3161_: *mut leanh::LeanObject,
    mut v___f_3162_: *mut leanh::LeanObject,
    mut v_____x_3163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_3164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_3165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v_toPure_3171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3164_ = leanh::lean_ctor_get(v_____x_3163_, 0);
                if leanh::lean_obj_tag(v_fst_3164_) == 0 {
                    leanh::lean_dec(v___f_3162_);
                    leanh::lean_dec(v_toBind_3161_);
                    v_toPure_3165_ = leanh::lean_ctor_get(v_toApplicative_3160_, 1);
                    leanh::lean_inc(v_toPure_3165_);
                    leanh::lean_dec_ref(v_toApplicative_3160_);
                    v___x_3166_ = leanh::lean_apply_2(
                        v_toPure_3165_,
                        leanh::lean_box(0),
                        v_____x_3163_,
                    );
                    return v___x_3166_;
                } else {
                    v_snd_3167_ = leanh::lean_ctor_get(v_____x_3163_, 1);
                    v_isSharedCheck_3179_ = (!leanh::lean_is_exclusive(v_____x_3163_)) as u8;
                    if v_isSharedCheck_3179_ == 0 {
                        v_unused_3180_ = leanh::lean_ctor_get(v_____x_3163_, 0);
                        leanh::lean_dec(v_unused_3180_);
                        v___x_3169_ = v_____x_3163_;
                        v_isShared_3170_ = v_isSharedCheck_3179_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_3167_);
                        leanh::lean_dec(v_____x_3163_);
                        v___x_3169_ = leanh::lean_box(0);
                        v_isShared_3170_ = v_isSharedCheck_3179_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toPure_3171_ = leanh::lean_ctor_get(v_toApplicative_3160_, 1);
                leanh::lean_inc_n(v_toPure_3171_, 2);
                leanh::lean_dec_ref(v_toApplicative_3160_);
                v___f_3172_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_3172_, 0, v_toPure_3171_);
                leanh::lean_inc(v_snd_3167_);
                if v_isShared_3170_ == 0 {
                    leanh::lean_ctor_set(v___x_3169_, 0, v_snd_3167_);
                    v___x_3174_ = v___x_3169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_snd_3167_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_snd_3167_);
                    v___x_3174_ = v_reuseFailAlloc_3178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3175_ = leanh::lean_apply_2(
                    v_toPure_3171_,
                    leanh::lean_box(0),
                    v___x_3174_,
                );
                leanh::lean_inc(v_toBind_3161_);
                v___x_3176_ = leanh::lean_apply_4(
                    v_toBind_3161_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3175_,
                    v___f_3172_,
                );
                v___x_3177_ = leanh::lean_apply_4(
                    v_toBind_3161_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_3176_,
                    v___f_3162_,
                );
                return v___x_3177_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
    mut v_inst_3181_: *mut leanh::LeanObject,
    mut v_a_3182_: *mut leanh::LeanObject,
    mut v_a_3183_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3184_ = leanh::lean_ctor_get(v_inst_3181_, 0);
    v_toBind_3185_ = leanh::lean_ctor_get(v_inst_3181_, 1);
    leanh::lean_inc_n(v_toBind_3185_, 2);
    leanh::lean_inc_ref(v_a_3182_);
    leanh::lean_inc_ref(v_inst_3181_);
    leanh::lean_inc_ref_n(v_toApplicative_3184_, 2);
    v___f_3186_ = leanh::lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_3186_, 0, v_toApplicative_3184_);
    leanh::lean_closure_set(v___f_3186_, 1, v_inst_3181_);
    leanh::lean_closure_set(v___f_3186_, 2, v_a_3182_);
    v___f_3187_ = leanh::lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_3187_, 0, v_toApplicative_3184_);
    leanh::lean_closure_set(v___f_3187_, 1, v_toBind_3185_);
    leanh::lean_closure_set(v___f_3187_, 2, v___f_3186_);
    v___x_3188_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_3181_,
        v_a_3182_,
        v_a_3183_,
    );
    v___x_3189_ = leanh::lean_apply_4(
        v_toBind_3185_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3188_,
        v___f_3187_,
    );
    return v___x_3189_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(
    mut v_inst_3190_: *mut leanh::LeanObject,
    mut v_a_3191_: *mut leanh::LeanObject,
    mut v_a_3192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3193_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3193_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
        v_inst_3190_,
        v_a_3191_,
        v_a_3192_,
    );
    leanh::lean_dec_ref(v_a_3191_);
    return v_res_3193_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(
    mut v_m_3194_: *mut leanh::LeanObject,
    mut v_inst_3195_: *mut leanh::LeanObject,
    mut v_a_3196_: *mut leanh::LeanObject,
    mut v_a_3197_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3198_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
        v_inst_3195_,
        v_a_3196_,
        v_a_3197_,
    );
    return v___x_3198_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(
    mut v_m_3199_: *mut leanh::LeanObject,
    mut v_inst_3200_: *mut leanh::LeanObject,
    mut v_a_3201_: *mut leanh::LeanObject,
    mut v_a_3202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3203_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(
        v_m_3199_,
        v_inst_3200_,
        v_a_3201_,
        v_a_3202_,
    );
    leanh::lean_dec_ref(v_a_3201_);
    return v_res_3203_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__0(
    mut v_toApplicative_3204_: *mut leanh::LeanObject,
    mut v_____x_3205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_3206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cur_3208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numCalls_3209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_found_3210_: u8 = 0;
    let mut v___y_3212_: u8 = 0;
    let mut v_toPure_3213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u8 = 0;
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3206_ = leanh::lean_ctor_get(v_____x_3205_, 1);
                v_fst_3207_ = leanh::lean_ctor_get(v_____x_3205_, 0);
                v_cur_3208_ = leanh::lean_ctor_get(v_snd_3206_, 0);
                v_numCalls_3209_ = leanh::lean_ctor_get(v_snd_3206_, 2);
                v_found_3210_ = leanh::lean_ctor_get_uint8(
                    v_snd_3206_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                );
                if v_found_3210_ == 0 {
                    v___x_3216_ = 0;
                    v___y_3212_ = v___x_3216_;
                    state = 1;
                    continue;
                } else {
                    if leanh::lean_obj_tag(v_fst_3207_) == 0 {
                        v___x_3217_ = 1;
                        v___y_3212_ = v___x_3217_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3218_ = 2;
                        v___y_3212_ = v___x_3218_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toPure_3213_ = leanh::lean_ctor_get(v_toApplicative_3204_, 1);
                leanh::lean_inc(v_toPure_3213_);
                leanh::lean_dec_ref(v_toApplicative_3204_);
                leanh::lean_inc(v_numCalls_3209_);
                leanh::lean_inc_ref(v_cur_3208_);
                v___x_3214_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_3214_, 0, v_cur_3208_);
                leanh::lean_ctor_set(v___x_3214_, 1, v_numCalls_3209_);
                leanh::lean_ctor_set_uint8(
                    v___x_3214_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___y_3212_,
                );
                v___x_3215_ = leanh::lean_apply_2(
                    v_toPure_3213_,
                    leanh::lean_box(0),
                    v___x_3214_,
                );
                return v___x_3215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(
    mut v_toApplicative_3219_: *mut leanh::LeanObject,
    mut v_____x_3220_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3221_ =
        l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toApplicative_3219_, v_____x_3220_);
    leanh::lean_dec_ref(v_____x_3220_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__1(
    mut v_initialMask_3224_: *mut leanh::LeanObject,
    mut v_test_3225_: *mut leanh::LeanObject,
    mut v_maxCalls_3226_: *mut leanh::LeanObject,
    mut v_inst_3227_: *mut leanh::LeanObject,
    mut v_toBind_3228_: *mut leanh::LeanObject,
    mut v___f_3229_: *mut leanh::LeanObject,
    mut v_toApplicative_3230_: *mut leanh::LeanObject,
    mut v_____do__lift_3231_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_3231_ == 0 {
        let mut v___x_3232_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3235_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3237_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_toApplicative_3230_);
        leanh::lean_inc_ref(v_initialMask_3224_);
        v___x_3232_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
        leanh::lean_ctor_set(v___x_3232_, 0, v_initialMask_3224_);
        leanh::lean_ctor_set(v___x_3232_, 1, v_test_3225_);
        leanh::lean_ctor_set(v___x_3232_, 2, v_maxCalls_3226_);
        v___x_3233_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0;
        v___x_3234_ = leanh::lean_unsigned_to_nat(1);
        v___x_3235_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
        leanh::lean_ctor_set(v___x_3235_, 0, v_initialMask_3224_);
        leanh::lean_ctor_set(v___x_3235_, 1, v___x_3233_);
        leanh::lean_ctor_set(v___x_3235_, 2, v___x_3234_);
        leanh::lean_ctor_set_uint8(
            v___x_3235_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
            v_____do__lift_3231_,
        );
        v___x_3236_ =
            l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
                v_inst_3227_,
                v___x_3232_,
                v___x_3235_,
            );
        leanh::lean_dec_ref_known(v___x_3232_, 3);
        v___x_3237_ = leanh::lean_apply_4(
            v_toBind_3228_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_3236_,
            v___f_3229_,
        );
        return v___x_3237_;
    } else {
        let mut v_toPure_3238_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3239_: u8 = 0;
        let mut v___x_3240_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3241_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___f_3229_);
        leanh::lean_dec(v_toBind_3228_);
        leanh::lean_dec_ref(v_inst_3227_);
        leanh::lean_dec(v_maxCalls_3226_);
        leanh::lean_dec(v_test_3225_);
        v_toPure_3238_ = leanh::lean_ctor_get(v_toApplicative_3230_, 1);
        leanh::lean_inc(v_toPure_3238_);
        leanh::lean_dec_ref(v_toApplicative_3230_);
        v___x_3239_ = 2;
        v___x_3240_ = leanh::lean_unsigned_to_nat(1);
        v___x_3241_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
        leanh::lean_ctor_set(v___x_3241_, 0, v_initialMask_3224_);
        leanh::lean_ctor_set(v___x_3241_, 1, v___x_3240_);
        leanh::lean_ctor_set_uint8(
            v___x_3241_,
            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
            v___x_3239_,
        );
        v___x_3242_ =
            leanh::lean_apply_2(v_toPure_3238_, leanh::lean_box(0), v___x_3241_);
        return v___x_3242_;
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(
    mut v_initialMask_3243_: *mut leanh::LeanObject,
    mut v_test_3244_: *mut leanh::LeanObject,
    mut v_maxCalls_3245_: *mut leanh::LeanObject,
    mut v_inst_3246_: *mut leanh::LeanObject,
    mut v_toBind_3247_: *mut leanh::LeanObject,
    mut v___f_3248_: *mut leanh::LeanObject,
    mut v_toApplicative_3249_: *mut leanh::LeanObject,
    mut v_____do__lift_3250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_277__boxed_3251_: u8 = 0;
    let mut v_res_3252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_277__boxed_3251_ = (leanh::lean_unbox(v_____do__lift_3250_) as u8);
    v_res_3252_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1(
        v_initialMask_3243_,
        v_test_3244_,
        v_maxCalls_3245_,
        v_inst_3246_,
        v_toBind_3247_,
        v___f_3248_,
        v_toApplicative_3249_,
        v_____do__lift_277__boxed_3251_,
    );
    return v_res_3252_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg(
    mut v_inst_3253_: *mut leanh::LeanObject,
    mut v_initialMask_3254_: *mut leanh::LeanObject,
    mut v_test_3255_: *mut leanh::LeanObject,
    mut v_maxCalls_3256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_3257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_3258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_3257_ = leanh::lean_ctor_get(v_inst_3253_, 0);
    leanh::lean_inc_ref_n(v_toApplicative_3257_, 2);
    v_toBind_3258_ = leanh::lean_ctor_get(v_inst_3253_, 1);
    leanh::lean_inc_n(v_toBind_3258_, 2);
    v___f_3259_ = leanh::lean_alloc_closure(
        l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3259_, 0, v_toApplicative_3257_);
    leanh::lean_inc(v_test_3255_);
    leanh::lean_inc_ref(v_initialMask_3254_);
    v___f_3260_ = leanh::lean_alloc_closure(
        l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    leanh::lean_closure_set(v___f_3260_, 0, v_initialMask_3254_);
    leanh::lean_closure_set(v___f_3260_, 1, v_test_3255_);
    leanh::lean_closure_set(v___f_3260_, 2, v_maxCalls_3256_);
    leanh::lean_closure_set(v___f_3260_, 3, v_inst_3253_);
    leanh::lean_closure_set(v___f_3260_, 4, v_toBind_3258_);
    leanh::lean_closure_set(v___f_3260_, 5, v___f_3259_);
    leanh::lean_closure_set(v___f_3260_, 6, v_toApplicative_3257_);
    v___x_3261_ = leanh::lean_apply_1(v_test_3255_, v_initialMask_3254_);
    v___x_3262_ = leanh::lean_apply_4(
        v_toBind_3258_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_3261_,
        v___f_3260_,
    );
    return v___x_3262_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search(
    mut v_m_3263_: *mut leanh::LeanObject,
    mut v_inst_3264_: *mut leanh::LeanObject,
    mut v_initialMask_3265_: *mut leanh::LeanObject,
    mut v_test_3266_: *mut leanh::LeanObject,
    mut v_maxCalls_3267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3268_ = l_Lean_Util_ParamMinimizer_search___redArg(
        v_inst_3264_,
        v_initialMask_3265_,
        v_test_3266_,
        v_maxCalls_3267_,
    );
    return v___x_3268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ParamMinimizer(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Util_ParamMinimizer_instInhabitedStatus_default =
        _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default();
    l_Lean_Util_ParamMinimizer_instInhabitedStatus =
        _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ParamMinimizer(
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
pub unsafe fn initialize_Lean_Util_ParamMinimizer(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ParamMinimizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ParamMinimizer(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Util_ParamMinimizer(builtin);
}
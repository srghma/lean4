// Lean compiler output
// Module: Lean.Util.ParamMinimizer
// Imports: Init.While Init.Data.Range.Polymorphic
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
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_set;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_le, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_6, lean_box, lean_closure_set,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unsigned_to_nat,
};
pub static mut l_Lean_Util_ParamMinimizer_instInhabitedStatus_default: u8 = 0;
pub static mut l_Lean_Util_ParamMinimizer_instInhabitedStatus: u8 = 0;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105,
            109, 105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 109, 105, 115, 115, 105,
            110, 103, 0,
        ],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__0_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value: LeanStringObject<39> =
    LeanStringObject {
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
            76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105,
            109, 105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 97, 112, 112, 114, 111,
            120, 0,
        ],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__2_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value: LeanStringObject<40> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 40,
        m_capacity: 40,
        m_length: 39,
        m_data: [
            76, 101, 97, 110, 46, 85, 116, 105, 108, 46, 80, 97, 114, 97, 109, 77, 105, 110, 105,
            109, 105, 122, 101, 114, 46, 83, 116, 97, 116, 117, 115, 46, 112, 114, 101, 99, 105,
            115, 101, 0,
        ],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [core::ptr::addr_of!(
            l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__4_value
        ) as *mut LeanObject],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Util_ParamMinimizer_instReprStatus_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Util_ParamMinimizer_instReprStatus___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Util_ParamMinimizer_instReprStatus: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_instReprStatus___closed__0_value)
        as *mut LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value: LeanArrayObject<
    0,
> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorIdx(mut v_x_1635_: u8) -> *mut LeanObject {
    match v_x_1635_ {
        0 => {
            let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
            v___x_1636_ = lean_unsigned_to_nat(0);
            return v___x_1636_;
        }
        1 => {
            let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
            v___x_1637_ = lean_unsigned_to_nat(1);
            return v___x_1637_;
        }
        _ => {
            let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
            v___x_1638_ = lean_unsigned_to_nat(2);
            return v___x_1638_;
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorIdx___boxed(
    mut v_x_1639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_1640_: u8 = 0;
    let mut v_res_1641_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_1640_ = (lean_unbox(v_x_1639_) as u8);
    v_res_1641_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_boxed_1640_);
    return v_res_1641_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_toCtorIdx(mut v_x_1642_: u8) -> *mut LeanObject {
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1643_ = l_Lean_Util_ParamMinimizer_Status_ctorIdx(v_x_1642_);
    return v___x_1643_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_toCtorIdx___boxed(
    mut v_x_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_1645_: u8 = 0;
    let mut v_res_1646_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_1645_ = (lean_unbox(v_x_1644_) as u8);
    v_res_1646_ = l_Lean_Util_ParamMinimizer_Status_toCtorIdx(v_x_4__boxed_1645_);
    return v_res_1646_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(
    mut v_k_1647_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1647_);
    return v_k_1647_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg___boxed(
    mut v_k_1648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1649_: *mut LeanObject = core::ptr::null_mut();
    v_res_1649_ = l_Lean_Util_ParamMinimizer_Status_ctorElim___redArg(v_k_1648_);
    lean_dec(v_k_1648_);
    return v_res_1649_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim(
    mut v_motive_1650_: *mut LeanObject,
    mut v_ctorIdx_1651_: *mut LeanObject,
    mut v_t_1652_: u8,
    mut v_h_1653_: *mut LeanObject,
    mut v_k_1654_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_1654_);
    return v_k_1654_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_ctorElim___boxed(
    mut v_motive_1655_: *mut LeanObject,
    mut v_ctorIdx_1656_: *mut LeanObject,
    mut v_t_1657_: *mut LeanObject,
    mut v_h_1658_: *mut LeanObject,
    mut v_k_1659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1660_: u8 = 0;
    let mut v_res_1661_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1660_ = (lean_unbox(v_t_1657_) as u8);
    v_res_1661_ = l_Lean_Util_ParamMinimizer_Status_ctorElim(
        v_motive_1655_,
        v_ctorIdx_1656_,
        v_t_boxed_1660_,
        v_h_1658_,
        v_k_1659_,
    );
    lean_dec(v_k_1659_);
    lean_dec(v_ctorIdx_1656_);
    return v_res_1661_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(
    mut v_missing_1662_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_missing_1662_);
    return v_missing_1662_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg___boxed(
    mut v_missing_1663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1664_: *mut LeanObject = core::ptr::null_mut();
    v_res_1664_ = l_Lean_Util_ParamMinimizer_Status_missing_elim___redArg(v_missing_1663_);
    lean_dec(v_missing_1663_);
    return v_res_1664_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim(
    mut v_motive_1665_: *mut LeanObject,
    mut v_t_1666_: u8,
    mut v_h_1667_: *mut LeanObject,
    mut v_missing_1668_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_missing_1668_);
    return v_missing_1668_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_missing_elim___boxed(
    mut v_motive_1669_: *mut LeanObject,
    mut v_t_1670_: *mut LeanObject,
    mut v_h_1671_: *mut LeanObject,
    mut v_missing_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1673_: u8 = 0;
    let mut v_res_1674_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1673_ = (lean_unbox(v_t_1670_) as u8);
    v_res_1674_ = l_Lean_Util_ParamMinimizer_Status_missing_elim(
        v_motive_1669_,
        v_t_boxed_1673_,
        v_h_1671_,
        v_missing_1672_,
    );
    lean_dec(v_missing_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(
    mut v_approx_1675_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_approx_1675_);
    return v_approx_1675_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg___boxed(
    mut v_approx_1676_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1677_: *mut LeanObject = core::ptr::null_mut();
    v_res_1677_ = l_Lean_Util_ParamMinimizer_Status_approx_elim___redArg(v_approx_1676_);
    lean_dec(v_approx_1676_);
    return v_res_1677_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim(
    mut v_motive_1678_: *mut LeanObject,
    mut v_t_1679_: u8,
    mut v_h_1680_: *mut LeanObject,
    mut v_approx_1681_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_approx_1681_);
    return v_approx_1681_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_approx_elim___boxed(
    mut v_motive_1682_: *mut LeanObject,
    mut v_t_1683_: *mut LeanObject,
    mut v_h_1684_: *mut LeanObject,
    mut v_approx_1685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1686_: u8 = 0;
    let mut v_res_1687_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1686_ = (lean_unbox(v_t_1683_) as u8);
    v_res_1687_ = l_Lean_Util_ParamMinimizer_Status_approx_elim(
        v_motive_1682_,
        v_t_boxed_1686_,
        v_h_1684_,
        v_approx_1685_,
    );
    lean_dec(v_approx_1685_);
    return v_res_1687_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(
    mut v_precise_1688_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_precise_1688_);
    return v_precise_1688_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg___boxed(
    mut v_precise_1689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1690_: *mut LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lean_Util_ParamMinimizer_Status_precise_elim___redArg(v_precise_1689_);
    lean_dec(v_precise_1689_);
    return v_res_1690_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim(
    mut v_motive_1691_: *mut LeanObject,
    mut v_t_1692_: u8,
    mut v_h_1693_: *mut LeanObject,
    mut v_precise_1694_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_precise_1694_);
    return v_precise_1694_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_Status_precise_elim___boxed(
    mut v_motive_1695_: *mut LeanObject,
    mut v_t_1696_: *mut LeanObject,
    mut v_h_1697_: *mut LeanObject,
    mut v_precise_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_1699_: u8 = 0;
    let mut v_res_1700_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_1699_ = (lean_unbox(v_t_1696_) as u8);
    v_res_1700_ = l_Lean_Util_ParamMinimizer_Status_precise_elim(
        v_motive_1695_,
        v_t_boxed_1699_,
        v_h_1697_,
        v_precise_1698_,
    );
    lean_dec(v_precise_1698_);
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
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__6() -> *mut LeanObject
{
    let mut v___x_1712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    v___x_1712_ = lean_unsigned_to_nat(2);
    v___x_1713_ = lean_nat_to_int(v___x_1712_);
    return v___x_1713_;
}
pub unsafe fn _init_l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__7() -> *mut LeanObject
{
    let mut v___x_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut LeanObject = core::ptr::null_mut();
    v___x_1714_ = lean_unsigned_to_nat(1);
    v___x_1715_ = lean_nat_to_int(v___x_1714_);
    return v___x_1715_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_instReprStatus_repr(
    mut v_x_1716_: u8,
    mut v_prec_1717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_1719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: u8 = 0;
    let mut v___x_1723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1729_: u8 = 0;
    let mut v___x_1730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: u8 = 0;
    let mut v___x_1741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1744_: u8 = 0;
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: u8 = 0;
    let mut v___x_1749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1750_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_1716_ {
                0 => {
                    v___x_1739_ = lean_unsigned_to_nat(1024);
                    v___x_1740_ = lean_nat_dec_le(v___x_1739_, v_prec_1717_);
                    if v___x_1740_ == 0 {
                        v___x_1741_ = lean_obj_once(
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
                        v___x_1742_ = lean_obj_once(
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
                    v___x_1743_ = lean_unsigned_to_nat(1024);
                    v___x_1744_ = lean_nat_dec_le(v___x_1743_, v_prec_1717_);
                    if v___x_1744_ == 0 {
                        v___x_1745_ = lean_obj_once(
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
                        v___x_1746_ = lean_obj_once(
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
                    v___x_1747_ = lean_unsigned_to_nat(1024);
                    v___x_1748_ = lean_nat_dec_le(v___x_1747_, v_prec_1717_);
                    if v___x_1748_ == 0 {
                        v___x_1749_ = lean_obj_once(
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
                        v___x_1750_ = lean_obj_once(
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
                lean_inc(v___y_1719_);
                v___x_1721_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1721_, 0, v___y_1719_);
                lean_ctor_set(v___x_1721_, 1, v___x_1720_);
                v___x_1722_ = 0;
                v___x_1723_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1723_, 0, v___x_1721_);
                lean_ctor_set_uint8(
                    v___x_1723_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1722_,
                );
                v___x_1724_ = l_Repr_addAppParen(v___x_1723_, v_prec_1717_);
                return v___x_1724_;
            }
            2 => {
                v___x_1727_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__3;
                lean_inc(v___y_1726_);
                v___x_1728_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1728_, 0, v___y_1726_);
                lean_ctor_set(v___x_1728_, 1, v___x_1727_);
                v___x_1729_ = 0;
                v___x_1730_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1730_, 0, v___x_1728_);
                lean_ctor_set_uint8(
                    v___x_1730_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1729_,
                );
                v___x_1731_ = l_Repr_addAppParen(v___x_1730_, v_prec_1717_);
                return v___x_1731_;
            }
            3 => {
                v___x_1734_ = l_Lean_Util_ParamMinimizer_instReprStatus_repr___closed__5;
                lean_inc(v___y_1733_);
                v___x_1735_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_1735_, 0, v___y_1733_);
                lean_ctor_set(v___x_1735_, 1, v___x_1734_);
                v___x_1736_ = 0;
                v___x_1737_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_1737_, 0, v___x_1735_);
                lean_ctor_set_uint8(
                    v___x_1737_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_1751_: *mut LeanObject,
    mut v_prec_1752_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_177__boxed_1753_: u8 = 0;
    let mut v_res_1754_: *mut LeanObject = core::ptr::null_mut();
    v_x_177__boxed_1753_ = (lean_unbox(v_x_1751_) as u8);
    v_res_1754_ =
        l_Lean_Util_ParamMinimizer_instReprStatus_repr(v_x_177__boxed_1753_, v_prec_1752_);
    lean_dec(v_prec_1752_);
    return v_res_1754_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0(
    mut v_toPure_1757_: *mut LeanObject,
    mut v_____x_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1763_: u8 = 0;
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1769_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1759_ = lean_ctor_get(v_____x_1758_, 0);
                v_snd_1760_ = lean_ctor_get(v_____x_1758_, 1);
                v_isSharedCheck_1769_ = (!lean_is_exclusive(v_____x_1758_)) as u8;
                if v_isSharedCheck_1769_ == 0 {
                    v___x_1762_ = v_____x_1758_;
                    v_isShared_1763_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_1760_);
                    lean_inc(v_fst_1759_);
                    lean_dec(v_____x_1758_);
                    v___x_1762_ = lean_box(0);
                    v_isShared_1763_ = v_isSharedCheck_1769_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1764_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1764_, 0, v_fst_1759_);
                if v_isShared_1763_ == 0 {
                    lean_ctor_set(v___x_1762_, 0, v___x_1764_);
                    v___x_1766_ = v___x_1762_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1768_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 0, v___x_1764_);
                    lean_ctor_set(v_reuseFailAlloc_1768_, 1, v_snd_1760_);
                    v___x_1766_ = v_reuseFailAlloc_1768_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1767_ = lean_apply_2(v_toPure_1757_, lean_box(0), v___x_1766_);
                return v___x_1767_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
    mut v_inst_1770_: *mut LeanObject,
    mut v_a_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1776_: u8 = 0;
    let mut v_toPure_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_1778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_1779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___f_1784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1786_: u8 = 0;
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1795_: u8 = 0;
    let mut v_isSharedCheck_1796_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1772_ = lean_ctor_get(v_inst_1770_, 0);
                v_toBind_1773_ = lean_ctor_get(v_inst_1770_, 1);
                v_isSharedCheck_1796_ = (!lean_is_exclusive(v_inst_1770_)) as u8;
                if v_isSharedCheck_1796_ == 0 {
                    v___x_1775_ = v_inst_1770_;
                    v_isShared_1776_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1773_);
                    lean_inc(v_toApplicative_1772_);
                    lean_dec(v_inst_1770_);
                    v___x_1775_ = lean_box(0);
                    v_isShared_1776_ = v_isSharedCheck_1796_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1777_ = lean_ctor_get(v_toApplicative_1772_, 1);
                lean_inc(v_toPure_1777_);
                lean_dec_ref(v_toApplicative_1772_);
                v_cur_1778_ = lean_ctor_get(v_a_1771_, 0);
                v_added_1779_ = lean_ctor_get(v_a_1771_, 1);
                v_numCalls_1780_ = lean_ctor_get(v_a_1771_, 2);
                v_isSharedCheck_1795_ = (!lean_is_exclusive(v_a_1771_)) as u8;
                if v_isSharedCheck_1795_ == 0 {
                    v___x_1782_ = v_a_1771_;
                    v_isShared_1783_ = v_isSharedCheck_1795_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_numCalls_1780_);
                    lean_inc(v_added_1779_);
                    lean_inc(v_cur_1778_);
                    lean_dec(v_a_1771_);
                    v___x_1782_ = lean_box(0);
                    v_isShared_1783_ = v_isSharedCheck_1795_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toPure_1777_);
                v___f_1784_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1784_, 0, v_toPure_1777_);
                v___x_1785_ = lean_box(0);
                v___x_1786_ = 1;
                if v_isShared_1783_ == 0 {
                    v___x_1788_ = v___x_1782_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1794_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 0, v_cur_1778_);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 1, v_added_1779_);
                    lean_ctor_set(v_reuseFailAlloc_1794_, 2, v_numCalls_1780_);
                    v___x_1788_ = v_reuseFailAlloc_1794_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                lean_ctor_set_uint8(
                    v___x_1788_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_1786_,
                );
                if v_isShared_1776_ == 0 {
                    lean_ctor_set(v___x_1775_, 1, v___x_1788_);
                    lean_ctor_set(v___x_1775_, 0, v___x_1785_);
                    v___x_1790_ = v___x_1775_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1793_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 0, v___x_1785_);
                    lean_ctor_set(v_reuseFailAlloc_1793_, 1, v___x_1788_);
                    v___x_1790_ = v_reuseFailAlloc_1793_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1791_ = lean_apply_2(v_toPure_1777_, lean_box(0), v___x_1790_);
                v___x_1792_ = lean_apply_4(
                    v_toBind_1773_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1797_: *mut LeanObject,
    mut v_inst_1798_: *mut LeanObject,
    mut v_a_1799_: *mut LeanObject,
    mut v_a_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    v___x_1801_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
            v_inst_1798_,
            v_a_1800_,
        );
    return v___x_1801_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___boxed(
    mut v_m_1802_: *mut LeanObject,
    mut v_inst_1803_: *mut LeanObject,
    mut v_a_1804_: *mut LeanObject,
    mut v_a_1805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1806_: *mut LeanObject = core::ptr::null_mut();
    v_res_1806_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound(
        v_m_1802_,
        v_inst_1803_,
        v_a_1804_,
        v_a_1805_,
    );
    lean_dec_ref(v_a_1804_);
    return v_res_1806_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(
    mut v_inst_1807_: *mut LeanObject,
    mut v_a_1808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v_toPure_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_1818_: u8 = 0;
    let mut v___x_1820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1821_: u8 = 0;
    let mut v___f_1822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1834_: u8 = 0;
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1809_ = lean_ctor_get(v_inst_1807_, 0);
                v_toBind_1810_ = lean_ctor_get(v_inst_1807_, 1);
                v_isSharedCheck_1835_ = (!lean_is_exclusive(v_inst_1807_)) as u8;
                if v_isSharedCheck_1835_ == 0 {
                    v___x_1812_ = v_inst_1807_;
                    v_isShared_1813_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1810_);
                    lean_inc(v_toApplicative_1809_);
                    lean_dec(v_inst_1807_);
                    v___x_1812_ = lean_box(0);
                    v_isShared_1813_ = v_isSharedCheck_1835_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1814_ = lean_ctor_get(v_toApplicative_1809_, 1);
                lean_inc(v_toPure_1814_);
                lean_dec_ref(v_toApplicative_1809_);
                v_cur_1815_ = lean_ctor_get(v_a_1808_, 0);
                v_added_1816_ = lean_ctor_get(v_a_1808_, 1);
                v_numCalls_1817_ = lean_ctor_get(v_a_1808_, 2);
                v_found_1818_ = lean_ctor_get_uint8(
                    v_a_1808_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1834_ = (!lean_is_exclusive(v_a_1808_)) as u8;
                if v_isSharedCheck_1834_ == 0 {
                    v___x_1820_ = v_a_1808_;
                    v_isShared_1821_ = v_isSharedCheck_1834_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_numCalls_1817_);
                    lean_inc(v_added_1816_);
                    lean_inc(v_cur_1815_);
                    lean_dec(v_a_1808_);
                    v___x_1820_ = lean_box(0);
                    v_isShared_1821_ = v_isSharedCheck_1834_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toPure_1814_);
                v___f_1822_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1822_, 0, v_toPure_1814_);
                v___x_1823_ = lean_box(0);
                v___x_1824_ = lean_unsigned_to_nat(1);
                v___x_1825_ = lean_nat_add(v_numCalls_1817_, v___x_1824_);
                lean_dec(v_numCalls_1817_);
                if v_isShared_1821_ == 0 {
                    lean_ctor_set(v___x_1820_, 2, v___x_1825_);
                    v___x_1827_ = v___x_1820_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1833_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 0, v_cur_1815_);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 1, v_added_1816_);
                    lean_ctor_set(v_reuseFailAlloc_1833_, 2, v___x_1825_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1833_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_found_1818_,
                    );
                    v___x_1827_ = v_reuseFailAlloc_1833_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1813_ == 0 {
                    lean_ctor_set(v___x_1812_, 1, v___x_1827_);
                    lean_ctor_set(v___x_1812_, 0, v___x_1823_);
                    v___x_1829_ = v___x_1812_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1832_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1832_, 0, v___x_1823_);
                    lean_ctor_set(v_reuseFailAlloc_1832_, 1, v___x_1827_);
                    v___x_1829_ = v_reuseFailAlloc_1832_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1830_ = lean_apply_2(v_toPure_1814_, lean_box(0), v___x_1829_);
                v___x_1831_ = lean_apply_4(
                    v_toBind_1810_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1836_: *mut LeanObject,
    mut v_inst_1837_: *mut LeanObject,
    mut v_a_1838_: *mut LeanObject,
    mut v_a_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___redArg(
            v_inst_1837_,
            v_a_1839_,
        );
    return v___x_1840_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls___boxed(
    mut v_m_1841_: *mut LeanObject,
    mut v_inst_1842_: *mut LeanObject,
    mut v_a_1843_: *mut LeanObject,
    mut v_a_1844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1845_: *mut LeanObject = core::ptr::null_mut();
    v_res_1845_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_incNumCalls(
        v_m_1841_,
        v_inst_1842_,
        v_a_1843_,
        v_a_1844_,
    );
    lean_dec_ref(v_a_1843_);
    return v_res_1845_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(
    mut v_i_1846_: *mut LeanObject,
    mut v_inst_1847_: *mut LeanObject,
    mut v_a_1848_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1853_: u8 = 0;
    let mut v_toPure_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_1858_: u8 = 0;
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1861_: u8 = 0;
    let mut v___f_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: u8 = 0;
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1876_: u8 = 0;
    let mut v_isSharedCheck_1877_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1849_ = lean_ctor_get(v_inst_1847_, 0);
                v_toBind_1850_ = lean_ctor_get(v_inst_1847_, 1);
                v_isSharedCheck_1877_ = (!lean_is_exclusive(v_inst_1847_)) as u8;
                if v_isSharedCheck_1877_ == 0 {
                    v___x_1852_ = v_inst_1847_;
                    v_isShared_1853_ = v_isSharedCheck_1877_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1850_);
                    lean_inc(v_toApplicative_1849_);
                    lean_dec(v_inst_1847_);
                    v___x_1852_ = lean_box(0);
                    v_isShared_1853_ = v_isSharedCheck_1877_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1854_ = lean_ctor_get(v_toApplicative_1849_, 1);
                lean_inc(v_toPure_1854_);
                lean_dec_ref(v_toApplicative_1849_);
                v_cur_1855_ = lean_ctor_get(v_a_1848_, 0);
                v_added_1856_ = lean_ctor_get(v_a_1848_, 1);
                v_numCalls_1857_ = lean_ctor_get(v_a_1848_, 2);
                v_found_1858_ = lean_ctor_get_uint8(
                    v_a_1848_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1876_ = (!lean_is_exclusive(v_a_1848_)) as u8;
                if v_isSharedCheck_1876_ == 0 {
                    v___x_1860_ = v_a_1848_;
                    v_isShared_1861_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_numCalls_1857_);
                    lean_inc(v_added_1856_);
                    lean_inc(v_cur_1855_);
                    lean_dec(v_a_1848_);
                    v___x_1860_ = lean_box(0);
                    v_isShared_1861_ = v_isSharedCheck_1876_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toPure_1854_);
                v___f_1862_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1862_, 0, v_toPure_1854_);
                v___x_1863_ = lean_box(0);
                v___x_1864_ = 1;
                v___x_1865_ = lean_box((v___x_1864_) as usize);
                v___x_1866_ = lean_array_set(v_cur_1855_, v_i_1846_, v___x_1865_);
                v___x_1867_ = lean_array_push(v_added_1856_, v_i_1846_);
                if v_isShared_1861_ == 0 {
                    lean_ctor_set(v___x_1860_, 1, v___x_1867_);
                    lean_ctor_set(v___x_1860_, 0, v___x_1866_);
                    v___x_1869_ = v___x_1860_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1875_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1866_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1867_);
                    lean_ctor_set(v_reuseFailAlloc_1875_, 2, v_numCalls_1857_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1875_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_found_1858_,
                    );
                    v___x_1869_ = v_reuseFailAlloc_1875_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1853_ == 0 {
                    lean_ctor_set(v___x_1852_, 1, v___x_1869_);
                    lean_ctor_set(v___x_1852_, 0, v___x_1863_);
                    v___x_1871_ = v___x_1852_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1874_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 0, v___x_1863_);
                    lean_ctor_set(v_reuseFailAlloc_1874_, 1, v___x_1869_);
                    v___x_1871_ = v_reuseFailAlloc_1874_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1872_ = lean_apply_2(v_toPure_1854_, lean_box(0), v___x_1871_);
                v___x_1873_ = lean_apply_4(
                    v_toBind_1850_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_m_1878_: *mut LeanObject,
    mut v_i_1879_: *mut LeanObject,
    mut v_inst_1880_: *mut LeanObject,
    mut v_a_1881_: *mut LeanObject,
    mut v_a_1882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1883_: *mut LeanObject = core::ptr::null_mut();
    v___x_1883_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(
        v_i_1879_,
        v_inst_1880_,
        v_a_1882_,
    );
    return v___x_1883_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___boxed(
    mut v_m_1884_: *mut LeanObject,
    mut v_i_1885_: *mut LeanObject,
    mut v_inst_1886_: *mut LeanObject,
    mut v_a_1887_: *mut LeanObject,
    mut v_a_1888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1889_: *mut LeanObject = core::ptr::null_mut();
    v_res_1889_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add(
        v_m_1884_,
        v_i_1885_,
        v_inst_1886_,
        v_a_1887_,
        v_a_1888_,
    );
    lean_dec_ref(v_a_1887_);
    return v_res_1889_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
    mut v_i_1890_: *mut LeanObject,
    mut v_inst_1891_: *mut LeanObject,
    mut v_a_1892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1897_: u8 = 0;
    let mut v_toPure_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_1902_: u8 = 0;
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1905_: u8 = 0;
    let mut v___f_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1908_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1919_: u8 = 0;
    let mut v_isSharedCheck_1920_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1893_ = lean_ctor_get(v_inst_1891_, 0);
                v_toBind_1894_ = lean_ctor_get(v_inst_1891_, 1);
                v_isSharedCheck_1920_ = (!lean_is_exclusive(v_inst_1891_)) as u8;
                if v_isSharedCheck_1920_ == 0 {
                    v___x_1896_ = v_inst_1891_;
                    v_isShared_1897_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1894_);
                    lean_inc(v_toApplicative_1893_);
                    lean_dec(v_inst_1891_);
                    v___x_1896_ = lean_box(0);
                    v_isShared_1897_ = v_isSharedCheck_1920_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1898_ = lean_ctor_get(v_toApplicative_1893_, 1);
                lean_inc(v_toPure_1898_);
                lean_dec_ref(v_toApplicative_1893_);
                v_cur_1899_ = lean_ctor_get(v_a_1892_, 0);
                v_added_1900_ = lean_ctor_get(v_a_1892_, 1);
                v_numCalls_1901_ = lean_ctor_get(v_a_1892_, 2);
                v_found_1902_ = lean_ctor_get_uint8(
                    v_a_1892_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1919_ = (!lean_is_exclusive(v_a_1892_)) as u8;
                if v_isSharedCheck_1919_ == 0 {
                    v___x_1904_ = v_a_1892_;
                    v_isShared_1905_ = v_isSharedCheck_1919_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_numCalls_1901_);
                    lean_inc(v_added_1900_);
                    lean_inc(v_cur_1899_);
                    lean_dec(v_a_1892_);
                    v___x_1904_ = lean_box(0);
                    v_isShared_1905_ = v_isSharedCheck_1919_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toPure_1898_);
                v___f_1906_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1906_, 0, v_toPure_1898_);
                v___x_1907_ = lean_box(0);
                v___x_1908_ = 0;
                v___x_1909_ = lean_box((v___x_1908_) as usize);
                v___x_1910_ = lean_array_set(v_cur_1899_, v_i_1890_, v___x_1909_);
                if v_isShared_1905_ == 0 {
                    lean_ctor_set(v___x_1904_, 0, v___x_1910_);
                    v___x_1912_ = v___x_1904_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1910_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_added_1900_);
                    lean_ctor_set(v_reuseFailAlloc_1918_, 2, v_numCalls_1901_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1918_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_found_1902_,
                    );
                    v___x_1912_ = v_reuseFailAlloc_1918_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1897_ == 0 {
                    lean_ctor_set(v___x_1896_, 1, v___x_1912_);
                    lean_ctor_set(v___x_1896_, 0, v___x_1907_);
                    v___x_1914_ = v___x_1896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1917_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 0, v___x_1907_);
                    lean_ctor_set(v_reuseFailAlloc_1917_, 1, v___x_1912_);
                    v___x_1914_ = v_reuseFailAlloc_1917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1915_ = lean_apply_2(v_toPure_1898_, lean_box(0), v___x_1914_);
                v___x_1916_ = lean_apply_4(
                    v_toBind_1894_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_i_1921_: *mut LeanObject,
    mut v_inst_1922_: *mut LeanObject,
    mut v_a_1923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1924_: *mut LeanObject = core::ptr::null_mut();
    v_res_1924_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
        v_i_1921_,
        v_inst_1922_,
        v_a_1923_,
    );
    lean_dec(v_i_1921_);
    return v_res_1924_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(
    mut v_m_1925_: *mut LeanObject,
    mut v_i_1926_: *mut LeanObject,
    mut v_inst_1927_: *mut LeanObject,
    mut v_a_1928_: *mut LeanObject,
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1930_: *mut LeanObject = core::ptr::null_mut();
    v___x_1930_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(
        v_i_1926_,
        v_inst_1927_,
        v_a_1929_,
    );
    return v___x_1930_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___boxed(
    mut v_m_1931_: *mut LeanObject,
    mut v_i_1932_: *mut LeanObject,
    mut v_inst_1933_: *mut LeanObject,
    mut v_a_1934_: *mut LeanObject,
    mut v_a_1935_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1936_: *mut LeanObject = core::ptr::null_mut();
    v_res_1936_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase(
        v_m_1931_,
        v_i_1932_,
        v_inst_1933_,
        v_a_1934_,
        v_a_1935_,
    );
    lean_dec_ref(v_a_1934_);
    lean_dec(v_i_1932_);
    return v_res_1936_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
    mut v_i_1937_: *mut LeanObject,
    mut v_inst_1938_: *mut LeanObject,
    mut v_a_1939_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1944_: u8 = 0;
    let mut v_toPure_1945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_1949_: u8 = 0;
    let mut v___x_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___f_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: u8 = 0;
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1966_: u8 = 0;
    let mut v_isSharedCheck_1967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toApplicative_1940_ = lean_ctor_get(v_inst_1938_, 0);
                v_toBind_1941_ = lean_ctor_get(v_inst_1938_, 1);
                v_isSharedCheck_1967_ = (!lean_is_exclusive(v_inst_1938_)) as u8;
                if v_isSharedCheck_1967_ == 0 {
                    v___x_1943_ = v_inst_1938_;
                    v_isShared_1944_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_toBind_1941_);
                    lean_inc(v_toApplicative_1940_);
                    lean_dec(v_inst_1938_);
                    v___x_1943_ = lean_box(0);
                    v_isShared_1944_ = v_isSharedCheck_1967_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_toPure_1945_ = lean_ctor_get(v_toApplicative_1940_, 1);
                lean_inc(v_toPure_1945_);
                lean_dec_ref(v_toApplicative_1940_);
                v_cur_1946_ = lean_ctor_get(v_a_1939_, 0);
                v_added_1947_ = lean_ctor_get(v_a_1939_, 1);
                v_numCalls_1948_ = lean_ctor_get(v_a_1939_, 2);
                v_found_1949_ = lean_ctor_get_uint8(
                    v_a_1939_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_isSharedCheck_1966_ = (!lean_is_exclusive(v_a_1939_)) as u8;
                if v_isSharedCheck_1966_ == 0 {
                    v___x_1951_ = v_a_1939_;
                    v_isShared_1952_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_numCalls_1948_);
                    lean_inc(v_added_1947_);
                    lean_inc(v_cur_1946_);
                    lean_dec(v_a_1939_);
                    v___x_1951_ = lean_box(0);
                    v_isShared_1952_ = v_isSharedCheck_1966_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_toPure_1945_);
                v___f_1953_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_1953_, 0, v_toPure_1945_);
                v___x_1954_ = lean_box(0);
                v___x_1955_ = 1;
                v___x_1956_ = lean_box((v___x_1955_) as usize);
                v___x_1957_ = lean_array_set(v_cur_1946_, v_i_1937_, v___x_1956_);
                if v_isShared_1952_ == 0 {
                    lean_ctor_set(v___x_1951_, 0, v___x_1957_);
                    v___x_1959_ = v___x_1951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1965_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1965_, 0, v___x_1957_);
                    lean_ctor_set(v_reuseFailAlloc_1965_, 1, v_added_1947_);
                    lean_ctor_set(v_reuseFailAlloc_1965_, 2, v_numCalls_1948_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_1965_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_found_1949_,
                    );
                    v___x_1959_ = v_reuseFailAlloc_1965_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1944_ == 0 {
                    lean_ctor_set(v___x_1943_, 1, v___x_1959_);
                    lean_ctor_set(v___x_1943_, 0, v___x_1954_);
                    v___x_1961_ = v___x_1943_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1964_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 0, v___x_1954_);
                    lean_ctor_set(v_reuseFailAlloc_1964_, 1, v___x_1959_);
                    v___x_1961_ = v_reuseFailAlloc_1964_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1962_ = lean_apply_2(v_toPure_1945_, lean_box(0), v___x_1961_);
                v___x_1963_ = lean_apply_4(
                    v_toBind_1941_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_i_1968_: *mut LeanObject,
    mut v_inst_1969_: *mut LeanObject,
    mut v_a_1970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1971_: *mut LeanObject = core::ptr::null_mut();
    v_res_1971_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
        v_i_1968_,
        v_inst_1969_,
        v_a_1970_,
    );
    lean_dec(v_i_1968_);
    return v_res_1971_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(
    mut v_m_1972_: *mut LeanObject,
    mut v_i_1973_: *mut LeanObject,
    mut v_inst_1974_: *mut LeanObject,
    mut v_a_1975_: *mut LeanObject,
    mut v_a_1976_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1977_: *mut LeanObject = core::ptr::null_mut();
    v___x_1977_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(
        v_i_1973_,
        v_inst_1974_,
        v_a_1976_,
    );
    return v___x_1977_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___boxed(
    mut v_m_1978_: *mut LeanObject,
    mut v_i_1979_: *mut LeanObject,
    mut v_inst_1980_: *mut LeanObject,
    mut v_a_1981_: *mut LeanObject,
    mut v_a_1982_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1983_: *mut LeanObject = core::ptr::null_mut();
    v_res_1983_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore(
        v_m_1978_,
        v_i_1979_,
        v_inst_1980_,
        v_a_1981_,
        v_a_1982_,
    );
    lean_dec_ref(v_a_1981_);
    lean_dec(v_i_1979_);
    return v_res_1983_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(
    mut v_toPure_1984_: *mut LeanObject,
    mut v___x_1985_: u8,
    mut v_____x_1986_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_1987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1991_: u8 = 0;
    let mut v_a_1992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1995_: u8 = 0;
    let mut v___x_1997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_isSharedCheck_2004_: u8 = 0;
    let mut v_unused_2005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2009_: u8 = 0;
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2012_: u8 = 0;
    let mut v___x_2013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2021_: u8 = 0;
    let mut v_unused_2022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2023_: u8 = 0;
    let mut v_unused_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1987_ = lean_ctor_get(v_____x_1986_, 0);
                lean_inc(v_fst_1987_);
                if lean_obj_tag(v_fst_1987_) == 0 {
                    v_snd_1988_ = lean_ctor_get(v_____x_1986_, 1);
                    v_isSharedCheck_2004_ = (!lean_is_exclusive(v_____x_1986_)) as u8;
                    if v_isSharedCheck_2004_ == 0 {
                        v_unused_2005_ = lean_ctor_get(v_____x_1986_, 0);
                        lean_dec(v_unused_2005_);
                        v___x_1990_ = v_____x_1986_;
                        v_isShared_1991_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_1988_);
                        lean_dec(v_____x_1986_);
                        v___x_1990_ = lean_box(0);
                        v_isShared_1991_ = v_isSharedCheck_2004_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2006_ = lean_ctor_get(v_____x_1986_, 1);
                    v_isSharedCheck_2023_ = (!lean_is_exclusive(v_____x_1986_)) as u8;
                    if v_isSharedCheck_2023_ == 0 {
                        v_unused_2024_ = lean_ctor_get(v_____x_1986_, 0);
                        lean_dec(v_unused_2024_);
                        v___x_2008_ = v_____x_1986_;
                        v_isShared_2009_ = v_isSharedCheck_2023_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2006_);
                        lean_dec(v_____x_1986_);
                        v___x_2008_ = lean_box(0);
                        v_isShared_2009_ = v_isSharedCheck_2023_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1992_ = lean_ctor_get(v_fst_1987_, 0);
                v_isSharedCheck_2003_ = (!lean_is_exclusive(v_fst_1987_)) as u8;
                if v_isSharedCheck_2003_ == 0 {
                    v___x_1994_ = v_fst_1987_;
                    v_isShared_1995_ = v_isSharedCheck_2003_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_1992_);
                    lean_dec(v_fst_1987_);
                    v___x_1994_ = lean_box(0);
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
                    v_reuseFailAlloc_2002_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1992_);
                    v___x_1997_ = v_reuseFailAlloc_2002_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1991_ == 0 {
                    lean_ctor_set(v___x_1990_, 0, v___x_1997_);
                    v___x_1999_ = v___x_1990_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 0, v___x_1997_);
                    lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_snd_1988_);
                    v___x_1999_ = v_reuseFailAlloc_2001_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2000_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_1999_);
                return v___x_2000_;
            }
            5 => {
                v_isSharedCheck_2021_ = (!lean_is_exclusive(v_fst_1987_)) as u8;
                if v_isSharedCheck_2021_ == 0 {
                    v_unused_2022_ = lean_ctor_get(v_fst_1987_, 0);
                    lean_dec(v_unused_2022_);
                    v___x_2011_ = v_fst_1987_;
                    v_isShared_2012_ = v_isSharedCheck_2021_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_fst_1987_);
                    v___x_2011_ = lean_box(0);
                    v_isShared_2012_ = v_isSharedCheck_2021_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2013_ = lean_box((v___x_1985_) as usize);
                if v_isShared_2012_ == 0 {
                    lean_ctor_set(v___x_2011_, 0, v___x_2013_);
                    v___x_2015_ = v___x_2011_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2020_, 0, v___x_2013_);
                    v___x_2015_ = v_reuseFailAlloc_2020_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2009_ == 0 {
                    lean_ctor_set(v___x_2008_, 0, v___x_2015_);
                    v___x_2017_ = v___x_2008_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2019_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 0, v___x_2015_);
                    lean_ctor_set(v_reuseFailAlloc_2019_, 1, v_snd_2006_);
                    v___x_2017_ = v_reuseFailAlloc_2019_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2018_ = lean_apply_2(v_toPure_1984_, lean_box(0), v___x_2017_);
                return v___x_2018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed(
    mut v_toPure_2025_: *mut LeanObject,
    mut v___x_2026_: *mut LeanObject,
    mut v_____x_2027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7305__boxed_2028_: u8 = 0;
    let mut v_res_2029_: *mut LeanObject = core::ptr::null_mut();
    v___x_7305__boxed_2028_ = (lean_unbox(v___x_2026_) as u8);
    v_res_2029_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0(
            v_toPure_2025_,
            v___x_7305__boxed_2028_,
            v_____x_2027_,
        );
    return v_res_2029_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1(
    mut v_toPure_2030_: *mut LeanObject,
    mut v_inst_2031_: *mut LeanObject,
    mut v_toBind_2032_: *mut LeanObject,
    mut v___f_2033_: *mut LeanObject,
    mut v_____x_2034_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2035_: *mut LeanObject = core::ptr::null_mut();
    v_fst_2035_ = lean_ctor_get(v_____x_2034_, 0);
    if lean_obj_tag(v_fst_2035_) == 0 {
        let mut v___x_2036_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_2033_);
        lean_dec(v_toBind_2032_);
        lean_dec_ref(v_inst_2031_);
        v___x_2036_ = lean_apply_2(v_toPure_2030_, lean_box(0), v_____x_2034_);
        return v___x_2036_;
    } else {
        let mut v_a_2037_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2038_: u8 = 0;
        v_a_2037_ = lean_ctor_get(v_fst_2035_, 0);
        v___x_2038_ = (lean_unbox(v_a_2037_) as u8);
        if v___x_2038_ == 0 {
            let mut v___x_2039_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v___f_2033_);
            lean_dec(v_toBind_2032_);
            lean_dec_ref(v_inst_2031_);
            v___x_2039_ = lean_apply_2(v_toPure_2030_, lean_box(0), v_____x_2034_);
            return v___x_2039_;
        } else {
            let mut v_snd_2040_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_2042_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toPure_2030_);
            v_snd_2040_ = lean_ctor_get(v_____x_2034_, 1);
            lean_inc(v_snd_2040_);
            lean_dec_ref(v_____x_2034_);
            v___x_2041_ =
                l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg(
                    v_inst_2031_,
                    v_snd_2040_,
                );
            v___x_2042_ = lean_apply_4(
                v_toBind_2032_,
                lean_box(0),
                lean_box(0),
                v___x_2041_,
                v___f_2033_,
            );
            return v___x_2042_;
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2(
    mut v_toPure_2043_: *mut LeanObject,
    mut v_____x_2044_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2049_: u8 = 0;
    let mut v___x_2050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2055_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2045_ = lean_ctor_get(v_____x_2044_, 0);
                v_snd_2046_ = lean_ctor_get(v_____x_2044_, 1);
                v_isSharedCheck_2055_ = (!lean_is_exclusive(v_____x_2044_)) as u8;
                if v_isSharedCheck_2055_ == 0 {
                    v___x_2048_ = v_____x_2044_;
                    v_isShared_2049_ = v_isSharedCheck_2055_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2046_);
                    lean_inc(v_fst_2045_);
                    lean_dec(v_____x_2044_);
                    v___x_2048_ = lean_box(0);
                    v_isShared_2049_ = v_isSharedCheck_2055_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2050_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2050_, 0, v_fst_2045_);
                if v_isShared_2049_ == 0 {
                    lean_ctor_set(v___x_2048_, 0, v___x_2050_);
                    v___x_2052_ = v___x_2048_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 0, v___x_2050_);
                    lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_snd_2046_);
                    v___x_2052_ = v_reuseFailAlloc_2054_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2053_ = lean_apply_2(v_toPure_2043_, lean_box(0), v___x_2052_);
                return v___x_2053_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(
    mut v_snd_2056_: *mut LeanObject,
    mut v_toPure_2057_: *mut LeanObject,
    mut v_a_2058_: u8,
) -> *mut LeanObject {
    let mut v___x_2059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut LeanObject = core::ptr::null_mut();
    v___x_2059_ = lean_box((v_a_2058_) as usize);
    v___x_2060_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2060_, 0, v___x_2059_);
    lean_ctor_set(v___x_2060_, 1, v_snd_2056_);
    v___x_2061_ = lean_apply_2(v_toPure_2057_, lean_box(0), v___x_2060_);
    return v___x_2061_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed(
    mut v_snd_2062_: *mut LeanObject,
    mut v_toPure_2063_: *mut LeanObject,
    mut v_a_2064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_2065_: u8 = 0;
    let mut v_res_2066_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_2065_ = (lean_unbox(v_a_2064_) as u8);
    v_res_2066_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3(
            v_snd_2062_,
            v_toPure_2063_,
            v_a_boxed_2065_,
        );
    return v_res_2066_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4(
    mut v_toPure_2067_: *mut LeanObject,
    mut v_a_2068_: *mut LeanObject,
    mut v_toBind_2069_: *mut LeanObject,
    mut v___f_2070_: *mut LeanObject,
    mut v_____x_2071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2076_: u8 = 0;
    let mut v_a_2077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2080_: u8 = 0;
    let mut v___x_2082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2088_: u8 = 0;
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_unused_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_test_2093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_2094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2100_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2072_ = lean_ctor_get(v_____x_2071_, 0);
                lean_inc(v_fst_2072_);
                if lean_obj_tag(v_fst_2072_) == 0 {
                    lean_dec(v___f_2070_);
                    lean_dec(v_toBind_2069_);
                    lean_dec_ref(v_a_2068_);
                    v_snd_2073_ = lean_ctor_get(v_____x_2071_, 1);
                    v_isSharedCheck_2089_ = (!lean_is_exclusive(v_____x_2071_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v_unused_2090_ = lean_ctor_get(v_____x_2071_, 0);
                        lean_dec(v_unused_2090_);
                        v___x_2075_ = v_____x_2071_;
                        v_isShared_2076_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2073_);
                        lean_dec(v_____x_2071_);
                        v___x_2075_ = lean_box(0);
                        v_isShared_2076_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2091_ = lean_ctor_get(v_fst_2072_, 0);
                    lean_inc(v_a_2091_);
                    lean_dec_ref_known(v_fst_2072_, 1);
                    v_snd_2092_ = lean_ctor_get(v_____x_2071_, 1);
                    lean_inc(v_snd_2092_);
                    lean_dec_ref(v_____x_2071_);
                    v_test_2093_ = lean_ctor_get(v_a_2068_, 1);
                    lean_inc(v_test_2093_);
                    lean_dec_ref(v_a_2068_);
                    v_cur_2094_ = lean_ctor_get(v_a_2091_, 0);
                    lean_inc_ref(v_cur_2094_);
                    lean_dec(v_a_2091_);
                    v___x_2095_ = lean_apply_1(v_test_2093_, v_cur_2094_);
                    lean_inc(v_toPure_2067_);
                    v___f_2096_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__2 as *mut core::ffi::c_void, 2, 1);
                    lean_closure_set(v___f_2096_, 0, v_toPure_2067_);
                    v___f_2097_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__3___boxed as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2097_, 0, v_snd_2092_);
                    lean_closure_set(v___f_2097_, 1, v_toPure_2067_);
                    lean_inc_n(v_toBind_2069_, 2);
                    v___x_2098_ = lean_apply_4(
                        v_toBind_2069_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2095_,
                        v___f_2097_,
                    );
                    v___x_2099_ = lean_apply_4(
                        v_toBind_2069_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2098_,
                        v___f_2096_,
                    );
                    v___x_2100_ = lean_apply_4(
                        v_toBind_2069_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2099_,
                        v___f_2070_,
                    );
                    return v___x_2100_;
                }
            }
            1 => {
                v_a_2077_ = lean_ctor_get(v_fst_2072_, 0);
                v_isSharedCheck_2088_ = (!lean_is_exclusive(v_fst_2072_)) as u8;
                if v_isSharedCheck_2088_ == 0 {
                    v___x_2079_ = v_fst_2072_;
                    v_isShared_2080_ = v_isSharedCheck_2088_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2077_);
                    lean_dec(v_fst_2072_);
                    v___x_2079_ = lean_box(0);
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
                    v_reuseFailAlloc_2087_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2087_, 0, v_a_2077_);
                    v___x_2082_ = v_reuseFailAlloc_2087_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2076_ == 0 {
                    lean_ctor_set(v___x_2075_, 0, v___x_2082_);
                    v___x_2084_ = v___x_2075_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2086_, 0, v___x_2082_);
                    lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_snd_2073_);
                    v___x_2084_ = v_reuseFailAlloc_2086_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2085_ = lean_apply_2(v_toPure_2067_, lean_box(0), v___x_2084_);
                return v___x_2085_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5(
    mut v_toPure_2101_: *mut LeanObject,
    mut v_____x_2102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2107_: u8 = 0;
    let mut v___x_2108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2103_ = lean_ctor_get(v_____x_2102_, 0);
                v_snd_2104_ = lean_ctor_get(v_____x_2102_, 1);
                v_isSharedCheck_2113_ = (!lean_is_exclusive(v_____x_2102_)) as u8;
                if v_isSharedCheck_2113_ == 0 {
                    v___x_2106_ = v_____x_2102_;
                    v_isShared_2107_ = v_isSharedCheck_2113_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2104_);
                    lean_inc(v_fst_2103_);
                    lean_dec(v_____x_2102_);
                    v___x_2106_ = lean_box(0);
                    v_isShared_2107_ = v_isSharedCheck_2113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2108_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2108_, 0, v_fst_2103_);
                if v_isShared_2107_ == 0 {
                    lean_ctor_set(v___x_2106_, 0, v___x_2108_);
                    v___x_2110_ = v___x_2106_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2112_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2112_, 0, v___x_2108_);
                    lean_ctor_set(v_reuseFailAlloc_2112_, 1, v_snd_2104_);
                    v___x_2110_ = v_reuseFailAlloc_2112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2111_ = lean_apply_2(v_toPure_2101_, lean_box(0), v___x_2110_);
                return v___x_2111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6(
    mut v_toPure_2114_: *mut LeanObject,
    mut v_toBind_2115_: *mut LeanObject,
    mut v___f_2116_: *mut LeanObject,
    mut v_____x_2117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2122_: u8 = 0;
    let mut v_a_2123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2126_: u8 = 0;
    let mut v___x_2128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2134_: u8 = 0;
    let mut v_isSharedCheck_2135_: u8 = 0;
    let mut v_unused_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2140_: u8 = 0;
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2150_: u8 = 0;
    let mut v_unused_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2118_ = lean_ctor_get(v_____x_2117_, 0);
                lean_inc(v_fst_2118_);
                if lean_obj_tag(v_fst_2118_) == 0 {
                    lean_dec(v___f_2116_);
                    lean_dec(v_toBind_2115_);
                    v_snd_2119_ = lean_ctor_get(v_____x_2117_, 1);
                    v_isSharedCheck_2135_ = (!lean_is_exclusive(v_____x_2117_)) as u8;
                    if v_isSharedCheck_2135_ == 0 {
                        v_unused_2136_ = lean_ctor_get(v_____x_2117_, 0);
                        lean_dec(v_unused_2136_);
                        v___x_2121_ = v_____x_2117_;
                        v_isShared_2122_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2119_);
                        lean_dec(v_____x_2117_);
                        v___x_2121_ = lean_box(0);
                        v_isShared_2122_ = v_isSharedCheck_2135_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2137_ = lean_ctor_get(v_____x_2117_, 1);
                    v_isSharedCheck_2150_ = (!lean_is_exclusive(v_____x_2117_)) as u8;
                    if v_isSharedCheck_2150_ == 0 {
                        v_unused_2151_ = lean_ctor_get(v_____x_2117_, 0);
                        lean_dec(v_unused_2151_);
                        v___x_2139_ = v_____x_2117_;
                        v_isShared_2140_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2137_);
                        lean_dec(v_____x_2117_);
                        v___x_2139_ = lean_box(0);
                        v_isShared_2140_ = v_isSharedCheck_2150_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2123_ = lean_ctor_get(v_fst_2118_, 0);
                v_isSharedCheck_2134_ = (!lean_is_exclusive(v_fst_2118_)) as u8;
                if v_isSharedCheck_2134_ == 0 {
                    v___x_2125_ = v_fst_2118_;
                    v_isShared_2126_ = v_isSharedCheck_2134_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2123_);
                    lean_dec(v_fst_2118_);
                    v___x_2125_ = lean_box(0);
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
                    v_reuseFailAlloc_2133_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2133_, 0, v_a_2123_);
                    v___x_2128_ = v_reuseFailAlloc_2133_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2122_ == 0 {
                    lean_ctor_set(v___x_2121_, 0, v___x_2128_);
                    v___x_2130_ = v___x_2121_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2132_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2132_, 0, v___x_2128_);
                    lean_ctor_set(v_reuseFailAlloc_2132_, 1, v_snd_2119_);
                    v___x_2130_ = v_reuseFailAlloc_2132_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2131_ = lean_apply_2(v_toPure_2114_, lean_box(0), v___x_2130_);
                return v___x_2131_;
            }
            5 => {
                v_a_2141_ = lean_ctor_get(v_fst_2118_, 0);
                lean_inc(v_a_2141_);
                lean_dec_ref_known(v_fst_2118_, 1);
                lean_inc(v_toBind_2115_);
                lean_inc_n(v_toPure_2114_, 2);
                v___f_2142_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__4 as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_2142_, 0, v_toPure_2114_);
                lean_closure_set(v___f_2142_, 1, v_a_2141_);
                lean_closure_set(v___f_2142_, 2, v_toBind_2115_);
                lean_closure_set(v___f_2142_, 3, v___f_2116_);
                v___f_2143_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_2143_, 0, v_toPure_2114_);
                lean_inc(v_snd_2137_);
                if v_isShared_2140_ == 0 {
                    lean_ctor_set(v___x_2139_, 0, v_snd_2137_);
                    v___x_2145_ = v___x_2139_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2149_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 0, v_snd_2137_);
                    lean_ctor_set(v_reuseFailAlloc_2149_, 1, v_snd_2137_);
                    v___x_2145_ = v_reuseFailAlloc_2149_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2146_ = lean_apply_2(v_toPure_2114_, lean_box(0), v___x_2145_);
                lean_inc(v_toBind_2115_);
                v___x_2147_ = lean_apply_4(
                    v_toBind_2115_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2146_,
                    v___f_2143_,
                );
                v___x_2148_ = lean_apply_4(
                    v_toBind_2115_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_toPure_2152_: *mut LeanObject,
    mut v_a_2153_: *mut LeanObject,
    mut v_toBind_2154_: *mut LeanObject,
    mut v___f_2155_: *mut LeanObject,
    mut v_____x_2156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2161_: u8 = 0;
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2173_: u8 = 0;
    let mut v_isSharedCheck_2174_: u8 = 0;
    let mut v_unused_2175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2179_: u8 = 0;
    let mut v___x_2181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2182_: u8 = 0;
    let mut v___x_2184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2191_: u8 = 0;
    let mut v_unused_2192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2193_: u8 = 0;
    let mut v_unused_2194_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2157_ = lean_ctor_get(v_____x_2156_, 0);
                lean_inc(v_fst_2157_);
                if lean_obj_tag(v_fst_2157_) == 0 {
                    lean_dec(v___f_2155_);
                    lean_dec(v_toBind_2154_);
                    v_snd_2158_ = lean_ctor_get(v_____x_2156_, 1);
                    v_isSharedCheck_2174_ = (!lean_is_exclusive(v_____x_2156_)) as u8;
                    if v_isSharedCheck_2174_ == 0 {
                        v_unused_2175_ = lean_ctor_get(v_____x_2156_, 0);
                        lean_dec(v_unused_2175_);
                        v___x_2160_ = v_____x_2156_;
                        v_isShared_2161_ = v_isSharedCheck_2174_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2158_);
                        lean_dec(v_____x_2156_);
                        v___x_2160_ = lean_box(0);
                        v_isShared_2161_ = v_isSharedCheck_2174_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2176_ = lean_ctor_get(v_____x_2156_, 1);
                    v_isSharedCheck_2193_ = (!lean_is_exclusive(v_____x_2156_)) as u8;
                    if v_isSharedCheck_2193_ == 0 {
                        v_unused_2194_ = lean_ctor_get(v_____x_2156_, 0);
                        lean_dec(v_unused_2194_);
                        v___x_2178_ = v_____x_2156_;
                        v_isShared_2179_ = v_isSharedCheck_2193_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2176_);
                        lean_dec(v_____x_2156_);
                        v___x_2178_ = lean_box(0);
                        v_isShared_2179_ = v_isSharedCheck_2193_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2162_ = lean_ctor_get(v_fst_2157_, 0);
                v_isSharedCheck_2173_ = (!lean_is_exclusive(v_fst_2157_)) as u8;
                if v_isSharedCheck_2173_ == 0 {
                    v___x_2164_ = v_fst_2157_;
                    v_isShared_2165_ = v_isSharedCheck_2173_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2162_);
                    lean_dec(v_fst_2157_);
                    v___x_2164_ = lean_box(0);
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
                    v_reuseFailAlloc_2172_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2172_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2172_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2161_ == 0 {
                    lean_ctor_set(v___x_2160_, 0, v___x_2167_);
                    v___x_2169_ = v___x_2160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2171_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 0, v___x_2167_);
                    lean_ctor_set(v_reuseFailAlloc_2171_, 1, v_snd_2158_);
                    v___x_2169_ = v_reuseFailAlloc_2171_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2170_ = lean_apply_2(v_toPure_2152_, lean_box(0), v___x_2169_);
                return v___x_2170_;
            }
            5 => {
                v_isSharedCheck_2191_ = (!lean_is_exclusive(v_fst_2157_)) as u8;
                if v_isSharedCheck_2191_ == 0 {
                    v_unused_2192_ = lean_ctor_get(v_fst_2157_, 0);
                    lean_dec(v_unused_2192_);
                    v___x_2181_ = v_fst_2157_;
                    v_isShared_2182_ = v_isSharedCheck_2191_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_fst_2157_);
                    v___x_2181_ = lean_box(0);
                    v_isShared_2182_ = v_isSharedCheck_2191_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                lean_inc_ref(v_a_2153_);
                if v_isShared_2182_ == 0 {
                    lean_ctor_set(v___x_2181_, 0, v_a_2153_);
                    v___x_2184_ = v___x_2181_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2190_, 0, v_a_2153_);
                    v___x_2184_ = v_reuseFailAlloc_2190_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2179_ == 0 {
                    lean_ctor_set(v___x_2178_, 0, v___x_2184_);
                    v___x_2186_ = v___x_2178_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2184_);
                    lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_snd_2176_);
                    v___x_2186_ = v_reuseFailAlloc_2189_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2187_ = lean_apply_2(v_toPure_2152_, lean_box(0), v___x_2186_);
                v___x_2188_ = lean_apply_4(
                    v_toBind_2154_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_toPure_2195_: *mut LeanObject,
    mut v_a_2196_: *mut LeanObject,
    mut v_toBind_2197_: *mut LeanObject,
    mut v___f_2198_: *mut LeanObject,
    mut v_____x_2199_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2200_: *mut LeanObject = core::ptr::null_mut();
    v_res_2200_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7(
            v_toPure_2195_,
            v_a_2196_,
            v_toBind_2197_,
            v___f_2198_,
            v_____x_2199_,
        );
    lean_dec_ref(v_a_2196_);
    return v_res_2200_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(
    mut v_toPure_2203_: *mut LeanObject,
    mut v_inst_2204_: *mut LeanObject,
    mut v_toBind_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_maxCalls_2207_: *mut LeanObject,
    mut v_____x_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2213_: u8 = 0;
    let mut v___y_2215_: u8 = 0;
    let mut v_cur_2216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_2218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_2219_: u8 = 0;
    let mut v___x_2221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2222_: u8 = 0;
    let mut v___x_2223_: u8 = 0;
    let mut v___x_2224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2242_: u8 = 0;
    let mut v___x_2243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2251_: u8 = 0;
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2257_: u8 = 0;
    let mut v_a_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2260_: u8 = 0;
    let mut v_numCalls_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: u8 = 0;
    let mut v_isSharedCheck_2263_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2209_ = lean_ctor_get(v_____x_2208_, 0);
                v_snd_2210_ = lean_ctor_get(v_____x_2208_, 1);
                v_isSharedCheck_2263_ = (!lean_is_exclusive(v_____x_2208_)) as u8;
                if v_isSharedCheck_2263_ == 0 {
                    v___x_2212_ = v_____x_2208_;
                    v_isShared_2213_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_2210_);
                    lean_inc(v_fst_2209_);
                    lean_dec(v_____x_2208_);
                    v___x_2212_ = lean_box(0);
                    v_isShared_2213_ = v_isSharedCheck_2263_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if lean_obj_tag(v_fst_2209_) == 0 {
                    lean_del_object(v___x_2212_);
                    lean_dec(v_toBind_2205_);
                    lean_dec_ref(v_inst_2204_);
                    v_a_2248_ = lean_ctor_get(v_fst_2209_, 0);
                    v_isSharedCheck_2257_ = (!lean_is_exclusive(v_fst_2209_)) as u8;
                    if v_isSharedCheck_2257_ == 0 {
                        v___x_2250_ = v_fst_2209_;
                        v_isShared_2251_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_2248_);
                        lean_dec(v_fst_2209_);
                        v___x_2250_ = lean_box(0);
                        v_isShared_2251_ = v_isSharedCheck_2257_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_a_2258_ = lean_ctor_get(v_fst_2209_, 0);
                    lean_inc(v_a_2258_);
                    lean_dec_ref_known(v_fst_2209_, 1);
                    v___x_2259_ = lean_unsigned_to_nat(0);
                    v___x_2260_ = lean_nat_dec_lt(v___x_2259_, v_maxCalls_2207_);
                    if v___x_2260_ == 0 {
                        lean_dec(v_a_2258_);
                        v___y_2215_ = v___x_2260_;
                        state = 2;
                        continue;
                    } else {
                        v_numCalls_2261_ = lean_ctor_get(v_a_2258_, 2);
                        lean_inc(v_numCalls_2261_);
                        lean_dec(v_a_2258_);
                        v___x_2262_ = lean_nat_dec_le(v_maxCalls_2207_, v_numCalls_2261_);
                        lean_dec(v_numCalls_2261_);
                        v___y_2215_ = v___x_2262_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v___y_2215_ == 0 {
                    v_cur_2216_ = lean_ctor_get(v_snd_2210_, 0);
                    v_added_2217_ = lean_ctor_get(v_snd_2210_, 1);
                    v_numCalls_2218_ = lean_ctor_get(v_snd_2210_, 2);
                    v_found_2219_ = lean_ctor_get_uint8(
                        v_snd_2210_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    v_isSharedCheck_2242_ = (!lean_is_exclusive(v_snd_2210_)) as u8;
                    if v_isSharedCheck_2242_ == 0 {
                        v___x_2221_ = v_snd_2210_;
                        v_isShared_2222_ = v_isSharedCheck_2242_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_numCalls_2218_);
                        lean_inc(v_added_2217_);
                        lean_inc(v_cur_2216_);
                        lean_dec(v_snd_2210_);
                        v___x_2221_ = lean_box(0);
                        v_isShared_2222_ = v_isSharedCheck_2242_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_toBind_2205_);
                    lean_dec_ref(v_inst_2204_);
                    v___x_2243_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___closed__0;
                    if v_isShared_2213_ == 0 {
                        lean_ctor_set(v___x_2212_, 0, v___x_2243_);
                        v___x_2245_ = v___x_2212_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2247_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2247_, 0, v___x_2243_);
                        lean_ctor_set(v_reuseFailAlloc_2247_, 1, v_snd_2210_);
                        v___x_2245_ = v_reuseFailAlloc_2247_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_2223_ = 1;
                v___x_2224_ = lean_box((v___x_2223_) as usize);
                lean_inc_n(v_toPure_2203_, 5);
                v___f_2225_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                lean_closure_set(v___f_2225_, 0, v_toPure_2203_);
                lean_closure_set(v___f_2225_, 1, v___x_2224_);
                lean_inc_n(v_toBind_2205_, 3);
                v___f_2226_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__1 as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_2226_, 0, v_toPure_2203_);
                lean_closure_set(v___f_2226_, 1, v_inst_2204_);
                lean_closure_set(v___f_2226_, 2, v_toBind_2205_);
                lean_closure_set(v___f_2226_, 3, v___f_2225_);
                v___f_2227_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__6 as *mut core::ffi::c_void, 4, 3);
                lean_closure_set(v___f_2227_, 0, v_toPure_2203_);
                lean_closure_set(v___f_2227_, 1, v_toBind_2205_);
                lean_closure_set(v___f_2227_, 2, v___f_2226_);
                lean_inc_ref(v_a_2206_);
                v___f_2228_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__7___boxed as *mut core::ffi::c_void, 5, 4);
                lean_closure_set(v___f_2228_, 0, v_toPure_2203_);
                lean_closure_set(v___f_2228_, 1, v_a_2206_);
                lean_closure_set(v___f_2228_, 2, v_toBind_2205_);
                lean_closure_set(v___f_2228_, 3, v___f_2227_);
                v___f_2229_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_markFound___redArg___lam__0 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_2229_, 0, v_toPure_2203_);
                v___x_2230_ = lean_box(0);
                v___x_2231_ = lean_unsigned_to_nat(1);
                v___x_2232_ = lean_nat_add(v_numCalls_2218_, v___x_2231_);
                lean_dec(v_numCalls_2218_);
                if v_isShared_2222_ == 0 {
                    lean_ctor_set(v___x_2221_, 2, v___x_2232_);
                    v___x_2234_ = v___x_2221_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 0, v_cur_2216_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 1, v_added_2217_);
                    lean_ctor_set(v_reuseFailAlloc_2241_, 2, v___x_2232_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_2241_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_found_2219_,
                    );
                    v___x_2234_ = v_reuseFailAlloc_2241_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_2213_ == 0 {
                    lean_ctor_set(v___x_2212_, 1, v___x_2234_);
                    lean_ctor_set(v___x_2212_, 0, v___x_2230_);
                    v___x_2236_ = v___x_2212_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2240_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 0, v___x_2230_);
                    lean_ctor_set(v_reuseFailAlloc_2240_, 1, v___x_2234_);
                    v___x_2236_ = v_reuseFailAlloc_2240_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2237_ = lean_apply_2(v_toPure_2203_, lean_box(0), v___x_2236_);
                lean_inc(v_toBind_2205_);
                v___x_2238_ = lean_apply_4(
                    v_toBind_2205_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2237_,
                    v___f_2229_,
                );
                v___x_2239_ = lean_apply_4(
                    v_toBind_2205_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2238_,
                    v___f_2228_,
                );
                return v___x_2239_;
            }
            6 => {
                v___x_2246_ = lean_apply_2(v_toPure_2203_, lean_box(0), v___x_2245_);
                return v___x_2246_;
            }
            7 => {
                if v_isShared_2251_ == 0 {
                    v___x_2253_ = v___x_2250_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2256_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2248_);
                    v___x_2253_ = v_reuseFailAlloc_2256_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2254_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2254_, 0, v___x_2253_);
                lean_ctor_set(v___x_2254_, 1, v_snd_2210_);
                v___x_2255_ = lean_apply_2(v_toPure_2203_, lean_box(0), v___x_2254_);
                return v___x_2255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed(
    mut v_toPure_2264_: *mut LeanObject,
    mut v_inst_2265_: *mut LeanObject,
    mut v_toBind_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_maxCalls_2268_: *mut LeanObject,
    mut v_____x_2269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2270_: *mut LeanObject = core::ptr::null_mut();
    v_res_2270_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9(
            v_toPure_2264_,
            v_inst_2265_,
            v_toBind_2266_,
            v_a_2267_,
            v_maxCalls_2268_,
            v_____x_2269_,
        );
    lean_dec(v_maxCalls_2268_);
    lean_dec_ref(v_a_2267_);
    return v_res_2270_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(
    mut v_toPure_2271_: *mut LeanObject,
    mut v_inst_2272_: *mut LeanObject,
    mut v_toBind_2273_: *mut LeanObject,
    mut v_a_2274_: *mut LeanObject,
    mut v_____x_2275_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2280_: u8 = 0;
    let mut v_a_2281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2284_: u8 = 0;
    let mut v___x_2286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2292_: u8 = 0;
    let mut v_isSharedCheck_2293_: u8 = 0;
    let mut v_unused_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v_maxCalls_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2309_: u8 = 0;
    let mut v_unused_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2276_ = lean_ctor_get(v_____x_2275_, 0);
                lean_inc(v_fst_2276_);
                if lean_obj_tag(v_fst_2276_) == 0 {
                    lean_dec(v_toBind_2273_);
                    lean_dec_ref(v_inst_2272_);
                    v_snd_2277_ = lean_ctor_get(v_____x_2275_, 1);
                    v_isSharedCheck_2293_ = (!lean_is_exclusive(v_____x_2275_)) as u8;
                    if v_isSharedCheck_2293_ == 0 {
                        v_unused_2294_ = lean_ctor_get(v_____x_2275_, 0);
                        lean_dec(v_unused_2294_);
                        v___x_2279_ = v_____x_2275_;
                        v_isShared_2280_ = v_isSharedCheck_2293_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2277_);
                        lean_dec(v_____x_2275_);
                        v___x_2279_ = lean_box(0);
                        v_isShared_2280_ = v_isSharedCheck_2293_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2295_ = lean_ctor_get(v_fst_2276_, 0);
                    lean_inc(v_a_2295_);
                    lean_dec_ref_known(v_fst_2276_, 1);
                    v_snd_2296_ = lean_ctor_get(v_____x_2275_, 1);
                    v_isSharedCheck_2309_ = (!lean_is_exclusive(v_____x_2275_)) as u8;
                    if v_isSharedCheck_2309_ == 0 {
                        v_unused_2310_ = lean_ctor_get(v_____x_2275_, 0);
                        lean_dec(v_unused_2310_);
                        v___x_2298_ = v_____x_2275_;
                        v_isShared_2299_ = v_isSharedCheck_2309_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2296_);
                        lean_dec(v_____x_2275_);
                        v___x_2298_ = lean_box(0);
                        v_isShared_2299_ = v_isSharedCheck_2309_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2281_ = lean_ctor_get(v_fst_2276_, 0);
                v_isSharedCheck_2292_ = (!lean_is_exclusive(v_fst_2276_)) as u8;
                if v_isSharedCheck_2292_ == 0 {
                    v___x_2283_ = v_fst_2276_;
                    v_isShared_2284_ = v_isSharedCheck_2292_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2281_);
                    lean_dec(v_fst_2276_);
                    v___x_2283_ = lean_box(0);
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
                    v_reuseFailAlloc_2291_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2281_);
                    v___x_2286_ = v_reuseFailAlloc_2291_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2280_ == 0 {
                    lean_ctor_set(v___x_2279_, 0, v___x_2286_);
                    v___x_2288_ = v___x_2279_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2290_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2290_, 0, v___x_2286_);
                    lean_ctor_set(v_reuseFailAlloc_2290_, 1, v_snd_2277_);
                    v___x_2288_ = v_reuseFailAlloc_2290_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2289_ = lean_apply_2(v_toPure_2271_, lean_box(0), v___x_2288_);
                return v___x_2289_;
            }
            5 => {
                v_maxCalls_2300_ = lean_ctor_get(v_a_2295_, 2);
                lean_inc(v_maxCalls_2300_);
                lean_dec(v_a_2295_);
                lean_inc_ref(v_a_2274_);
                lean_inc(v_toBind_2273_);
                lean_inc_n(v_toPure_2271_, 2);
                v___f_2301_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__9___boxed as *mut core::ffi::c_void, 6, 5);
                lean_closure_set(v___f_2301_, 0, v_toPure_2271_);
                lean_closure_set(v___f_2301_, 1, v_inst_2272_);
                lean_closure_set(v___f_2301_, 2, v_toBind_2273_);
                lean_closure_set(v___f_2301_, 3, v_a_2274_);
                lean_closure_set(v___f_2301_, 4, v_maxCalls_2300_);
                v___f_2302_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_2302_, 0, v_toPure_2271_);
                lean_inc(v_snd_2296_);
                if v_isShared_2299_ == 0 {
                    lean_ctor_set(v___x_2298_, 0, v_snd_2296_);
                    v___x_2304_ = v___x_2298_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2308_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 0, v_snd_2296_);
                    lean_ctor_set(v_reuseFailAlloc_2308_, 1, v_snd_2296_);
                    v___x_2304_ = v_reuseFailAlloc_2308_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2305_ = lean_apply_2(v_toPure_2271_, lean_box(0), v___x_2304_);
                lean_inc(v_toBind_2273_);
                v___x_2306_ = lean_apply_4(
                    v_toBind_2273_,
                    lean_box(0),
                    lean_box(0),
                    v___x_2305_,
                    v___f_2302_,
                );
                v___x_2307_ = lean_apply_4(
                    v_toBind_2273_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_toPure_2311_: *mut LeanObject,
    mut v_inst_2312_: *mut LeanObject,
    mut v_toBind_2313_: *mut LeanObject,
    mut v_a_2314_: *mut LeanObject,
    mut v_____x_2315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2316_: *mut LeanObject = core::ptr::null_mut();
    v_res_2316_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10(
            v_toPure_2311_,
            v_inst_2312_,
            v_toBind_2313_,
            v_a_2314_,
            v_____x_2315_,
        );
    lean_dec_ref(v_a_2314_);
    return v_res_2316_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
    mut v_inst_2317_: *mut LeanObject,
    mut v_a_2318_: *mut LeanObject,
    mut v_a_2319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2320_ = lean_ctor_get(v_inst_2317_, 0);
    v_toBind_2321_ = lean_ctor_get(v_inst_2317_, 1);
    lean_inc_n(v_toBind_2321_, 2);
    v_toPure_2322_ = lean_ctor_get(v_toApplicative_2320_, 1);
    lean_inc_n(v_toPure_2322_, 2);
    lean_inc_ref_n(v_a_2318_, 2);
    v___f_2323_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__10___boxed as *mut core::ffi::c_void, 5, 4);
    lean_closure_set(v___f_2323_, 0, v_toPure_2322_);
    lean_closure_set(v___f_2323_, 1, v_inst_2317_);
    lean_closure_set(v___f_2323_, 2, v_toBind_2321_);
    lean_closure_set(v___f_2323_, 3, v_a_2318_);
    v___x_2324_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2324_, 0, v_a_2318_);
    v___x_2325_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2325_, 0, v___x_2324_);
    lean_ctor_set(v___x_2325_, 1, v_a_2319_);
    v___x_2326_ = lean_apply_2(v_toPure_2322_, lean_box(0), v___x_2325_);
    v___x_2327_ = lean_apply_4(
        v_toBind_2321_,
        lean_box(0),
        lean_box(0),
        v___x_2326_,
        v___f_2323_,
    );
    return v___x_2327_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___boxed(
    mut v_inst_2328_: *mut LeanObject,
    mut v_a_2329_: *mut LeanObject,
    mut v_a_2330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2331_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2328_,
        v_a_2329_,
        v_a_2330_,
    );
    lean_dec_ref(v_a_2329_);
    return v_res_2331_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(
    mut v_m_2332_: *mut LeanObject,
    mut v_inst_2333_: *mut LeanObject,
    mut v_a_2334_: *mut LeanObject,
    mut v_a_2335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2336_: *mut LeanObject = core::ptr::null_mut();
    v___x_2336_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2333_,
        v_a_2334_,
        v_a_2335_,
    );
    return v___x_2336_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___boxed(
    mut v_m_2337_: *mut LeanObject,
    mut v_inst_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2341_: *mut LeanObject = core::ptr::null_mut();
    v_res_2341_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur(
        v_m_2337_,
        v_inst_2338_,
        v_a_2339_,
        v_a_2340_,
    );
    lean_dec_ref(v_a_2339_);
    return v_res_2341_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0(
    mut v_toPure_2342_: *mut LeanObject,
    mut v_____x_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2348_: u8 = 0;
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2360_: u8 = 0;
    let mut v_isSharedCheck_2361_: u8 = 0;
    let mut v_unused_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v_a_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2370_: u8 = 0;
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut v_isSharedCheck_2379_: u8 = 0;
    let mut v_unused_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2344_ = lean_ctor_get(v_____x_2343_, 0);
                lean_inc(v_fst_2344_);
                if lean_obj_tag(v_fst_2344_) == 0 {
                    v_snd_2345_ = lean_ctor_get(v_____x_2343_, 1);
                    v_isSharedCheck_2361_ = (!lean_is_exclusive(v_____x_2343_)) as u8;
                    if v_isSharedCheck_2361_ == 0 {
                        v_unused_2362_ = lean_ctor_get(v_____x_2343_, 0);
                        lean_dec(v_unused_2362_);
                        v___x_2347_ = v_____x_2343_;
                        v_isShared_2348_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2345_);
                        lean_dec(v_____x_2343_);
                        v___x_2347_ = lean_box(0);
                        v_isShared_2348_ = v_isSharedCheck_2361_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2363_ = lean_ctor_get(v_____x_2343_, 1);
                    v_isSharedCheck_2379_ = (!lean_is_exclusive(v_____x_2343_)) as u8;
                    if v_isSharedCheck_2379_ == 0 {
                        v_unused_2380_ = lean_ctor_get(v_____x_2343_, 0);
                        lean_dec(v_unused_2380_);
                        v___x_2365_ = v_____x_2343_;
                        v_isShared_2366_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2363_);
                        lean_dec(v_____x_2343_);
                        v___x_2365_ = lean_box(0);
                        v_isShared_2366_ = v_isSharedCheck_2379_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2349_ = lean_ctor_get(v_fst_2344_, 0);
                v_isSharedCheck_2360_ = (!lean_is_exclusive(v_fst_2344_)) as u8;
                if v_isSharedCheck_2360_ == 0 {
                    v___x_2351_ = v_fst_2344_;
                    v_isShared_2352_ = v_isSharedCheck_2360_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2349_);
                    lean_dec(v_fst_2344_);
                    v___x_2351_ = lean_box(0);
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
                    v_reuseFailAlloc_2359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2359_, 0, v_a_2349_);
                    v___x_2354_ = v_reuseFailAlloc_2359_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2348_ == 0 {
                    lean_ctor_set(v___x_2347_, 0, v___x_2354_);
                    v___x_2356_ = v___x_2347_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2358_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 0, v___x_2354_);
                    lean_ctor_set(v_reuseFailAlloc_2358_, 1, v_snd_2345_);
                    v___x_2356_ = v_reuseFailAlloc_2358_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2357_ = lean_apply_2(v_toPure_2342_, lean_box(0), v___x_2356_);
                return v___x_2357_;
            }
            5 => {
                v_a_2367_ = lean_ctor_get(v_fst_2344_, 0);
                v_isSharedCheck_2378_ = (!lean_is_exclusive(v_fst_2344_)) as u8;
                if v_isSharedCheck_2378_ == 0 {
                    v___x_2369_ = v_fst_2344_;
                    v_isShared_2370_ = v_isSharedCheck_2378_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_a_2367_);
                    lean_dec(v_fst_2344_);
                    v___x_2369_ = lean_box(0);
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
                    v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2367_);
                    v___x_2372_ = v_reuseFailAlloc_2377_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2366_ == 0 {
                    lean_ctor_set(v___x_2365_, 0, v___x_2372_);
                    v___x_2374_ = v___x_2365_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2376_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2372_);
                    lean_ctor_set(v_reuseFailAlloc_2376_, 1, v_snd_2363_);
                    v___x_2374_ = v_reuseFailAlloc_2376_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2375_ = lean_apply_2(v_toPure_2342_, lean_box(0), v___x_2374_);
                return v___x_2375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1(
    mut v_toPure_2381_: *mut LeanObject,
    mut v___x_2382_: *mut LeanObject,
    mut v_____x_2383_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2388_: u8 = 0;
    let mut v_a_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2400_: u8 = 0;
    let mut v_isSharedCheck_2401_: u8 = 0;
    let mut v_unused_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2406_: u8 = 0;
    let mut v_fst_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2410_: u8 = 0;
    let mut v_snd_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2428_: u8 = 0;
    let mut v_unused_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2430_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2384_ = lean_ctor_get(v_____x_2383_, 0);
                lean_inc(v_fst_2384_);
                if lean_obj_tag(v_fst_2384_) == 0 {
                    v_snd_2385_ = lean_ctor_get(v_____x_2383_, 1);
                    v_isSharedCheck_2401_ = (!lean_is_exclusive(v_____x_2383_)) as u8;
                    if v_isSharedCheck_2401_ == 0 {
                        v_unused_2402_ = lean_ctor_get(v_____x_2383_, 0);
                        lean_dec(v_unused_2402_);
                        v___x_2387_ = v_____x_2383_;
                        v_isShared_2388_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2385_);
                        lean_dec(v_____x_2383_);
                        v___x_2387_ = lean_box(0);
                        v_isShared_2388_ = v_isSharedCheck_2401_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2403_ = lean_ctor_get(v_fst_2384_, 0);
                    v_isSharedCheck_2430_ = (!lean_is_exclusive(v_fst_2384_)) as u8;
                    if v_isSharedCheck_2430_ == 0 {
                        v___x_2405_ = v_fst_2384_;
                        v_isShared_2406_ = v_isSharedCheck_2430_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2403_);
                        lean_dec(v_fst_2384_);
                        v___x_2405_ = lean_box(0);
                        v_isShared_2406_ = v_isSharedCheck_2430_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2389_ = lean_ctor_get(v_fst_2384_, 0);
                v_isSharedCheck_2400_ = (!lean_is_exclusive(v_fst_2384_)) as u8;
                if v_isSharedCheck_2400_ == 0 {
                    v___x_2391_ = v_fst_2384_;
                    v_isShared_2392_ = v_isSharedCheck_2400_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2389_);
                    lean_dec(v_fst_2384_);
                    v___x_2391_ = lean_box(0);
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
                    v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_a_2389_);
                    v___x_2394_ = v_reuseFailAlloc_2399_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2388_ == 0 {
                    lean_ctor_set(v___x_2387_, 0, v___x_2394_);
                    v___x_2396_ = v___x_2387_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2394_);
                    lean_ctor_set(v_reuseFailAlloc_2398_, 1, v_snd_2385_);
                    v___x_2396_ = v_reuseFailAlloc_2398_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2397_ = lean_apply_2(v_toPure_2381_, lean_box(0), v___x_2396_);
                return v___x_2397_;
            }
            5 => {
                v_fst_2407_ = lean_ctor_get(v_a_2403_, 0);
                v_isSharedCheck_2428_ = (!lean_is_exclusive(v_a_2403_)) as u8;
                if v_isSharedCheck_2428_ == 0 {
                    v_unused_2429_ = lean_ctor_get(v_a_2403_, 1);
                    lean_dec(v_unused_2429_);
                    v___x_2409_ = v_a_2403_;
                    v_isShared_2410_ = v_isSharedCheck_2428_;
                    state = 6;
                    continue;
                } else {
                    lean_inc(v_fst_2407_);
                    lean_dec(v_a_2403_);
                    v___x_2409_ = lean_box(0);
                    v_isShared_2410_ = v_isSharedCheck_2428_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if lean_obj_tag(v_fst_2407_) == 0 {
                    v_snd_2411_ = lean_ctor_get(v_____x_2383_, 1);
                    lean_inc(v_snd_2411_);
                    lean_dec_ref(v_____x_2383_);
                    if v_isShared_2406_ == 0 {
                        lean_ctor_set(v___x_2405_, 0, v___x_2382_);
                        v___x_2413_ = v___x_2405_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2418_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2418_, 0, v___x_2382_);
                        v___x_2413_ = v_reuseFailAlloc_2418_;
                        state = 7;
                        continue;
                    }
                } else {
                    v_snd_2419_ = lean_ctor_get(v_____x_2383_, 1);
                    lean_inc(v_snd_2419_);
                    lean_dec_ref(v_____x_2383_);
                    v_val_2420_ = lean_ctor_get(v_fst_2407_, 0);
                    lean_inc(v_val_2420_);
                    lean_dec_ref_known(v_fst_2407_, 1);
                    if v_isShared_2406_ == 0 {
                        lean_ctor_set(v___x_2405_, 0, v_val_2420_);
                        v___x_2422_ = v___x_2405_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2427_, 0, v_val_2420_);
                        v___x_2422_ = v_reuseFailAlloc_2427_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_2410_ == 0 {
                    lean_ctor_set(v___x_2409_, 1, v_snd_2411_);
                    lean_ctor_set(v___x_2409_, 0, v___x_2413_);
                    v___x_2415_ = v___x_2409_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2417_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 0, v___x_2413_);
                    lean_ctor_set(v_reuseFailAlloc_2417_, 1, v_snd_2411_);
                    v___x_2415_ = v_reuseFailAlloc_2417_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2416_ = lean_apply_2(v_toPure_2381_, lean_box(0), v___x_2415_);
                return v___x_2416_;
            }
            9 => {
                if v_isShared_2410_ == 0 {
                    lean_ctor_set(v___x_2409_, 1, v_snd_2419_);
                    lean_ctor_set(v___x_2409_, 0, v___x_2422_);
                    v___x_2424_ = v___x_2409_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2426_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 0, v___x_2422_);
                    lean_ctor_set(v_reuseFailAlloc_2426_, 1, v_snd_2419_);
                    v___x_2424_ = v_reuseFailAlloc_2426_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2425_ = lean_apply_2(v_toPure_2381_, lean_box(0), v___x_2424_);
                return v___x_2425_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2(
    mut v_toPure_2431_: *mut LeanObject,
    mut v___x_2432_: *mut LeanObject,
    mut v___x_2433_: *mut LeanObject,
    mut v_____x_2434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2439_: u8 = 0;
    let mut v_a_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2443_: u8 = 0;
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2451_: u8 = 0;
    let mut v_isSharedCheck_2452_: u8 = 0;
    let mut v_unused_2453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2457_: u8 = 0;
    let mut v___x_2458_: u8 = 0;
    let mut v_snd_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2462_: u8 = 0;
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2471_: u8 = 0;
    let mut v_unused_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2487_: u8 = 0;
    let mut v_unused_2488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2489_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2435_ = lean_ctor_get(v_____x_2434_, 0);
                lean_inc(v_fst_2435_);
                if lean_obj_tag(v_fst_2435_) == 0 {
                    lean_dec_ref(v___x_2432_);
                    v_snd_2436_ = lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2452_ = (!lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2452_ == 0 {
                        v_unused_2453_ = lean_ctor_get(v_____x_2434_, 0);
                        lean_dec(v_unused_2453_);
                        v___x_2438_ = v_____x_2434_;
                        v_isShared_2439_ = v_isSharedCheck_2452_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2436_);
                        lean_dec(v_____x_2434_);
                        v___x_2438_ = lean_box(0);
                        v_isShared_2439_ = v_isSharedCheck_2452_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2454_ = lean_ctor_get(v_fst_2435_, 0);
                    v_isSharedCheck_2489_ = (!lean_is_exclusive(v_fst_2435_)) as u8;
                    if v_isSharedCheck_2489_ == 0 {
                        v___x_2456_ = v_fst_2435_;
                        v_isShared_2457_ = v_isSharedCheck_2489_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2454_);
                        lean_dec(v_fst_2435_);
                        v___x_2456_ = lean_box(0);
                        v_isShared_2457_ = v_isSharedCheck_2489_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2440_ = lean_ctor_get(v_fst_2435_, 0);
                v_isSharedCheck_2451_ = (!lean_is_exclusive(v_fst_2435_)) as u8;
                if v_isSharedCheck_2451_ == 0 {
                    v___x_2442_ = v_fst_2435_;
                    v_isShared_2443_ = v_isSharedCheck_2451_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2440_);
                    lean_dec(v_fst_2435_);
                    v___x_2442_ = lean_box(0);
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
                    v_reuseFailAlloc_2450_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2450_, 0, v_a_2440_);
                    v___x_2445_ = v_reuseFailAlloc_2450_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2439_ == 0 {
                    lean_ctor_set(v___x_2438_, 0, v___x_2445_);
                    v___x_2447_ = v___x_2438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2449_, 0, v___x_2445_);
                    lean_ctor_set(v_reuseFailAlloc_2449_, 1, v_snd_2436_);
                    v___x_2447_ = v_reuseFailAlloc_2449_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2448_ = lean_apply_2(v_toPure_2431_, lean_box(0), v___x_2447_);
                return v___x_2448_;
            }
            5 => {
                v___x_2458_ = (lean_unbox(v_a_2454_) as u8);
                lean_dec(v_a_2454_);
                if v___x_2458_ == 0 {
                    v_snd_2459_ = lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2471_ = (!lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2471_ == 0 {
                        v_unused_2472_ = lean_ctor_get(v_____x_2434_, 0);
                        lean_dec(v_unused_2472_);
                        v___x_2461_ = v_____x_2434_;
                        v_isShared_2462_ = v_isSharedCheck_2471_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2459_);
                        lean_dec(v_____x_2434_);
                        v___x_2461_ = lean_box(0);
                        v_isShared_2462_ = v_isSharedCheck_2471_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___x_2432_);
                    v_snd_2473_ = lean_ctor_get(v_____x_2434_, 1);
                    v_isSharedCheck_2487_ = (!lean_is_exclusive(v_____x_2434_)) as u8;
                    if v_isSharedCheck_2487_ == 0 {
                        v_unused_2488_ = lean_ctor_get(v_____x_2434_, 0);
                        lean_dec(v_unused_2488_);
                        v___x_2475_ = v_____x_2434_;
                        v_isShared_2476_ = v_isSharedCheck_2487_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_snd_2473_);
                        lean_dec(v_____x_2434_);
                        v___x_2475_ = lean_box(0);
                        v_isShared_2476_ = v_isSharedCheck_2487_;
                        state = 9;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2463_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2463_, 0, v___x_2432_);
                if v_isShared_2457_ == 0 {
                    lean_ctor_set(v___x_2456_, 0, v___x_2463_);
                    v___x_2465_ = v___x_2456_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2470_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2470_, 0, v___x_2463_);
                    v___x_2465_ = v_reuseFailAlloc_2470_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2462_ == 0 {
                    lean_ctor_set(v___x_2461_, 0, v___x_2465_);
                    v___x_2467_ = v___x_2461_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2469_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 0, v___x_2465_);
                    lean_ctor_set(v_reuseFailAlloc_2469_, 1, v_snd_2459_);
                    v___x_2467_ = v_reuseFailAlloc_2469_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2468_ = lean_apply_2(v_toPure_2431_, lean_box(0), v___x_2467_);
                return v___x_2468_;
            }
            9 => {
                v___x_2477_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2477_, 0, v___x_2433_);
                if v_isShared_2476_ == 0 {
                    lean_ctor_set(v___x_2475_, 1, v___x_2433_);
                    lean_ctor_set(v___x_2475_, 0, v___x_2477_);
                    v___x_2479_ = v___x_2475_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2486_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 0, v___x_2477_);
                    lean_ctor_set(v_reuseFailAlloc_2486_, 1, v___x_2433_);
                    v___x_2479_ = v_reuseFailAlloc_2486_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2480_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2480_, 0, v___x_2479_);
                if v_isShared_2457_ == 0 {
                    lean_ctor_set(v___x_2456_, 0, v___x_2480_);
                    v___x_2482_ = v___x_2456_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2485_, 0, v___x_2480_);
                    v___x_2482_ = v_reuseFailAlloc_2485_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                v___x_2483_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2483_, 0, v___x_2482_);
                lean_ctor_set(v___x_2483_, 1, v_snd_2473_);
                v___x_2484_ = lean_apply_2(v_toPure_2431_, lean_box(0), v___x_2483_);
                return v___x_2484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(
    mut v_inst_2490_: *mut LeanObject,
    mut v_toBind_2491_: *mut LeanObject,
    mut v___f_2492_: *mut LeanObject,
    mut v_____r_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut LeanObject = core::ptr::null_mut();
    v___x_2496_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(
        v_inst_2490_,
        v___y_2494_,
        v___y_2495_,
    );
    v___x_2497_ = lean_apply_4(
        v_toBind_2491_,
        lean_box(0),
        lean_box(0),
        v___x_2496_,
        v___f_2492_,
    );
    return v___x_2497_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed(
    mut v_inst_2498_: *mut LeanObject,
    mut v_toBind_2499_: *mut LeanObject,
    mut v___f_2500_: *mut LeanObject,
    mut v_____r_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2504_: *mut LeanObject = core::ptr::null_mut();
    v_res_2504_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3(
            v_inst_2498_,
            v_toBind_2499_,
            v___f_2500_,
            v_____r_2501_,
            v___y_2502_,
            v___y_2503_,
        );
    lean_dec_ref(v___y_2502_);
    return v_res_2504_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(
    mut v_toPure_2505_: *mut LeanObject,
    mut v_next_2506_: *mut LeanObject,
    mut v_G_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v_____x_2509_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2514_: u8 = 0;
    let mut v_a_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2518_: u8 = 0;
    let mut v___x_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_isSharedCheck_2527_: u8 = 0;
    let mut v_unused_2528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2532_: u8 = 0;
    let mut v_snd_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2536_: u8 = 0;
    let mut v_a_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2545_: u8 = 0;
    let mut v_unused_2546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2552_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2510_ = lean_ctor_get(v_____x_2509_, 0);
                lean_inc(v_fst_2510_);
                if lean_obj_tag(v_fst_2510_) == 0 {
                    lean_dec(v_G_2507_);
                    v_snd_2511_ = lean_ctor_get(v_____x_2509_, 1);
                    v_isSharedCheck_2527_ = (!lean_is_exclusive(v_____x_2509_)) as u8;
                    if v_isSharedCheck_2527_ == 0 {
                        v_unused_2528_ = lean_ctor_get(v_____x_2509_, 0);
                        lean_dec(v_unused_2528_);
                        v___x_2513_ = v_____x_2509_;
                        v_isShared_2514_ = v_isSharedCheck_2527_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2511_);
                        lean_dec(v_____x_2509_);
                        v___x_2513_ = lean_box(0);
                        v_isShared_2514_ = v_isSharedCheck_2527_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2529_ = lean_ctor_get(v_fst_2510_, 0);
                    v_isSharedCheck_2552_ = (!lean_is_exclusive(v_fst_2510_)) as u8;
                    if v_isSharedCheck_2552_ == 0 {
                        v___x_2531_ = v_fst_2510_;
                        v_isShared_2532_ = v_isSharedCheck_2552_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2529_);
                        lean_dec(v_fst_2510_);
                        v___x_2531_ = lean_box(0);
                        v_isShared_2532_ = v_isSharedCheck_2552_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2515_ = lean_ctor_get(v_fst_2510_, 0);
                v_isSharedCheck_2526_ = (!lean_is_exclusive(v_fst_2510_)) as u8;
                if v_isSharedCheck_2526_ == 0 {
                    v___x_2517_ = v_fst_2510_;
                    v_isShared_2518_ = v_isSharedCheck_2526_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2515_);
                    lean_dec(v_fst_2510_);
                    v___x_2517_ = lean_box(0);
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
                    v_reuseFailAlloc_2525_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2525_, 0, v_a_2515_);
                    v___x_2520_ = v_reuseFailAlloc_2525_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2514_ == 0 {
                    lean_ctor_set(v___x_2513_, 0, v___x_2520_);
                    v___x_2522_ = v___x_2513_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2524_, 0, v___x_2520_);
                    lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_snd_2511_);
                    v___x_2522_ = v_reuseFailAlloc_2524_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2523_ = lean_apply_2(v_toPure_2505_, lean_box(0), v___x_2522_);
                return v___x_2523_;
            }
            5 => {
                if lean_obj_tag(v_a_2529_) == 0 {
                    lean_dec(v_G_2507_);
                    v_snd_2533_ = lean_ctor_get(v_____x_2509_, 1);
                    v_isSharedCheck_2545_ = (!lean_is_exclusive(v_____x_2509_)) as u8;
                    if v_isSharedCheck_2545_ == 0 {
                        v_unused_2546_ = lean_ctor_get(v_____x_2509_, 0);
                        lean_dec(v_unused_2546_);
                        v___x_2535_ = v_____x_2509_;
                        v_isShared_2536_ = v_isSharedCheck_2545_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2533_);
                        lean_dec(v_____x_2509_);
                        v___x_2535_ = lean_box(0);
                        v_isShared_2536_ = v_isSharedCheck_2545_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2531_);
                    lean_dec(v_toPure_2505_);
                    v_snd_2547_ = lean_ctor_get(v_____x_2509_, 1);
                    lean_inc(v_snd_2547_);
                    lean_dec_ref(v_____x_2509_);
                    v_a_2548_ = lean_ctor_get(v_a_2529_, 0);
                    lean_inc(v_a_2548_);
                    lean_dec_ref_known(v_a_2529_, 1);
                    v___x_2549_ = lean_unsigned_to_nat(1);
                    v___x_2550_ = lean_nat_add(v_next_2506_, v___x_2549_);
                    lean_inc_ref(v___y_2508_);
                    v___x_2551_ = lean_apply_6(
                        v_G_2507_,
                        v___x_2550_,
                        v_a_2548_,
                        lean_box(0),
                        lean_box(0),
                        v___y_2508_,
                        v_snd_2547_,
                    );
                    return v___x_2551_;
                }
            }
            6 => {
                v_a_2537_ = lean_ctor_get(v_a_2529_, 0);
                lean_inc(v_a_2537_);
                lean_dec_ref_known(v_a_2529_, 1);
                if v_isShared_2532_ == 0 {
                    lean_ctor_set(v___x_2531_, 0, v_a_2537_);
                    v___x_2539_ = v___x_2531_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2544_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2544_, 0, v_a_2537_);
                    v___x_2539_ = v_reuseFailAlloc_2544_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2536_ == 0 {
                    lean_ctor_set(v___x_2535_, 0, v___x_2539_);
                    v___x_2541_ = v___x_2535_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2543_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 0, v___x_2539_);
                    lean_ctor_set(v_reuseFailAlloc_2543_, 1, v_snd_2533_);
                    v___x_2541_ = v_reuseFailAlloc_2543_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2542_ = lean_apply_2(v_toPure_2505_, lean_box(0), v___x_2541_);
                return v___x_2542_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed(
    mut v_toPure_2553_: *mut LeanObject,
    mut v_next_2554_: *mut LeanObject,
    mut v_G_2555_: *mut LeanObject,
    mut v___y_2556_: *mut LeanObject,
    mut v_____x_2557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2558_: *mut LeanObject = core::ptr::null_mut();
    v_res_2558_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4(
            v_toPure_2553_,
            v_next_2554_,
            v_G_2555_,
            v___y_2556_,
            v_____x_2557_,
        );
    lean_dec_ref(v___y_2556_);
    lean_dec(v_next_2554_);
    return v_res_2558_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(
    mut v_toPure_2559_: *mut LeanObject,
    mut v___f_2560_: *mut LeanObject,
    mut v___y_2561_: *mut LeanObject,
    mut v_____x_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2567_: u8 = 0;
    let mut v_a_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2571_: u8 = 0;
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2579_: u8 = 0;
    let mut v_isSharedCheck_2580_: u8 = 0;
    let mut v_unused_2581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2563_ = lean_ctor_get(v_____x_2562_, 0);
                lean_inc(v_fst_2563_);
                if lean_obj_tag(v_fst_2563_) == 0 {
                    lean_dec(v___f_2560_);
                    v_snd_2564_ = lean_ctor_get(v_____x_2562_, 1);
                    v_isSharedCheck_2580_ = (!lean_is_exclusive(v_____x_2562_)) as u8;
                    if v_isSharedCheck_2580_ == 0 {
                        v_unused_2581_ = lean_ctor_get(v_____x_2562_, 0);
                        lean_dec(v_unused_2581_);
                        v___x_2566_ = v_____x_2562_;
                        v_isShared_2567_ = v_isSharedCheck_2580_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2564_);
                        lean_dec(v_____x_2562_);
                        v___x_2566_ = lean_box(0);
                        v_isShared_2567_ = v_isSharedCheck_2580_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_toPure_2559_);
                    v_snd_2582_ = lean_ctor_get(v_____x_2562_, 1);
                    lean_inc(v_snd_2582_);
                    lean_dec_ref(v_____x_2562_);
                    v_a_2583_ = lean_ctor_get(v_fst_2563_, 0);
                    lean_inc(v_a_2583_);
                    lean_dec_ref_known(v_fst_2563_, 1);
                    lean_inc_ref(v___y_2561_);
                    v___x_2584_ = lean_apply_3(v___f_2560_, v_a_2583_, v___y_2561_, v_snd_2582_);
                    return v___x_2584_;
                }
            }
            1 => {
                v_a_2568_ = lean_ctor_get(v_fst_2563_, 0);
                v_isSharedCheck_2579_ = (!lean_is_exclusive(v_fst_2563_)) as u8;
                if v_isSharedCheck_2579_ == 0 {
                    v___x_2570_ = v_fst_2563_;
                    v_isShared_2571_ = v_isSharedCheck_2579_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2568_);
                    lean_dec(v_fst_2563_);
                    v___x_2570_ = lean_box(0);
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
                    v_reuseFailAlloc_2578_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2578_, 0, v_a_2568_);
                    v___x_2573_ = v_reuseFailAlloc_2578_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2567_ == 0 {
                    lean_ctor_set(v___x_2566_, 0, v___x_2573_);
                    v___x_2575_ = v___x_2566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 0, v___x_2573_);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 1, v_snd_2564_);
                    v___x_2575_ = v_reuseFailAlloc_2577_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2576_ = lean_apply_2(v_toPure_2559_, lean_box(0), v___x_2575_);
                return v___x_2576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed(
    mut v_toPure_2585_: *mut LeanObject,
    mut v___f_2586_: *mut LeanObject,
    mut v___y_2587_: *mut LeanObject,
    mut v_____x_2588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2589_: *mut LeanObject = core::ptr::null_mut();
    v_res_2589_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5(
            v_toPure_2585_,
            v___f_2586_,
            v___y_2587_,
            v_____x_2588_,
        );
    lean_dec_ref(v___y_2587_);
    return v_res_2589_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6(
    mut v___x_2590_: *mut LeanObject,
    mut v_toPure_2591_: *mut LeanObject,
    mut v_toBind_2592_: *mut LeanObject,
    mut v___f_2593_: *mut LeanObject,
    mut v_initialMask_2594_: *mut LeanObject,
    mut v___f_2595_: *mut LeanObject,
    mut v_inst_2596_: *mut LeanObject,
    mut v___x_2597_: *mut LeanObject,
    mut v_next_2598_: *mut LeanObject,
    mut v_acc_2599_: *mut LeanObject,
    mut v_h_2600_: *mut LeanObject,
    mut v_G_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2604_: u8 = 0;
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: u8 = 0;
    let mut v___f_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2604_ = lean_nat_dec_lt(v_next_2598_, v___x_2590_);
                if v___x_2604_ == 0 {
                    lean_dec(v_G_2601_);
                    lean_dec(v_next_2598_);
                    lean_dec_ref(v_inst_2596_);
                    lean_dec(v___f_2595_);
                    lean_dec(v___f_2593_);
                    lean_dec(v_toBind_2592_);
                    v___x_2605_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2605_, 0, v_acc_2599_);
                    v___x_2606_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2606_, 0, v___x_2605_);
                    lean_ctor_set(v___x_2606_, 1, v___y_2603_);
                    v___x_2607_ = lean_apply_2(v_toPure_2591_, lean_box(0), v___x_2606_);
                    return v___x_2607_;
                } else {
                    lean_dec_ref(v_acc_2599_);
                    lean_inc_ref(v___y_2602_);
                    lean_inc(v_next_2598_);
                    lean_inc(v_toPure_2591_);
                    v___f_2608_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__4___boxed as *mut core::ffi::c_void, 5, 4);
                    lean_closure_set(v___f_2608_, 0, v_toPure_2591_);
                    lean_closure_set(v___f_2608_, 1, v_next_2598_);
                    lean_closure_set(v___f_2608_, 2, v_G_2601_);
                    lean_closure_set(v___f_2608_, 3, v___y_2602_);
                    v___x_2613_ = lean_array_fget_borrowed(v_initialMask_2594_, v_next_2598_);
                    v___x_2614_ = (lean_unbox(v___x_2613_) as u8);
                    if v___x_2614_ == 0 {
                        lean_inc_ref(v___y_2602_);
                        v___f_2615_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__5___boxed as *mut core::ffi::c_void, 4, 3);
                        lean_closure_set(v___f_2615_, 0, v_toPure_2591_);
                        lean_closure_set(v___f_2615_, 1, v___f_2595_);
                        lean_closure_set(v___f_2615_, 2, v___y_2602_);
                        v___x_2616_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_add___redArg(v_next_2598_, v_inst_2596_, v___y_2603_);
                        lean_inc(v_toBind_2592_);
                        v___x_2617_ = lean_apply_4(
                            v_toBind_2592_,
                            lean_box(0),
                            lean_box(0),
                            v___x_2616_,
                            v___f_2615_,
                        );
                        v___y_2610_ = v___x_2617_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_next_2598_);
                        lean_dec_ref(v_inst_2596_);
                        lean_dec(v_toPure_2591_);
                        lean_inc_ref(v___y_2602_);
                        v___x_2618_ =
                            lean_apply_3(v___f_2595_, v___x_2597_, v___y_2602_, v___y_2603_);
                        v___y_2610_ = v___x_2618_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_toBind_2592_);
                v___x_2611_ = lean_apply_4(
                    v_toBind_2592_,
                    lean_box(0),
                    lean_box(0),
                    v___y_2610_,
                    v___f_2593_,
                );
                v___x_2612_ = lean_apply_4(
                    v_toBind_2592_,
                    lean_box(0),
                    lean_box(0),
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
    mut v___x_2619_: *mut LeanObject,
    mut v_toPure_2620_: *mut LeanObject,
    mut v_toBind_2621_: *mut LeanObject,
    mut v___f_2622_: *mut LeanObject,
    mut v_initialMask_2623_: *mut LeanObject,
    mut v___f_2624_: *mut LeanObject,
    mut v_inst_2625_: *mut LeanObject,
    mut v___x_2626_: *mut LeanObject,
    mut v_next_2627_: *mut LeanObject,
    mut v_acc_2628_: *mut LeanObject,
    mut v_h_2629_: *mut LeanObject,
    mut v_G_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2633_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_2631_);
    lean_dec_ref(v_initialMask_2623_);
    lean_dec(v___x_2619_);
    return v_res_2633_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(
    mut v_toPure_2637_: *mut LeanObject,
    mut v_inst_2638_: *mut LeanObject,
    mut v_toBind_2639_: *mut LeanObject,
    mut v___f_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_____x_2642_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2647_: u8 = 0;
    let mut v_a_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2651_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2659_: u8 = 0;
    let mut v_isSharedCheck_2660_: u8 = 0;
    let mut v_unused_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initialMask_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6334__overap_2673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2643_ = lean_ctor_get(v_____x_2642_, 0);
                lean_inc(v_fst_2643_);
                if lean_obj_tag(v_fst_2643_) == 0 {
                    lean_dec(v___f_2640_);
                    lean_dec(v_toBind_2639_);
                    lean_dec_ref(v_inst_2638_);
                    v_snd_2644_ = lean_ctor_get(v_____x_2642_, 1);
                    v_isSharedCheck_2660_ = (!lean_is_exclusive(v_____x_2642_)) as u8;
                    if v_isSharedCheck_2660_ == 0 {
                        v_unused_2661_ = lean_ctor_get(v_____x_2642_, 0);
                        lean_dec(v_unused_2661_);
                        v___x_2646_ = v_____x_2642_;
                        v_isShared_2647_ = v_isSharedCheck_2660_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2644_);
                        lean_dec(v_____x_2642_);
                        v___x_2646_ = lean_box(0);
                        v_isShared_2647_ = v_isSharedCheck_2660_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2662_ = lean_ctor_get(v_fst_2643_, 0);
                    lean_inc(v_a_2662_);
                    lean_dec_ref_known(v_fst_2643_, 1);
                    v_snd_2663_ = lean_ctor_get(v_____x_2642_, 1);
                    lean_inc(v_snd_2663_);
                    lean_dec_ref(v_____x_2642_);
                    v_initialMask_2664_ = lean_ctor_get(v_a_2662_, 0);
                    lean_inc_ref(v_initialMask_2664_);
                    lean_dec(v_a_2662_);
                    v___x_2665_ = lean_array_get_size(v_initialMask_2664_);
                    v___x_2666_ = lean_unsigned_to_nat(0);
                    v___x_2667_ = lean_box(0);
                    lean_inc_n(v_toPure_2637_, 2);
                    v___f_2668_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
                    lean_closure_set(v___f_2668_, 0, v_toPure_2637_);
                    lean_closure_set(v___f_2668_, 1, v___x_2667_);
                    v___x_2669_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___closed__0;
                    v___f_2670_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__2 as *mut core::ffi::c_void, 4, 3);
                    lean_closure_set(v___f_2670_, 0, v_toPure_2637_);
                    lean_closure_set(v___f_2670_, 1, v___x_2669_);
                    lean_closure_set(v___f_2670_, 2, v___x_2667_);
                    lean_inc_n(v_toBind_2639_, 2);
                    lean_inc_ref(v_inst_2638_);
                    v___f_2671_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__3___boxed as *mut core::ffi::c_void, 6, 3);
                    lean_closure_set(v___f_2671_, 0, v_inst_2638_);
                    lean_closure_set(v___f_2671_, 1, v_toBind_2639_);
                    lean_closure_set(v___f_2671_, 2, v___f_2670_);
                    v___f_2672_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__6___boxed as *mut core::ffi::c_void, 14, 8);
                    lean_closure_set(v___f_2672_, 0, v___x_2665_);
                    lean_closure_set(v___f_2672_, 1, v_toPure_2637_);
                    lean_closure_set(v___f_2672_, 2, v_toBind_2639_);
                    lean_closure_set(v___f_2672_, 3, v___f_2640_);
                    lean_closure_set(v___f_2672_, 4, v_initialMask_2664_);
                    lean_closure_set(v___f_2672_, 5, v___f_2671_);
                    lean_closure_set(v___f_2672_, 6, v_inst_2638_);
                    lean_closure_set(v___f_2672_, 7, v___x_2667_);
                    v___x_6334__overap_2673_ = l_WellFounded_opaqueFix_u2083___redArg(
                        v___f_2672_,
                        v___x_2666_,
                        v___x_2669_,
                        lean_box(0),
                    );
                    lean_inc_ref(v_a_2641_);
                    v___x_2674_ = lean_apply_2(v___x_6334__overap_2673_, v_a_2641_, v_snd_2663_);
                    v___x_2675_ = lean_apply_4(
                        v_toBind_2639_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2674_,
                        v___f_2668_,
                    );
                    return v___x_2675_;
                }
            }
            1 => {
                v_a_2648_ = lean_ctor_get(v_fst_2643_, 0);
                v_isSharedCheck_2659_ = (!lean_is_exclusive(v_fst_2643_)) as u8;
                if v_isSharedCheck_2659_ == 0 {
                    v___x_2650_ = v_fst_2643_;
                    v_isShared_2651_ = v_isSharedCheck_2659_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2648_);
                    lean_dec(v_fst_2643_);
                    v___x_2650_ = lean_box(0);
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
                    v_reuseFailAlloc_2658_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2658_, 0, v_a_2648_);
                    v___x_2653_ = v_reuseFailAlloc_2658_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2647_ == 0 {
                    lean_ctor_set(v___x_2646_, 0, v___x_2653_);
                    v___x_2655_ = v___x_2646_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2653_);
                    lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_snd_2644_);
                    v___x_2655_ = v_reuseFailAlloc_2657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2656_ = lean_apply_2(v_toPure_2637_, lean_box(0), v___x_2655_);
                return v___x_2656_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed(
    mut v_toPure_2676_: *mut LeanObject,
    mut v_inst_2677_: *mut LeanObject,
    mut v_toBind_2678_: *mut LeanObject,
    mut v___f_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_____x_2681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2682_: *mut LeanObject = core::ptr::null_mut();
    v_res_2682_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7(
            v_toPure_2676_,
            v_inst_2677_,
            v_toBind_2678_,
            v___f_2679_,
            v_a_2680_,
            v_____x_2681_,
        );
    lean_dec_ref(v_a_2680_);
    return v_res_2682_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
    mut v_inst_2683_: *mut LeanObject,
    mut v_a_2684_: *mut LeanObject,
    mut v_a_2685_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_2686_ = lean_ctor_get(v_inst_2683_, 0);
    v_toBind_2687_ = lean_ctor_get(v_inst_2683_, 1);
    lean_inc_n(v_toBind_2687_, 2);
    v_toPure_2688_ = lean_ctor_get(v_toApplicative_2686_, 1);
    lean_inc_n(v_toPure_2688_, 3);
    v___f_2689_ = lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_2689_, 0, v_toPure_2688_);
    lean_inc_ref_n(v_a_2684_, 2);
    v___f_2690_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___lam__7___boxed as *mut core::ffi::c_void, 6, 5);
    lean_closure_set(v___f_2690_, 0, v_toPure_2688_);
    lean_closure_set(v___f_2690_, 1, v_inst_2683_);
    lean_closure_set(v___f_2690_, 2, v_toBind_2687_);
    lean_closure_set(v___f_2690_, 3, v___f_2689_);
    lean_closure_set(v___f_2690_, 4, v_a_2684_);
    v___x_2691_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_2691_, 0, v_a_2684_);
    v___x_2692_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2692_, 0, v___x_2691_);
    lean_ctor_set(v___x_2692_, 1, v_a_2685_);
    v___x_2693_ = lean_apply_2(v_toPure_2688_, lean_box(0), v___x_2692_);
    v___x_2694_ = lean_apply_4(
        v_toBind_2687_,
        lean_box(0),
        lean_box(0),
        v___x_2693_,
        v___f_2690_,
    );
    return v___x_2694_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg___boxed(
    mut v_inst_2695_: *mut LeanObject,
    mut v_a_2696_: *mut LeanObject,
    mut v_a_2697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2698_: *mut LeanObject = core::ptr::null_mut();
    v_res_2698_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_2695_,
        v_a_2696_,
        v_a_2697_,
    );
    lean_dec_ref(v_a_2696_);
    return v_res_2698_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(
    mut v_m_2699_: *mut LeanObject,
    mut v_inst_2700_: *mut LeanObject,
    mut v_a_2701_: *mut LeanObject,
    mut v_a_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    v___x_2703_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_2700_,
        v_a_2701_,
        v_a_2702_,
    );
    return v___x_2703_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___boxed(
    mut v_m_2704_: *mut LeanObject,
    mut v_inst_2705_: *mut LeanObject,
    mut v_a_2706_: *mut LeanObject,
    mut v_a_2707_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2708_: *mut LeanObject = core::ptr::null_mut();
    v_res_2708_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init(
        v_m_2704_,
        v_inst_2705_,
        v_a_2706_,
        v_a_2707_,
    );
    lean_dec_ref(v_a_2706_);
    return v_res_2708_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0(
    mut v_toPure_2711_: *mut LeanObject,
    mut v_____x_2712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2717_: u8 = 0;
    let mut v_a_2718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2721_: u8 = 0;
    let mut v___x_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2729_: u8 = 0;
    let mut v_isSharedCheck_2730_: u8 = 0;
    let mut v_unused_2731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2735_: u8 = 0;
    let mut v___x_2736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut v_unused_2742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2713_ = lean_ctor_get(v_____x_2712_, 0);
                lean_inc(v_fst_2713_);
                if lean_obj_tag(v_fst_2713_) == 0 {
                    v_snd_2714_ = lean_ctor_get(v_____x_2712_, 1);
                    v_isSharedCheck_2730_ = (!lean_is_exclusive(v_____x_2712_)) as u8;
                    if v_isSharedCheck_2730_ == 0 {
                        v_unused_2731_ = lean_ctor_get(v_____x_2712_, 0);
                        lean_dec(v_unused_2731_);
                        v___x_2716_ = v_____x_2712_;
                        v_isShared_2717_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2714_);
                        lean_dec(v_____x_2712_);
                        v___x_2716_ = lean_box(0);
                        v_isShared_2717_ = v_isSharedCheck_2730_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_fst_2713_, 1);
                    v_snd_2732_ = lean_ctor_get(v_____x_2712_, 1);
                    v_isSharedCheck_2741_ = (!lean_is_exclusive(v_____x_2712_)) as u8;
                    if v_isSharedCheck_2741_ == 0 {
                        v_unused_2742_ = lean_ctor_get(v_____x_2712_, 0);
                        lean_dec(v_unused_2742_);
                        v___x_2734_ = v_____x_2712_;
                        v_isShared_2735_ = v_isSharedCheck_2741_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2732_);
                        lean_dec(v_____x_2712_);
                        v___x_2734_ = lean_box(0);
                        v_isShared_2735_ = v_isSharedCheck_2741_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2718_ = lean_ctor_get(v_fst_2713_, 0);
                v_isSharedCheck_2729_ = (!lean_is_exclusive(v_fst_2713_)) as u8;
                if v_isSharedCheck_2729_ == 0 {
                    v___x_2720_ = v_fst_2713_;
                    v_isShared_2721_ = v_isSharedCheck_2729_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2718_);
                    lean_dec(v_fst_2713_);
                    v___x_2720_ = lean_box(0);
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
                    v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2728_, 0, v_a_2718_);
                    v___x_2723_ = v_reuseFailAlloc_2728_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2717_ == 0 {
                    lean_ctor_set(v___x_2716_, 0, v___x_2723_);
                    v___x_2725_ = v___x_2716_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2727_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 0, v___x_2723_);
                    lean_ctor_set(v_reuseFailAlloc_2727_, 1, v_snd_2714_);
                    v___x_2725_ = v_reuseFailAlloc_2727_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2726_ = lean_apply_2(v_toPure_2711_, lean_box(0), v___x_2725_);
                return v___x_2726_;
            }
            5 => {
                v___x_2736_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0;
                if v_isShared_2735_ == 0 {
                    lean_ctor_set(v___x_2734_, 0, v___x_2736_);
                    v___x_2738_ = v___x_2734_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2736_);
                    lean_ctor_set(v_reuseFailAlloc_2740_, 1, v_snd_2732_);
                    v___x_2738_ = v_reuseFailAlloc_2740_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2739_ = lean_apply_2(v_toPure_2711_, lean_box(0), v___x_2738_);
                return v___x_2739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1(
    mut v_toPure_2743_: *mut LeanObject,
    mut v_____x_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2749_: u8 = 0;
    let mut v_a_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2753_: u8 = 0;
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2761_: u8 = 0;
    let mut v_isSharedCheck_2762_: u8 = 0;
    let mut v_unused_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2767_: u8 = 0;
    let mut v_snd_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v_a_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2775_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2786_: u8 = 0;
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2792_: u8 = 0;
    let mut v_a_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2807_: u8 = 0;
    let mut v_isSharedCheck_2808_: u8 = 0;
    let mut v_unused_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2745_ = lean_ctor_get(v_____x_2744_, 0);
                lean_inc(v_fst_2745_);
                if lean_obj_tag(v_fst_2745_) == 0 {
                    v_snd_2746_ = lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2762_ = (!lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2762_ == 0 {
                        v_unused_2763_ = lean_ctor_get(v_____x_2744_, 0);
                        lean_dec(v_unused_2763_);
                        v___x_2748_ = v_____x_2744_;
                        v_isShared_2749_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2746_);
                        lean_dec(v_____x_2744_);
                        v___x_2748_ = lean_box(0);
                        v_isShared_2749_ = v_isSharedCheck_2762_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2764_ = lean_ctor_get(v_fst_2745_, 0);
                    v_isSharedCheck_2810_ = (!lean_is_exclusive(v_fst_2745_)) as u8;
                    if v_isSharedCheck_2810_ == 0 {
                        v___x_2766_ = v_fst_2745_;
                        v_isShared_2767_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2764_);
                        lean_dec(v_fst_2745_);
                        v___x_2766_ = lean_box(0);
                        v_isShared_2767_ = v_isSharedCheck_2810_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2750_ = lean_ctor_get(v_fst_2745_, 0);
                v_isSharedCheck_2761_ = (!lean_is_exclusive(v_fst_2745_)) as u8;
                if v_isSharedCheck_2761_ == 0 {
                    v___x_2752_ = v_fst_2745_;
                    v_isShared_2753_ = v_isSharedCheck_2761_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2750_);
                    lean_dec(v_fst_2745_);
                    v___x_2752_ = lean_box(0);
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
                    v_reuseFailAlloc_2760_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2760_, 0, v_a_2750_);
                    v___x_2755_ = v_reuseFailAlloc_2760_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2749_ == 0 {
                    lean_ctor_set(v___x_2748_, 0, v___x_2755_);
                    v___x_2757_ = v___x_2748_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2759_, 0, v___x_2755_);
                    lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_snd_2746_);
                    v___x_2757_ = v_reuseFailAlloc_2759_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2758_ = lean_apply_2(v_toPure_2743_, lean_box(0), v___x_2757_);
                return v___x_2758_;
            }
            5 => {
                if lean_obj_tag(v_a_2764_) == 0 {
                    v_snd_2768_ = lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2787_ = (!lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2787_ == 0 {
                        v_unused_2788_ = lean_ctor_get(v_____x_2744_, 0);
                        lean_dec(v_unused_2788_);
                        v___x_2770_ = v_____x_2744_;
                        v_isShared_2771_ = v_isSharedCheck_2787_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2768_);
                        lean_dec(v_____x_2744_);
                        v___x_2770_ = lean_box(0);
                        v_isShared_2771_ = v_isSharedCheck_2787_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_snd_2789_ = lean_ctor_get(v_____x_2744_, 1);
                    v_isSharedCheck_2808_ = (!lean_is_exclusive(v_____x_2744_)) as u8;
                    if v_isSharedCheck_2808_ == 0 {
                        v_unused_2809_ = lean_ctor_get(v_____x_2744_, 0);
                        lean_dec(v_unused_2809_);
                        v___x_2791_ = v_____x_2744_;
                        v_isShared_2792_ = v_isSharedCheck_2808_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_snd_2789_);
                        lean_dec(v_____x_2744_);
                        v___x_2791_ = lean_box(0);
                        v_isShared_2792_ = v_isSharedCheck_2808_;
                        state = 11;
                        continue;
                    }
                }
            }
            6 => {
                v_a_2772_ = lean_ctor_get(v_a_2764_, 0);
                v_isSharedCheck_2786_ = (!lean_is_exclusive(v_a_2764_)) as u8;
                if v_isSharedCheck_2786_ == 0 {
                    v___x_2774_ = v_a_2764_;
                    v_isShared_2775_ = v_isSharedCheck_2786_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_a_2772_);
                    lean_dec(v_a_2764_);
                    v___x_2774_ = lean_box(0);
                    v_isShared_2775_ = v_isSharedCheck_2786_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2775_ == 0 {
                    lean_ctor_set_tag(v___x_2774_, 1);
                    v___x_2777_ = v___x_2774_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_a_2772_);
                    v___x_2777_ = v_reuseFailAlloc_2785_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_2767_ == 0 {
                    lean_ctor_set(v___x_2766_, 0, v___x_2777_);
                    v___x_2779_ = v___x_2766_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2784_, 0, v___x_2777_);
                    v___x_2779_ = v_reuseFailAlloc_2784_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_2771_ == 0 {
                    lean_ctor_set(v___x_2770_, 0, v___x_2779_);
                    v___x_2781_ = v___x_2770_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2783_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 0, v___x_2779_);
                    lean_ctor_set(v_reuseFailAlloc_2783_, 1, v_snd_2768_);
                    v___x_2781_ = v_reuseFailAlloc_2783_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_2782_ = lean_apply_2(v_toPure_2743_, lean_box(0), v___x_2781_);
                return v___x_2782_;
            }
            11 => {
                v_a_2793_ = lean_ctor_get(v_a_2764_, 0);
                v_isSharedCheck_2807_ = (!lean_is_exclusive(v_a_2764_)) as u8;
                if v_isSharedCheck_2807_ == 0 {
                    v___x_2795_ = v_a_2764_;
                    v_isShared_2796_ = v_isSharedCheck_2807_;
                    state = 12;
                    continue;
                } else {
                    lean_inc(v_a_2793_);
                    lean_dec(v_a_2764_);
                    v___x_2795_ = lean_box(0);
                    v_isShared_2796_ = v_isSharedCheck_2807_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_2796_ == 0 {
                    lean_ctor_set_tag(v___x_2795_, 0);
                    v___x_2798_ = v___x_2795_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_a_2793_);
                    v___x_2798_ = v_reuseFailAlloc_2806_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_2767_ == 0 {
                    lean_ctor_set(v___x_2766_, 0, v___x_2798_);
                    v___x_2800_ = v___x_2766_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v___x_2798_);
                    v___x_2800_ = v_reuseFailAlloc_2805_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2792_ == 0 {
                    lean_ctor_set(v___x_2791_, 0, v___x_2800_);
                    v___x_2802_ = v___x_2791_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 0, v___x_2800_);
                    lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_snd_2789_);
                    v___x_2802_ = v_reuseFailAlloc_2804_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_2803_ = lean_apply_2(v_toPure_2743_, lean_box(0), v___x_2802_);
                return v___x_2803_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2(
    mut v_toPure_2811_: *mut LeanObject,
    mut v___x_2812_: *mut LeanObject,
    mut v_____x_2813_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2818_: u8 = 0;
    let mut v_a_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2822_: u8 = 0;
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2830_: u8 = 0;
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v_unused_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2836_: u8 = 0;
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2848_: u8 = 0;
    let mut v_unused_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2850_: u8 = 0;
    let mut v_unused_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2814_ = lean_ctor_get(v_____x_2813_, 0);
                lean_inc(v_fst_2814_);
                if lean_obj_tag(v_fst_2814_) == 0 {
                    lean_dec(v___x_2812_);
                    v_snd_2815_ = lean_ctor_get(v_____x_2813_, 1);
                    v_isSharedCheck_2831_ = (!lean_is_exclusive(v_____x_2813_)) as u8;
                    if v_isSharedCheck_2831_ == 0 {
                        v_unused_2832_ = lean_ctor_get(v_____x_2813_, 0);
                        lean_dec(v_unused_2832_);
                        v___x_2817_ = v_____x_2813_;
                        v_isShared_2818_ = v_isSharedCheck_2831_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2815_);
                        lean_dec(v_____x_2813_);
                        v___x_2817_ = lean_box(0);
                        v_isShared_2818_ = v_isSharedCheck_2831_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_snd_2833_ = lean_ctor_get(v_____x_2813_, 1);
                    v_isSharedCheck_2850_ = (!lean_is_exclusive(v_____x_2813_)) as u8;
                    if v_isSharedCheck_2850_ == 0 {
                        v_unused_2851_ = lean_ctor_get(v_____x_2813_, 0);
                        lean_dec(v_unused_2851_);
                        v___x_2835_ = v_____x_2813_;
                        v_isShared_2836_ = v_isSharedCheck_2850_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_snd_2833_);
                        lean_dec(v_____x_2813_);
                        v___x_2835_ = lean_box(0);
                        v_isShared_2836_ = v_isSharedCheck_2850_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2819_ = lean_ctor_get(v_fst_2814_, 0);
                v_isSharedCheck_2830_ = (!lean_is_exclusive(v_fst_2814_)) as u8;
                if v_isSharedCheck_2830_ == 0 {
                    v___x_2821_ = v_fst_2814_;
                    v_isShared_2822_ = v_isSharedCheck_2830_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2819_);
                    lean_dec(v_fst_2814_);
                    v___x_2821_ = lean_box(0);
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
                    v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_a_2819_);
                    v___x_2824_ = v_reuseFailAlloc_2829_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2818_ == 0 {
                    lean_ctor_set(v___x_2817_, 0, v___x_2824_);
                    v___x_2826_ = v___x_2817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2824_);
                    lean_ctor_set(v_reuseFailAlloc_2828_, 1, v_snd_2815_);
                    v___x_2826_ = v_reuseFailAlloc_2828_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2827_ = lean_apply_2(v_toPure_2811_, lean_box(0), v___x_2826_);
                return v___x_2827_;
            }
            5 => {
                v_isSharedCheck_2848_ = (!lean_is_exclusive(v_fst_2814_)) as u8;
                if v_isSharedCheck_2848_ == 0 {
                    v_unused_2849_ = lean_ctor_get(v_fst_2814_, 0);
                    lean_dec(v_unused_2849_);
                    v___x_2838_ = v_fst_2814_;
                    v_isShared_2839_ = v_isSharedCheck_2848_;
                    state = 6;
                    continue;
                } else {
                    lean_dec(v_fst_2814_);
                    v___x_2838_ = lean_box(0);
                    v_isShared_2839_ = v_isSharedCheck_2848_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_2840_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2840_, 0, v___x_2812_);
                if v_isShared_2839_ == 0 {
                    lean_ctor_set(v___x_2838_, 0, v___x_2840_);
                    v___x_2842_ = v___x_2838_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2840_);
                    v___x_2842_ = v_reuseFailAlloc_2847_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2836_ == 0 {
                    lean_ctor_set(v___x_2835_, 0, v___x_2842_);
                    v___x_2844_ = v___x_2835_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2842_);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 1, v_snd_2833_);
                    v___x_2844_ = v_reuseFailAlloc_2846_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2845_ = lean_apply_2(v_toPure_2811_, lean_box(0), v___x_2844_);
                return v___x_2845_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3(
    mut v_toPure_2852_: *mut LeanObject,
    mut v___x_2853_: *mut LeanObject,
    mut v_inst_2854_: *mut LeanObject,
    mut v_toBind_2855_: *mut LeanObject,
    mut v___f_2856_: *mut LeanObject,
    mut v___x_2857_: *mut LeanObject,
    mut v_____x_2858_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2863_: u8 = 0;
    let mut v_a_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2867_: u8 = 0;
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2875_: u8 = 0;
    let mut v_isSharedCheck_2876_: u8 = 0;
    let mut v_unused_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2882_: u8 = 0;
    let mut v_snd_2883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2898_: u8 = 0;
    let mut v_unused_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2859_ = lean_ctor_get(v_____x_2858_, 0);
                lean_inc(v_fst_2859_);
                if lean_obj_tag(v_fst_2859_) == 0 {
                    lean_dec(v___x_2857_);
                    lean_dec(v___f_2856_);
                    lean_dec(v_toBind_2855_);
                    lean_dec_ref(v_inst_2854_);
                    v_snd_2860_ = lean_ctor_get(v_____x_2858_, 1);
                    v_isSharedCheck_2876_ = (!lean_is_exclusive(v_____x_2858_)) as u8;
                    if v_isSharedCheck_2876_ == 0 {
                        v_unused_2877_ = lean_ctor_get(v_____x_2858_, 0);
                        lean_dec(v_unused_2877_);
                        v___x_2862_ = v_____x_2858_;
                        v_isShared_2863_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2860_);
                        lean_dec(v_____x_2858_);
                        v___x_2862_ = lean_box(0);
                        v_isShared_2863_ = v_isSharedCheck_2876_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2878_ = lean_ctor_get(v_fst_2859_, 0);
                    v_isSharedCheck_2900_ = (!lean_is_exclusive(v_fst_2859_)) as u8;
                    if v_isSharedCheck_2900_ == 0 {
                        v___x_2880_ = v_fst_2859_;
                        v_isShared_2881_ = v_isSharedCheck_2900_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2878_);
                        lean_dec(v_fst_2859_);
                        v___x_2880_ = lean_box(0);
                        v_isShared_2881_ = v_isSharedCheck_2900_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2864_ = lean_ctor_get(v_fst_2859_, 0);
                v_isSharedCheck_2875_ = (!lean_is_exclusive(v_fst_2859_)) as u8;
                if v_isSharedCheck_2875_ == 0 {
                    v___x_2866_ = v_fst_2859_;
                    v_isShared_2867_ = v_isSharedCheck_2875_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2864_);
                    lean_dec(v_fst_2859_);
                    v___x_2866_ = lean_box(0);
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
                    v_reuseFailAlloc_2874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2874_, 0, v_a_2864_);
                    v___x_2869_ = v_reuseFailAlloc_2874_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2863_ == 0 {
                    lean_ctor_set(v___x_2862_, 0, v___x_2869_);
                    v___x_2871_ = v___x_2862_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2873_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2873_, 0, v___x_2869_);
                    lean_ctor_set(v_reuseFailAlloc_2873_, 1, v_snd_2860_);
                    v___x_2871_ = v_reuseFailAlloc_2873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2872_ = lean_apply_2(v_toPure_2852_, lean_box(0), v___x_2871_);
                return v___x_2872_;
            }
            5 => {
                v___x_2882_ = (lean_unbox(v_a_2878_) as u8);
                lean_dec(v_a_2878_);
                if v___x_2882_ == 0 {
                    lean_del_object(v___x_2880_);
                    lean_dec(v___x_2857_);
                    lean_dec(v_toPure_2852_);
                    v_snd_2883_ = lean_ctor_get(v_____x_2858_, 1);
                    lean_inc(v_snd_2883_);
                    lean_dec_ref(v_____x_2858_);
                    v___x_2884_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_restore___redArg(v___x_2853_, v_inst_2854_, v_snd_2883_);
                    v___x_2885_ = lean_apply_4(
                        v_toBind_2855_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2884_,
                        v___f_2856_,
                    );
                    return v___x_2885_;
                } else {
                    lean_dec(v___f_2856_);
                    lean_dec(v_toBind_2855_);
                    lean_dec_ref(v_inst_2854_);
                    v_snd_2886_ = lean_ctor_get(v_____x_2858_, 1);
                    v_isSharedCheck_2898_ = (!lean_is_exclusive(v_____x_2858_)) as u8;
                    if v_isSharedCheck_2898_ == 0 {
                        v_unused_2899_ = lean_ctor_get(v_____x_2858_, 0);
                        lean_dec(v_unused_2899_);
                        v___x_2888_ = v_____x_2858_;
                        v_isShared_2889_ = v_isSharedCheck_2898_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_snd_2886_);
                        lean_dec(v_____x_2858_);
                        v___x_2888_ = lean_box(0);
                        v_isShared_2889_ = v_isSharedCheck_2898_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                v___x_2890_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2890_, 0, v___x_2857_);
                if v_isShared_2881_ == 0 {
                    lean_ctor_set(v___x_2880_, 0, v___x_2890_);
                    v___x_2892_ = v___x_2880_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2897_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2897_, 0, v___x_2890_);
                    v___x_2892_ = v_reuseFailAlloc_2897_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_2889_ == 0 {
                    lean_ctor_set(v___x_2888_, 0, v___x_2892_);
                    v___x_2894_ = v___x_2888_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2896_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2896_, 0, v___x_2892_);
                    lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_snd_2886_);
                    v___x_2894_ = v_reuseFailAlloc_2896_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_2895_ = lean_apply_2(v_toPure_2852_, lean_box(0), v___x_2894_);
                return v___x_2895_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed(
    mut v_toPure_2901_: *mut LeanObject,
    mut v___x_2902_: *mut LeanObject,
    mut v_inst_2903_: *mut LeanObject,
    mut v_toBind_2904_: *mut LeanObject,
    mut v___f_2905_: *mut LeanObject,
    mut v___x_2906_: *mut LeanObject,
    mut v_____x_2907_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2908_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___x_2902_);
    return v_res_2908_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(
    mut v_toPure_2909_: *mut LeanObject,
    mut v_inst_2910_: *mut LeanObject,
    mut v___y_2911_: *mut LeanObject,
    mut v_toBind_2912_: *mut LeanObject,
    mut v___f_2913_: *mut LeanObject,
    mut v_____x_2914_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2919_: u8 = 0;
    let mut v_a_2920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2923_: u8 = 0;
    let mut v___x_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2931_: u8 = 0;
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_unused_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2915_ = lean_ctor_get(v_____x_2914_, 0);
                lean_inc(v_fst_2915_);
                if lean_obj_tag(v_fst_2915_) == 0 {
                    lean_dec(v___f_2913_);
                    lean_dec(v_toBind_2912_);
                    lean_dec_ref(v_inst_2910_);
                    v_snd_2916_ = lean_ctor_get(v_____x_2914_, 1);
                    v_isSharedCheck_2932_ = (!lean_is_exclusive(v_____x_2914_)) as u8;
                    if v_isSharedCheck_2932_ == 0 {
                        v_unused_2933_ = lean_ctor_get(v_____x_2914_, 0);
                        lean_dec(v_unused_2933_);
                        v___x_2918_ = v_____x_2914_;
                        v_isShared_2919_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2916_);
                        lean_dec(v_____x_2914_);
                        v___x_2918_ = lean_box(0);
                        v_isShared_2919_ = v_isSharedCheck_2932_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_fst_2915_, 1);
                    lean_dec(v_toPure_2909_);
                    v_snd_2934_ = lean_ctor_get(v_____x_2914_, 1);
                    lean_inc(v_snd_2934_);
                    lean_dec_ref(v_____x_2914_);
                    v___x_2935_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg(v_inst_2910_, v___y_2911_, v_snd_2934_);
                    v___x_2936_ = lean_apply_4(
                        v_toBind_2912_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2935_,
                        v___f_2913_,
                    );
                    return v___x_2936_;
                }
            }
            1 => {
                v_a_2920_ = lean_ctor_get(v_fst_2915_, 0);
                v_isSharedCheck_2931_ = (!lean_is_exclusive(v_fst_2915_)) as u8;
                if v_isSharedCheck_2931_ == 0 {
                    v___x_2922_ = v_fst_2915_;
                    v_isShared_2923_ = v_isSharedCheck_2931_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2920_);
                    lean_dec(v_fst_2915_);
                    v___x_2922_ = lean_box(0);
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
                    v_reuseFailAlloc_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2930_, 0, v_a_2920_);
                    v___x_2925_ = v_reuseFailAlloc_2930_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2919_ == 0 {
                    lean_ctor_set(v___x_2918_, 0, v___x_2925_);
                    v___x_2927_ = v___x_2918_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2929_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2925_);
                    lean_ctor_set(v_reuseFailAlloc_2929_, 1, v_snd_2916_);
                    v___x_2927_ = v_reuseFailAlloc_2929_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2928_ = lean_apply_2(v_toPure_2909_, lean_box(0), v___x_2927_);
                return v___x_2928_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed(
    mut v_toPure_2937_: *mut LeanObject,
    mut v_inst_2938_: *mut LeanObject,
    mut v___y_2939_: *mut LeanObject,
    mut v_toBind_2940_: *mut LeanObject,
    mut v___f_2941_: *mut LeanObject,
    mut v_____x_2942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2943_: *mut LeanObject = core::ptr::null_mut();
    v_res_2943_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4(
            v_toPure_2937_,
            v_inst_2938_,
            v___y_2939_,
            v_toBind_2940_,
            v___f_2941_,
            v_____x_2942_,
        );
    lean_dec_ref(v___y_2939_);
    return v_res_2943_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5(
    mut v_toPure_2944_: *mut LeanObject,
    mut v___x_2945_: *mut LeanObject,
    mut v_inst_2946_: *mut LeanObject,
    mut v_toBind_2947_: *mut LeanObject,
    mut v___f_2948_: *mut LeanObject,
    mut v___y_2949_: *mut LeanObject,
    mut v_____x_2950_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2955_: u8 = 0;
    let mut v_a_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2959_: u8 = 0;
    let mut v___x_2961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut v_isSharedCheck_2968_: u8 = 0;
    let mut v_unused_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2951_ = lean_ctor_get(v_____x_2950_, 0);
                lean_inc(v_fst_2951_);
                if lean_obj_tag(v_fst_2951_) == 0 {
                    lean_dec(v___f_2948_);
                    lean_dec(v_toBind_2947_);
                    lean_dec_ref(v_inst_2946_);
                    lean_dec(v___x_2945_);
                    v_snd_2952_ = lean_ctor_get(v_____x_2950_, 1);
                    v_isSharedCheck_2968_ = (!lean_is_exclusive(v_____x_2950_)) as u8;
                    if v_isSharedCheck_2968_ == 0 {
                        v_unused_2969_ = lean_ctor_get(v_____x_2950_, 0);
                        lean_dec(v_unused_2969_);
                        v___x_2954_ = v_____x_2950_;
                        v_isShared_2955_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2952_);
                        lean_dec(v_____x_2950_);
                        v___x_2954_ = lean_box(0);
                        v_isShared_2955_ = v_isSharedCheck_2968_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2970_ = lean_ctor_get(v_fst_2951_, 0);
                    lean_inc(v_a_2970_);
                    lean_dec_ref_known(v_fst_2951_, 1);
                    v_snd_2971_ = lean_ctor_get(v_____x_2950_, 1);
                    lean_inc(v_snd_2971_);
                    lean_dec_ref(v_____x_2950_);
                    v_added_2972_ = lean_ctor_get(v_a_2970_, 1);
                    lean_inc_ref(v_added_2972_);
                    lean_dec(v_a_2970_);
                    v___x_2973_ = lean_unsigned_to_nat(0);
                    v___x_2974_ = lean_array_get(v___x_2973_, v_added_2972_, v___x_2945_);
                    lean_dec_ref(v_added_2972_);
                    lean_inc_n(v_toBind_2947_, 2);
                    lean_inc_ref_n(v_inst_2946_, 2);
                    lean_inc(v___x_2974_);
                    lean_inc(v_toPure_2944_);
                    v___f_2975_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__3___boxed as *mut core::ffi::c_void, 7, 6);
                    lean_closure_set(v___f_2975_, 0, v_toPure_2944_);
                    lean_closure_set(v___f_2975_, 1, v___x_2974_);
                    lean_closure_set(v___f_2975_, 2, v_inst_2946_);
                    lean_closure_set(v___f_2975_, 3, v_toBind_2947_);
                    lean_closure_set(v___f_2975_, 4, v___f_2948_);
                    lean_closure_set(v___f_2975_, 5, v___x_2945_);
                    lean_inc_ref(v___y_2949_);
                    v___f_2976_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__4___boxed as *mut core::ffi::c_void, 6, 5);
                    lean_closure_set(v___f_2976_, 0, v_toPure_2944_);
                    lean_closure_set(v___f_2976_, 1, v_inst_2946_);
                    lean_closure_set(v___f_2976_, 2, v___y_2949_);
                    lean_closure_set(v___f_2976_, 3, v_toBind_2947_);
                    lean_closure_set(v___f_2976_, 4, v___f_2975_);
                    v___x_2977_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_erase___redArg(v___x_2974_, v_inst_2946_, v_snd_2971_);
                    lean_dec(v___x_2974_);
                    v___x_2978_ = lean_apply_4(
                        v_toBind_2947_,
                        lean_box(0),
                        lean_box(0),
                        v___x_2977_,
                        v___f_2976_,
                    );
                    return v___x_2978_;
                }
            }
            1 => {
                v_a_2956_ = lean_ctor_get(v_fst_2951_, 0);
                v_isSharedCheck_2967_ = (!lean_is_exclusive(v_fst_2951_)) as u8;
                if v_isSharedCheck_2967_ == 0 {
                    v___x_2958_ = v_fst_2951_;
                    v_isShared_2959_ = v_isSharedCheck_2967_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_2956_);
                    lean_dec(v_fst_2951_);
                    v___x_2958_ = lean_box(0);
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
                    v_reuseFailAlloc_2966_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2956_);
                    v___x_2961_ = v_reuseFailAlloc_2966_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2955_ == 0 {
                    lean_ctor_set(v___x_2954_, 0, v___x_2961_);
                    v___x_2963_ = v___x_2954_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2965_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2965_, 0, v___x_2961_);
                    lean_ctor_set(v_reuseFailAlloc_2965_, 1, v_snd_2952_);
                    v___x_2963_ = v_reuseFailAlloc_2965_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2964_ = lean_apply_2(v_toPure_2944_, lean_box(0), v___x_2963_);
                return v___x_2964_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed(
    mut v_toPure_2979_: *mut LeanObject,
    mut v___x_2980_: *mut LeanObject,
    mut v_inst_2981_: *mut LeanObject,
    mut v_toBind_2982_: *mut LeanObject,
    mut v___f_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v_____x_2985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2986_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_2984_);
    return v_res_2986_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7(
    mut v_toPure_2987_: *mut LeanObject,
    mut v_toBind_2988_: *mut LeanObject,
    mut v___f_2989_: *mut LeanObject,
    mut v___x_2990_: *mut LeanObject,
    mut v_inst_2991_: *mut LeanObject,
    mut v_b_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    v___x_2995_ = lean_unsigned_to_nat(0);
    v___x_2996_ = lean_nat_dec_lt(v___x_2995_, v_b_2992_);
    if v___x_2996_ == 0 {
        let mut v___x_2997_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3000_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3001_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_inst_2991_);
        v___x_2997_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2997_, 0, v_b_2992_);
        v___x_2998_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_2998_, 0, v___x_2997_);
        v___x_2999_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_2999_, 0, v___x_2998_);
        lean_ctor_set(v___x_2999_, 1, v___y_2994_);
        v___x_3000_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_2999_);
        v___x_3001_ = lean_apply_4(
            v_toBind_2988_,
            lean_box(0),
            lean_box(0),
            v___x_3000_,
            v___f_2989_,
        );
        return v___x_3001_;
    } else {
        let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_3005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
        v___x_3002_ = lean_nat_sub(v_b_2992_, v___x_2990_);
        lean_dec(v_b_2992_);
        lean_inc(v___x_3002_);
        lean_inc_n(v_toPure_2987_, 3);
        v___f_3003_ = lean_alloc_closure(
            l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__2
                as *mut core::ffi::c_void,
            3,
            2,
        );
        lean_closure_set(v___f_3003_, 0, v_toPure_2987_);
        lean_closure_set(v___f_3003_, 1, v___x_3002_);
        lean_inc_ref(v___y_2993_);
        lean_inc_n(v_toBind_2988_, 3);
        v___f_3004_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__5___boxed as *mut core::ffi::c_void, 7, 6);
        lean_closure_set(v___f_3004_, 0, v_toPure_2987_);
        lean_closure_set(v___f_3004_, 1, v___x_3002_);
        lean_closure_set(v___f_3004_, 2, v_inst_2991_);
        lean_closure_set(v___f_3004_, 3, v_toBind_2988_);
        lean_closure_set(v___f_3004_, 4, v___f_3003_);
        lean_closure_set(v___f_3004_, 5, v___y_2993_);
        v___f_3005_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
        lean_closure_set(v___f_3005_, 0, v_toPure_2987_);
        lean_inc_ref(v___y_2994_);
        v___x_3006_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_3006_, 0, v___y_2994_);
        lean_ctor_set(v___x_3006_, 1, v___y_2994_);
        v___x_3007_ = lean_apply_2(v_toPure_2987_, lean_box(0), v___x_3006_);
        v___x_3008_ = lean_apply_4(
            v_toBind_2988_,
            lean_box(0),
            lean_box(0),
            v___x_3007_,
            v___f_3005_,
        );
        v___x_3009_ = lean_apply_4(
            v_toBind_2988_,
            lean_box(0),
            lean_box(0),
            v___x_3008_,
            v___f_3004_,
        );
        v___x_3010_ = lean_apply_4(
            v_toBind_2988_,
            lean_box(0),
            lean_box(0),
            v___x_3009_,
            v___f_2989_,
        );
        return v___x_3010_;
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed(
    mut v_toPure_3011_: *mut LeanObject,
    mut v_toBind_3012_: *mut LeanObject,
    mut v___f_3013_: *mut LeanObject,
    mut v___x_3014_: *mut LeanObject,
    mut v_inst_3015_: *mut LeanObject,
    mut v_b_3016_: *mut LeanObject,
    mut v___y_3017_: *mut LeanObject,
    mut v___y_3018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3019_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v___y_3017_);
    lean_dec(v___x_3014_);
    return v_res_3019_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6(
    mut v_toPure_3020_: *mut LeanObject,
    mut v_toBind_3021_: *mut LeanObject,
    mut v___f_3022_: *mut LeanObject,
    mut v_inst_3023_: *mut LeanObject,
    mut v___x_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v___f_3026_: *mut LeanObject,
    mut v_____x_3027_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3032_: u8 = 0;
    let mut v_a_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3044_: u8 = 0;
    let mut v_isSharedCheck_3045_: u8 = 0;
    let mut v_unused_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_added_3049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143__overap_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3028_ = lean_ctor_get(v_____x_3027_, 0);
                lean_inc(v_fst_3028_);
                if lean_obj_tag(v_fst_3028_) == 0 {
                    lean_dec(v___f_3026_);
                    lean_dec_ref(v___x_3024_);
                    lean_dec_ref(v_inst_3023_);
                    lean_dec(v___f_3022_);
                    lean_dec(v_toBind_3021_);
                    v_snd_3029_ = lean_ctor_get(v_____x_3027_, 1);
                    v_isSharedCheck_3045_ = (!lean_is_exclusive(v_____x_3027_)) as u8;
                    if v_isSharedCheck_3045_ == 0 {
                        v_unused_3046_ = lean_ctor_get(v_____x_3027_, 0);
                        lean_dec(v_unused_3046_);
                        v___x_3031_ = v_____x_3027_;
                        v_isShared_3032_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3029_);
                        lean_dec(v_____x_3027_);
                        v___x_3031_ = lean_box(0);
                        v_isShared_3032_ = v_isSharedCheck_3045_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3047_ = lean_ctor_get(v_fst_3028_, 0);
                    lean_inc(v_a_3047_);
                    lean_dec_ref_known(v_fst_3028_, 1);
                    v_snd_3048_ = lean_ctor_get(v_____x_3027_, 1);
                    lean_inc(v_snd_3048_);
                    lean_dec_ref(v_____x_3027_);
                    v_added_3049_ = lean_ctor_get(v_a_3047_, 1);
                    lean_inc_ref(v_added_3049_);
                    lean_dec(v_a_3047_);
                    v___x_3050_ = lean_array_get_size(v_added_3049_);
                    lean_dec_ref(v_added_3049_);
                    v___x_3051_ = lean_unsigned_to_nat(1);
                    lean_inc(v_toBind_3021_);
                    v___f_3052_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__7___boxed as *mut core::ffi::c_void, 8, 5);
                    lean_closure_set(v___f_3052_, 0, v_toPure_3020_);
                    lean_closure_set(v___f_3052_, 1, v_toBind_3021_);
                    lean_closure_set(v___f_3052_, 2, v___f_3022_);
                    lean_closure_set(v___f_3052_, 3, v___x_3051_);
                    lean_closure_set(v___f_3052_, 4, v_inst_3023_);
                    v___x_3053_ = lean_nat_sub(v___x_3050_, v___x_3051_);
                    v___x_6143__overap_3054_ = l___private_Init_While_0__whileM_erased___redArg(
                        v___x_3024_,
                        v___f_3052_,
                        v___x_3053_,
                    );
                    lean_inc_ref(v_a_3025_);
                    v___x_3055_ = lean_apply_2(v___x_6143__overap_3054_, v_a_3025_, v_snd_3048_);
                    v___x_3056_ = lean_apply_4(
                        v_toBind_3021_,
                        lean_box(0),
                        lean_box(0),
                        v___x_3055_,
                        v___f_3026_,
                    );
                    return v___x_3056_;
                }
            }
            1 => {
                v_a_3033_ = lean_ctor_get(v_fst_3028_, 0);
                v_isSharedCheck_3044_ = (!lean_is_exclusive(v_fst_3028_)) as u8;
                if v_isSharedCheck_3044_ == 0 {
                    v___x_3035_ = v_fst_3028_;
                    v_isShared_3036_ = v_isSharedCheck_3044_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3033_);
                    lean_dec(v_fst_3028_);
                    v___x_3035_ = lean_box(0);
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
                    v_reuseFailAlloc_3043_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3043_, 0, v_a_3033_);
                    v___x_3038_ = v_reuseFailAlloc_3043_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3032_ == 0 {
                    lean_ctor_set(v___x_3031_, 0, v___x_3038_);
                    v___x_3040_ = v___x_3031_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3042_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 0, v___x_3038_);
                    lean_ctor_set(v_reuseFailAlloc_3042_, 1, v_snd_3029_);
                    v___x_3040_ = v_reuseFailAlloc_3042_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3041_ = lean_apply_2(v_toPure_3020_, lean_box(0), v___x_3040_);
                return v___x_3041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed(
    mut v_toPure_3057_: *mut LeanObject,
    mut v_toBind_3058_: *mut LeanObject,
    mut v___f_3059_: *mut LeanObject,
    mut v_inst_3060_: *mut LeanObject,
    mut v___x_3061_: *mut LeanObject,
    mut v_a_3062_: *mut LeanObject,
    mut v___f_3063_: *mut LeanObject,
    mut v_____x_3064_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3065_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_a_3062_);
    return v_res_3065_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
    mut v_inst_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toApplicative_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref_n(v_inst_3066_, 7);
    v___f_3069_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3069_, 0, v_inst_3066_);
    v___f_3070_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3070_, 0, v_inst_3066_);
    v___f_3071_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3071_, 0, v_inst_3066_);
    v___f_3072_ = lean_alloc_closure(
        l_StateT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        6,
        1,
    );
    lean_closure_set(v___f_3072_, 0, v_inst_3066_);
    v___x_3073_ = lean_alloc_closure(l_StateT_map as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_3073_, 0, lean_box(0));
    lean_closure_set(v___x_3073_, 1, lean_box(0));
    lean_closure_set(v___x_3073_, 2, v_inst_3066_);
    v___x_3074_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3074_, 0, v___x_3073_);
    lean_ctor_set(v___x_3074_, 1, v___f_3069_);
    v___x_3075_ = lean_alloc_closure(l_StateT_pure as *mut core::ffi::c_void, 6, 3);
    lean_closure_set(v___x_3075_, 0, lean_box(0));
    lean_closure_set(v___x_3075_, 1, lean_box(0));
    lean_closure_set(v___x_3075_, 2, v_inst_3066_);
    v___x_3076_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3076_, 0, v___x_3074_);
    lean_ctor_set(v___x_3076_, 1, v___x_3075_);
    lean_ctor_set(v___x_3076_, 2, v___f_3070_);
    lean_ctor_set(v___x_3076_, 3, v___f_3071_);
    lean_ctor_set(v___x_3076_, 4, v___f_3072_);
    v___x_3077_ = lean_alloc_closure(l_StateT_bind as *mut core::ffi::c_void, 8, 3);
    lean_closure_set(v___x_3077_, 0, lean_box(0));
    lean_closure_set(v___x_3077_, 1, lean_box(0));
    lean_closure_set(v___x_3077_, 2, v_inst_3066_);
    v___x_3078_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3078_, 0, v___x_3076_);
    lean_ctor_set(v___x_3078_, 1, v___x_3077_);
    lean_inc_ref_n(v___x_3078_, 6);
    v___f_3079_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__1 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3079_, 0, v___x_3078_);
    v___f_3080_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__4 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3080_, 0, v___x_3078_);
    v___f_3081_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__7 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3081_, 0, v___x_3078_);
    v___f_3082_ = lean_alloc_closure(
        l_ExceptT_instMonad___redArg___lam__9 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_3082_, 0, v___x_3078_);
    v___x_3083_ = lean_alloc_closure(l_ExceptT_map as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_3083_, 0, lean_box(0));
    lean_closure_set(v___x_3083_, 1, lean_box(0));
    lean_closure_set(v___x_3083_, 2, v___x_3078_);
    v___x_3084_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3084_, 0, v___x_3083_);
    lean_ctor_set(v___x_3084_, 1, v___f_3079_);
    v___x_3085_ = lean_alloc_closure(l_ExceptT_pure as *mut core::ffi::c_void, 5, 3);
    lean_closure_set(v___x_3085_, 0, lean_box(0));
    lean_closure_set(v___x_3085_, 1, lean_box(0));
    lean_closure_set(v___x_3085_, 2, v___x_3078_);
    v___x_3086_ = lean_alloc_ctor(0, 5, (0) as u32);
    lean_ctor_set(v___x_3086_, 0, v___x_3084_);
    lean_ctor_set(v___x_3086_, 1, v___x_3085_);
    lean_ctor_set(v___x_3086_, 2, v___f_3080_);
    lean_ctor_set(v___x_3086_, 3, v___f_3081_);
    lean_ctor_set(v___x_3086_, 4, v___f_3082_);
    v___x_3087_ = lean_alloc_closure(l_ExceptT_bind as *mut core::ffi::c_void, 7, 3);
    lean_closure_set(v___x_3087_, 0, lean_box(0));
    lean_closure_set(v___x_3087_, 1, lean_box(0));
    lean_closure_set(v___x_3087_, 2, v___x_3078_);
    v___x_3088_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3088_, 0, v___x_3086_);
    lean_ctor_set(v___x_3088_, 1, v___x_3087_);
    v___x_3089_ = l_ReaderT_instMonad___redArg(v___x_3088_);
    v_toApplicative_3090_ = lean_ctor_get(v_inst_3066_, 0);
    v_toBind_3091_ = lean_ctor_get(v_inst_3066_, 1);
    lean_inc_n(v_toBind_3091_, 3);
    v_toPure_3092_ = lean_ctor_get(v_toApplicative_3090_, 1);
    lean_inc_n(v_toPure_3092_, 5);
    v___f_3093_ = lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3093_, 0, v_toPure_3092_);
    v___f_3094_ = lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__1
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3094_, 0, v_toPure_3092_);
    lean_inc_ref(v_a_3067_);
    v___f_3095_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__6___boxed as *mut core::ffi::c_void, 8, 7);
    lean_closure_set(v___f_3095_, 0, v_toPure_3092_);
    lean_closure_set(v___f_3095_, 1, v_toBind_3091_);
    lean_closure_set(v___f_3095_, 2, v___f_3094_);
    lean_closure_set(v___f_3095_, 3, v_inst_3066_);
    lean_closure_set(v___f_3095_, 4, v___x_3089_);
    lean_closure_set(v___f_3095_, 5, v_a_3067_);
    lean_closure_set(v___f_3095_, 6, v___f_3093_);
    v___f_3096_ = lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3096_, 0, v_toPure_3092_);
    lean_inc_ref(v_a_3068_);
    v___x_3097_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3097_, 0, v_a_3068_);
    lean_ctor_set(v___x_3097_, 1, v_a_3068_);
    v___x_3098_ = lean_apply_2(v_toPure_3092_, lean_box(0), v___x_3097_);
    v___x_3099_ = lean_apply_4(
        v_toBind_3091_,
        lean_box(0),
        lean_box(0),
        v___x_3098_,
        v___f_3096_,
    );
    v___x_3100_ = lean_apply_4(
        v_toBind_3091_,
        lean_box(0),
        lean_box(0),
        v___x_3099_,
        v___f_3095_,
    );
    return v___x_3100_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___boxed(
    mut v_inst_3101_: *mut LeanObject,
    mut v_a_3102_: *mut LeanObject,
    mut v_a_3103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3104_: *mut LeanObject = core::ptr::null_mut();
    v_res_3104_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
        v_inst_3101_,
        v_a_3102_,
        v_a_3103_,
    );
    lean_dec_ref(v_a_3102_);
    return v_res_3104_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(
    mut v_m_3105_: *mut LeanObject,
    mut v_inst_3106_: *mut LeanObject,
    mut v_a_3107_: *mut LeanObject,
    mut v_a_3108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3109_: *mut LeanObject = core::ptr::null_mut();
    v___x_3109_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(
        v_inst_3106_,
        v_a_3107_,
        v_a_3108_,
    );
    return v___x_3109_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___boxed(
    mut v_m_3110_: *mut LeanObject,
    mut v_inst_3111_: *mut LeanObject,
    mut v_a_3112_: *mut LeanObject,
    mut v_a_3113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3114_: *mut LeanObject = core::ptr::null_mut();
    v_res_3114_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune(
        v_m_3110_,
        v_inst_3111_,
        v_a_3112_,
        v_a_3113_,
    );
    lean_dec_ref(v_a_3112_);
    return v_res_3114_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(
    mut v_toApplicative_3115_: *mut LeanObject,
    mut v_inst_3116_: *mut LeanObject,
    mut v_a_3117_: *mut LeanObject,
    mut v_____x_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3123_: u8 = 0;
    let mut v_a_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3127_: u8 = 0;
    let mut v_toPure_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3136_: u8 = 0;
    let mut v_isSharedCheck_3137_: u8 = 0;
    let mut v_unused_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_3140_: u8 = 0;
    let mut v_snd_3141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v_toPure_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3151_: u8 = 0;
    let mut v_unused_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3119_ = lean_ctor_get(v_____x_3118_, 0);
                lean_inc(v_fst_3119_);
                if lean_obj_tag(v_fst_3119_) == 0 {
                    lean_dec_ref(v_inst_3116_);
                    v_snd_3120_ = lean_ctor_get(v_____x_3118_, 1);
                    v_isSharedCheck_3137_ = (!lean_is_exclusive(v_____x_3118_)) as u8;
                    if v_isSharedCheck_3137_ == 0 {
                        v_unused_3138_ = lean_ctor_get(v_____x_3118_, 0);
                        lean_dec(v_unused_3138_);
                        v___x_3122_ = v_____x_3118_;
                        v_isShared_3123_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3120_);
                        lean_dec(v_____x_3118_);
                        v___x_3122_ = lean_box(0);
                        v_isShared_3123_ = v_isSharedCheck_3137_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3139_ = lean_ctor_get(v_fst_3119_, 0);
                    lean_inc(v_a_3139_);
                    lean_dec_ref_known(v_fst_3119_, 1);
                    v_found_3140_ = lean_ctor_get_uint8(
                        v_a_3139_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    );
                    lean_dec(v_a_3139_);
                    if v_found_3140_ == 0 {
                        lean_dec_ref(v_inst_3116_);
                        v_snd_3141_ = lean_ctor_get(v_____x_3118_, 1);
                        v_isSharedCheck_3151_ = (!lean_is_exclusive(v_____x_3118_)) as u8;
                        if v_isSharedCheck_3151_ == 0 {
                            v_unused_3152_ = lean_ctor_get(v_____x_3118_, 0);
                            lean_dec(v_unused_3152_);
                            v___x_3143_ = v_____x_3118_;
                            v_isShared_3144_ = v_isSharedCheck_3151_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_snd_3141_);
                            lean_dec(v_____x_3118_);
                            v___x_3143_ = lean_box(0);
                            v_isShared_3144_ = v_isSharedCheck_3151_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_toApplicative_3115_);
                        v_snd_3153_ = lean_ctor_get(v_____x_3118_, 1);
                        lean_inc(v_snd_3153_);
                        lean_dec_ref(v_____x_3118_);
                        v___x_3154_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg(v_inst_3116_, v_a_3117_, v_snd_3153_);
                        return v___x_3154_;
                    }
                }
            }
            1 => {
                v_a_3124_ = lean_ctor_get(v_fst_3119_, 0);
                v_isSharedCheck_3136_ = (!lean_is_exclusive(v_fst_3119_)) as u8;
                if v_isSharedCheck_3136_ == 0 {
                    v___x_3126_ = v_fst_3119_;
                    v_isShared_3127_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_a_3124_);
                    lean_dec(v_fst_3119_);
                    v___x_3126_ = lean_box(0);
                    v_isShared_3127_ = v_isSharedCheck_3136_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toPure_3128_ = lean_ctor_get(v_toApplicative_3115_, 1);
                lean_inc(v_toPure_3128_);
                lean_dec_ref(v_toApplicative_3115_);
                if v_isShared_3127_ == 0 {
                    v___x_3130_ = v___x_3126_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3135_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3135_, 0, v_a_3124_);
                    v___x_3130_ = v_reuseFailAlloc_3135_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3123_ == 0 {
                    lean_ctor_set(v___x_3122_, 0, v___x_3130_);
                    v___x_3132_ = v___x_3122_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3134_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 0, v___x_3130_);
                    lean_ctor_set(v_reuseFailAlloc_3134_, 1, v_snd_3120_);
                    v___x_3132_ = v_reuseFailAlloc_3134_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3133_ = lean_apply_2(v_toPure_3128_, lean_box(0), v___x_3132_);
                return v___x_3133_;
            }
            5 => {
                v_toPure_3145_ = lean_ctor_get(v_toApplicative_3115_, 1);
                lean_inc(v_toPure_3145_);
                lean_dec_ref(v_toApplicative_3115_);
                v___x_3146_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_prune___redArg___lam__0___closed__0;
                if v_isShared_3144_ == 0 {
                    lean_ctor_set(v___x_3143_, 0, v___x_3146_);
                    v___x_3148_ = v___x_3143_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3150_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 0, v___x_3146_);
                    lean_ctor_set(v_reuseFailAlloc_3150_, 1, v_snd_3141_);
                    v___x_3148_ = v_reuseFailAlloc_3150_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_3149_ = lean_apply_2(v_toPure_3145_, lean_box(0), v___x_3148_);
                return v___x_3149_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed(
    mut v_toApplicative_3155_: *mut LeanObject,
    mut v_inst_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_____x_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3159_: *mut LeanObject = core::ptr::null_mut();
    v_res_3159_ =
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0(
            v_toApplicative_3155_,
            v_inst_3156_,
            v_a_3157_,
            v_____x_3158_,
        );
    lean_dec_ref(v_a_3157_);
    return v_res_3159_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2(
    mut v_toApplicative_3160_: *mut LeanObject,
    mut v_toBind_3161_: *mut LeanObject,
    mut v___f_3162_: *mut LeanObject,
    mut v_____x_3163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v_toPure_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3179_: u8 = 0;
    let mut v_unused_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_3164_ = lean_ctor_get(v_____x_3163_, 0);
                if lean_obj_tag(v_fst_3164_) == 0 {
                    lean_dec(v___f_3162_);
                    lean_dec(v_toBind_3161_);
                    v_toPure_3165_ = lean_ctor_get(v_toApplicative_3160_, 1);
                    lean_inc(v_toPure_3165_);
                    lean_dec_ref(v_toApplicative_3160_);
                    v___x_3166_ = lean_apply_2(v_toPure_3165_, lean_box(0), v_____x_3163_);
                    return v___x_3166_;
                } else {
                    v_snd_3167_ = lean_ctor_get(v_____x_3163_, 1);
                    v_isSharedCheck_3179_ = (!lean_is_exclusive(v_____x_3163_)) as u8;
                    if v_isSharedCheck_3179_ == 0 {
                        v_unused_3180_ = lean_ctor_get(v_____x_3163_, 0);
                        lean_dec(v_unused_3180_);
                        v___x_3169_ = v_____x_3163_;
                        v_isShared_3170_ = v_isSharedCheck_3179_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3167_);
                        lean_dec(v_____x_3163_);
                        v___x_3169_ = lean_box(0);
                        v_isShared_3170_ = v_isSharedCheck_3179_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_toPure_3171_ = lean_ctor_get(v_toApplicative_3160_, 1);
                lean_inc_n(v_toPure_3171_, 2);
                lean_dec_ref(v_toApplicative_3160_);
                v___f_3172_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_tryCur___redArg___lam__5 as *mut core::ffi::c_void, 2, 1);
                lean_closure_set(v___f_3172_, 0, v_toPure_3171_);
                lean_inc(v_snd_3167_);
                if v_isShared_3170_ == 0 {
                    lean_ctor_set(v___x_3169_, 0, v_snd_3167_);
                    v___x_3174_ = v___x_3169_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 0, v_snd_3167_);
                    lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_snd_3167_);
                    v___x_3174_ = v_reuseFailAlloc_3178_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3175_ = lean_apply_2(v_toPure_3171_, lean_box(0), v___x_3174_);
                lean_inc(v_toBind_3161_);
                v___x_3176_ = lean_apply_4(
                    v_toBind_3161_,
                    lean_box(0),
                    lean_box(0),
                    v___x_3175_,
                    v___f_3172_,
                );
                v___x_3177_ = lean_apply_4(
                    v_toBind_3161_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_3181_: *mut LeanObject,
    mut v_a_3182_: *mut LeanObject,
    mut v_a_3183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3184_ = lean_ctor_get(v_inst_3181_, 0);
    v_toBind_3185_ = lean_ctor_get(v_inst_3181_, 1);
    lean_inc_n(v_toBind_3185_, 2);
    lean_inc_ref(v_a_3182_);
    lean_inc_ref(v_inst_3181_);
    lean_inc_ref_n(v_toApplicative_3184_, 2);
    v___f_3186_ = lean_alloc_closure(l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
    lean_closure_set(v___f_3186_, 0, v_toApplicative_3184_);
    lean_closure_set(v___f_3186_, 1, v_inst_3181_);
    lean_closure_set(v___f_3186_, 2, v_a_3182_);
    v___f_3187_ = lean_alloc_closure(
        l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___lam__2
            as *mut core::ffi::c_void,
        4,
        3,
    );
    lean_closure_set(v___f_3187_, 0, v_toApplicative_3184_);
    lean_closure_set(v___f_3187_, 1, v_toBind_3185_);
    lean_closure_set(v___f_3187_, 2, v___f_3186_);
    v___x_3188_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_init___redArg(
        v_inst_3181_,
        v_a_3182_,
        v_a_3183_,
    );
    v___x_3189_ = lean_apply_4(
        v_toBind_3185_,
        lean_box(0),
        lean_box(0),
        v___x_3188_,
        v___f_3187_,
    );
    return v___x_3189_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg___boxed(
    mut v_inst_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
    mut v_a_3192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3193_: *mut LeanObject = core::ptr::null_mut();
    v_res_3193_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
        v_inst_3190_,
        v_a_3191_,
        v_a_3192_,
    );
    lean_dec_ref(v_a_3191_);
    return v_res_3193_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(
    mut v_m_3194_: *mut LeanObject,
    mut v_inst_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
    mut v_a_3197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    v___x_3198_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
        v_inst_3195_,
        v_a_3196_,
        v_a_3197_,
    );
    return v___x_3198_;
}
pub unsafe fn l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___boxed(
    mut v_m_3199_: *mut LeanObject,
    mut v_inst_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3203_: *mut LeanObject = core::ptr::null_mut();
    v_res_3203_ = l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main(
        v_m_3199_,
        v_inst_3200_,
        v_a_3201_,
        v_a_3202_,
    );
    lean_dec_ref(v_a_3201_);
    return v_res_3203_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__0(
    mut v_toApplicative_3204_: *mut LeanObject,
    mut v_____x_3205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_snd_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cur_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_numCalls_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_found_3210_: u8 = 0;
    let mut v___y_3212_: u8 = 0;
    let mut v_toPure_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: u8 = 0;
    let mut v___x_3217_: u8 = 0;
    let mut v___x_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_3206_ = lean_ctor_get(v_____x_3205_, 1);
                v_fst_3207_ = lean_ctor_get(v_____x_3205_, 0);
                v_cur_3208_ = lean_ctor_get(v_snd_3206_, 0);
                v_numCalls_3209_ = lean_ctor_get(v_snd_3206_, 2);
                v_found_3210_ = lean_ctor_get_uint8(
                    v_snd_3206_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                if v_found_3210_ == 0 {
                    v___x_3216_ = 0;
                    v___y_3212_ = v___x_3216_;
                    state = 1;
                    continue;
                } else {
                    if lean_obj_tag(v_fst_3207_) == 0 {
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
                v_toPure_3213_ = lean_ctor_get(v_toApplicative_3204_, 1);
                lean_inc(v_toPure_3213_);
                lean_dec_ref(v_toApplicative_3204_);
                lean_inc(v_numCalls_3209_);
                lean_inc_ref(v_cur_3208_);
                v___x_3214_ = lean_alloc_ctor(0, 2, (1) as u32);
                lean_ctor_set(v___x_3214_, 0, v_cur_3208_);
                lean_ctor_set(v___x_3214_, 1, v_numCalls_3209_);
                lean_ctor_set_uint8(
                    v___x_3214_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___y_3212_,
                );
                v___x_3215_ = lean_apply_2(v_toPure_3213_, lean_box(0), v___x_3214_);
                return v___x_3215_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed(
    mut v_toApplicative_3219_: *mut LeanObject,
    mut v_____x_3220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3221_: *mut LeanObject = core::ptr::null_mut();
    v_res_3221_ =
        l_Lean_Util_ParamMinimizer_search___redArg___lam__0(v_toApplicative_3219_, v_____x_3220_);
    lean_dec_ref(v_____x_3220_);
    return v_res_3221_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__1(
    mut v_initialMask_3224_: *mut LeanObject,
    mut v_test_3225_: *mut LeanObject,
    mut v_maxCalls_3226_: *mut LeanObject,
    mut v_inst_3227_: *mut LeanObject,
    mut v_toBind_3228_: *mut LeanObject,
    mut v___f_3229_: *mut LeanObject,
    mut v_toApplicative_3230_: *mut LeanObject,
    mut v_____do__lift_3231_: u8,
) -> *mut LeanObject {
    if v_____do__lift_3231_ == 0 {
        let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3234_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3237_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_toApplicative_3230_);
        lean_inc_ref(v_initialMask_3224_);
        v___x_3232_ = lean_alloc_ctor(0, 3, (0) as u32);
        lean_ctor_set(v___x_3232_, 0, v_initialMask_3224_);
        lean_ctor_set(v___x_3232_, 1, v_test_3225_);
        lean_ctor_set(v___x_3232_, 2, v_maxCalls_3226_);
        v___x_3233_ = l_Lean_Util_ParamMinimizer_search___redArg___lam__1___closed__0;
        v___x_3234_ = lean_unsigned_to_nat(1);
        v___x_3235_ = lean_alloc_ctor(0, 3, (1) as u32);
        lean_ctor_set(v___x_3235_, 0, v_initialMask_3224_);
        lean_ctor_set(v___x_3235_, 1, v___x_3233_);
        lean_ctor_set(v___x_3235_, 2, v___x_3234_);
        lean_ctor_set_uint8(
            v___x_3235_,
            (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
            v_____do__lift_3231_,
        );
        v___x_3236_ =
            l___private_Lean_Util_ParamMinimizer_0__Lean_Util_ParamMinimizer_main___redArg(
                v_inst_3227_,
                v___x_3232_,
                v___x_3235_,
            );
        lean_dec_ref_known(v___x_3232_, 3);
        v___x_3237_ = lean_apply_4(
            v_toBind_3228_,
            lean_box(0),
            lean_box(0),
            v___x_3236_,
            v___f_3229_,
        );
        return v___x_3237_;
    } else {
        let mut v_toPure_3238_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3239_: u8 = 0;
        let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___f_3229_);
        lean_dec(v_toBind_3228_);
        lean_dec_ref(v_inst_3227_);
        lean_dec(v_maxCalls_3226_);
        lean_dec(v_test_3225_);
        v_toPure_3238_ = lean_ctor_get(v_toApplicative_3230_, 1);
        lean_inc(v_toPure_3238_);
        lean_dec_ref(v_toApplicative_3230_);
        v___x_3239_ = 2;
        v___x_3240_ = lean_unsigned_to_nat(1);
        v___x_3241_ = lean_alloc_ctor(0, 2, (1) as u32);
        lean_ctor_set(v___x_3241_, 0, v_initialMask_3224_);
        lean_ctor_set(v___x_3241_, 1, v___x_3240_);
        lean_ctor_set_uint8(
            v___x_3241_,
            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
            v___x_3239_,
        );
        v___x_3242_ = lean_apply_2(v_toPure_3238_, lean_box(0), v___x_3241_);
        return v___x_3242_;
    }
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed(
    mut v_initialMask_3243_: *mut LeanObject,
    mut v_test_3244_: *mut LeanObject,
    mut v_maxCalls_3245_: *mut LeanObject,
    mut v_inst_3246_: *mut LeanObject,
    mut v_toBind_3247_: *mut LeanObject,
    mut v___f_3248_: *mut LeanObject,
    mut v_toApplicative_3249_: *mut LeanObject,
    mut v_____do__lift_3250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_277__boxed_3251_: u8 = 0;
    let mut v_res_3252_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_277__boxed_3251_ = (lean_unbox(v_____do__lift_3250_) as u8);
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
    mut v_inst_3253_: *mut LeanObject,
    mut v_initialMask_3254_: *mut LeanObject,
    mut v_test_3255_: *mut LeanObject,
    mut v_maxCalls_3256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_3257_ = lean_ctor_get(v_inst_3253_, 0);
    lean_inc_ref_n(v_toApplicative_3257_, 2);
    v_toBind_3258_ = lean_ctor_get(v_inst_3253_, 1);
    lean_inc_n(v_toBind_3258_, 2);
    v___f_3259_ = lean_alloc_closure(
        l_Lean_Util_ParamMinimizer_search___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3259_, 0, v_toApplicative_3257_);
    lean_inc(v_test_3255_);
    lean_inc_ref(v_initialMask_3254_);
    v___f_3260_ = lean_alloc_closure(
        l_Lean_Util_ParamMinimizer_search___redArg___lam__1___boxed as *mut core::ffi::c_void,
        8,
        7,
    );
    lean_closure_set(v___f_3260_, 0, v_initialMask_3254_);
    lean_closure_set(v___f_3260_, 1, v_test_3255_);
    lean_closure_set(v___f_3260_, 2, v_maxCalls_3256_);
    lean_closure_set(v___f_3260_, 3, v_inst_3253_);
    lean_closure_set(v___f_3260_, 4, v_toBind_3258_);
    lean_closure_set(v___f_3260_, 5, v___f_3259_);
    lean_closure_set(v___f_3260_, 6, v_toApplicative_3257_);
    v___x_3261_ = lean_apply_1(v_test_3255_, v_initialMask_3254_);
    v___x_3262_ = lean_apply_4(
        v_toBind_3258_,
        lean_box(0),
        lean_box(0),
        v___x_3261_,
        v___f_3260_,
    );
    return v___x_3262_;
}
pub unsafe fn l_Lean_Util_ParamMinimizer_search(
    mut v_m_3263_: *mut LeanObject,
    mut v_inst_3264_: *mut LeanObject,
    mut v_initialMask_3265_: *mut LeanObject,
    mut v_test_3266_: *mut LeanObject,
    mut v_maxCalls_3267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    v___x_3268_ = l_Lean_Util_ParamMinimizer_search___redArg(
        v_inst_3264_,
        v_initialMask_3265_,
        v_test_3266_,
        v_maxCalls_3267_,
    );
    return v___x_3268_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_ParamMinimizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Util_ParamMinimizer_instInhabitedStatus_default =
        _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus_default();
    l_Lean_Util_ParamMinimizer_instInhabitedStatus =
        _init_l_Lean_Util_ParamMinimizer_instInhabitedStatus();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_ParamMinimizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_ParamMinimizer(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_ParamMinimizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Util_ParamMinimizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Util_ParamMinimizer(builtin);
}

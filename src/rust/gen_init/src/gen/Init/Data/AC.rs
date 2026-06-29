// Lean compiler output
// Module: Init.Data.AC
// Imports: Init.GetElem Init.ByCases Init.PropLemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_to_int};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::GetElem::{
    initialize_Init_GetElem, l_List_get_x3fInternal___redArg, runtime_initialize_Init_GetElem,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
pub static l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Data_AC_instInhabitedExpr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__0_value: crate::leanh::LeanStringObject<22> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 22,
        m_capacity: 22,
        m_length: 21,
        m_data: [
            76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 65, 67, 46, 69, 120, 112, 114, 46, 118, 97,
            114, 0,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__1_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__2_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__2_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_AC_instReprExpr_repr___closed__5_value: crate::leanh::LeanStringObject<21> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 21,
        m_capacity: 21,
        m_length: 20,
        m_data: [
            76, 101, 97, 110, 46, 68, 97, 116, 97, 46, 65, 67, 46, 69, 120, 112, 114, 46, 111, 112,
            0,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__6_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value)
                as *mut crate::leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instReprExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Data_AC_instReprExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instBEqExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instBEqExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Data_AC_instBEqExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__0_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__1_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__2_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__0_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__1_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__2_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__3_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
            as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx(
    mut v_x_530_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_530_) == 0 {
        let mut v___x_531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_531_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_531_;
    } else {
        let mut v___x_532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_532_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_532_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx___boxed(
    mut v_x_533_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ = l_Lean_Data_AC_Expr_ctorIdx(v_x_533_);
    crate::leanh::lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___redArg(
    mut v_t_535_: *mut crate::leanh::LeanObject,
    mut v_k_536_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_535_) == 0 {
        let mut v_x_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_537_ = crate::leanh::lean_ctor_get(v_t_535_, 0);
        crate::leanh::lean_inc(v_x_537_);
        crate::leanh::lean_dec_ref_known(v_t_535_, 1);
        v___x_538_ = crate::leanh::lean_apply_1(v_k_536_, v_x_537_);
        return v___x_538_;
    } else {
        let mut v_lhs_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_539_ = crate::leanh::lean_ctor_get(v_t_535_, 0);
        crate::leanh::lean_inc_ref(v_lhs_539_);
        v_rhs_540_ = crate::leanh::lean_ctor_get(v_t_535_, 1);
        crate::leanh::lean_inc_ref(v_rhs_540_);
        crate::leanh::lean_dec_ref_known(v_t_535_, 2);
        v___x_541_ = crate::leanh::lean_apply_2(v_k_536_, v_lhs_539_, v_rhs_540_);
        return v___x_541_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim(
    mut v_motive_542_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_543_: *mut crate::leanh::LeanObject,
    mut v_t_544_: *mut crate::leanh::LeanObject,
    mut v_h_545_: *mut crate::leanh::LeanObject,
    mut v_k_546_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_544_, v_k_546_);
    return v___x_547_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___boxed(
    mut v_motive_548_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_549_: *mut crate::leanh::LeanObject,
    mut v_t_550_: *mut crate::leanh::LeanObject,
    mut v_h_551_: *mut crate::leanh::LeanObject,
    mut v_k_552_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ =
        l_Lean_Data_AC_Expr_ctorElim(v_motive_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
    crate::leanh::lean_dec(v_ctorIdx_549_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim___redArg(
    mut v_t_554_: *mut crate::leanh::LeanObject,
    mut v_var_555_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_554_, v_var_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim(
    mut v_motive_557_: *mut crate::leanh::LeanObject,
    mut v_t_558_: *mut crate::leanh::LeanObject,
    mut v_h_559_: *mut crate::leanh::LeanObject,
    mut v_var_560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_558_, v_var_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim___redArg(
    mut v_t_562_: *mut crate::leanh::LeanObject,
    mut v_op_563_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_562_, v_op_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim(
    mut v_motive_565_: *mut crate::leanh::LeanObject,
    mut v_t_566_: *mut crate::leanh::LeanObject,
    mut v_h_567_: *mut crate::leanh::LeanObject,
    mut v_op_568_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_566_, v_op_568_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__3() -> *mut crate::leanh::LeanObject
{
    let mut v___x_580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_581_ = lean_nat_to_int(v___x_580_);
    return v___x_581_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__4() -> *mut crate::leanh::LeanObject
{
    let mut v___x_582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_583_ = lean_nat_to_int(v___x_582_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Data_AC_instReprExpr_repr(
    mut v_x_590_: *mut crate::leanh::LeanObject,
    mut v_prec_591_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___y_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_612_: u8 = 0;
    let mut v_lhs_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_590_) == 0 {
                    v_x_592_ = crate::leanh::lean_ctor_get(v_x_590_, 0);
                    v_isSharedCheck_612_ = (!crate::leanh::lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_612_ == 0 {
                        v___x_594_ = v_x_590_;
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_x_592_);
                        crate::leanh::lean_dec(v_x_590_);
                        v___x_594_ = crate::leanh::lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_613_ = crate::leanh::lean_ctor_get(v_x_590_, 0);
                    v_rhs_614_ = crate::leanh::lean_ctor_get(v_x_590_, 1);
                    v_isSharedCheck_637_ = (!crate::leanh::lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_637_ == 0 {
                        v___x_616_ = v_x_590_;
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_rhs_614_);
                        crate::leanh::lean_inc(v_lhs_613_);
                        crate::leanh::lean_dec(v_x_590_);
                        v___x_616_ = crate::leanh::lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_608_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_591_);
                if v___x_609_ == 0 {
                    v___x_610_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_597_ = v___x_610_;
                    state = 2;
                    continue;
                } else {
                    v___x_611_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_597_ = v___x_611_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_598_ = l_Lean_Data_AC_instReprExpr_repr___closed__2;
                v___x_599_ = l_Nat_reprFast(v_x_592_);
                if v_isShared_595_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_594_, 3);
                    crate::leanh::lean_ctor_set(v___x_594_, 0, v___x_599_);
                    v___x_601_ = v___x_594_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_607_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
                    v___x_601_ = v_reuseFailAlloc_607_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_602_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_602_, 0, v___x_598_);
                crate::leanh::lean_ctor_set(v___x_602_, 1, v___x_601_);
                crate::leanh::lean_inc(v___y_597_);
                v___x_603_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_603_, 0, v___y_597_);
                crate::leanh::lean_ctor_set(v___x_603_, 1, v___x_602_);
                v___x_604_ = 0;
                v___x_605_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_605_, 0, v___x_603_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_605_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_591_);
                return v___x_606_;
            }
            4 => {
                v___x_618_ = crate::leanh::lean_unsigned_to_nat(1024);
                v___x_634_ = lean_nat_dec_le(v___x_618_, v_prec_591_);
                if v___x_634_ == 0 {
                    v___x_635_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_620_ = v___x_635_;
                    state = 5;
                    continue;
                } else {
                    v___x_636_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_620_ = v___x_636_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_621_ = crate::leanh::lean_box(1);
                v___x_622_ = l_Lean_Data_AC_instReprExpr_repr___closed__7;
                v___x_623_ = l_Lean_Data_AC_instReprExpr_repr(v_lhs_613_, v___x_618_);
                if v_isShared_617_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_616_, 5);
                    crate::leanh::lean_ctor_set(v___x_616_, 1, v___x_623_);
                    crate::leanh::lean_ctor_set(v___x_616_, 0, v___x_622_);
                    v___x_625_ = v___x_616_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_622_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_623_);
                    v___x_625_ = v_reuseFailAlloc_633_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_626_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_626_, 0, v___x_625_);
                crate::leanh::lean_ctor_set(v___x_626_, 1, v___x_621_);
                v___x_627_ = l_Lean_Data_AC_instReprExpr_repr(v_rhs_614_, v___x_618_);
                v___x_628_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_628_, 0, v___x_626_);
                crate::leanh::lean_ctor_set(v___x_628_, 1, v___x_627_);
                crate::leanh::lean_inc(v___y_620_);
                v___x_629_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_629_, 0, v___y_620_);
                crate::leanh::lean_ctor_set(v___x_629_, 1, v___x_628_);
                v___x_630_ = 0;
                v___x_631_ = crate::leanh::lean_alloc_ctor(6, 1, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_631_, 0, v___x_629_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_631_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v___x_630_,
                );
                v___x_632_ = l_Repr_addAppParen(v___x_631_, v_prec_591_);
                return v___x_632_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_instReprExpr_repr___boxed(
    mut v_x_638_: *mut crate::leanh::LeanObject,
    mut v_prec_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Lean_Data_AC_instReprExpr_repr(v_x_638_, v_prec_639_);
    crate::leanh::lean_dec(v_prec_639_);
    return v_res_640_;
}
pub unsafe fn l_Lean_Data_AC_instBEqExpr_beq(
    mut v_x_643_: *mut crate::leanh::LeanObject,
    mut v_x_644_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_x_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v_lhs_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_643_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_644_) == 0 {
                        v_x_645_ = crate::leanh::lean_ctor_get(v_x_643_, 0);
                        v_x_646_ = crate::leanh::lean_ctor_get(v_x_644_, 0);
                        v___x_647_ = lean_nat_dec_eq(v_x_645_, v_x_646_);
                        return v___x_647_;
                    } else {
                        v___x_648_ = 0;
                        return v___x_648_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_644_) == 1 {
                        v_lhs_649_ = crate::leanh::lean_ctor_get(v_x_643_, 0);
                        v_rhs_650_ = crate::leanh::lean_ctor_get(v_x_643_, 1);
                        v_lhs_651_ = crate::leanh::lean_ctor_get(v_x_644_, 0);
                        v_rhs_652_ = crate::leanh::lean_ctor_get(v_x_644_, 1);
                        v___x_653_ = l_Lean_Data_AC_instBEqExpr_beq(v_lhs_649_, v_lhs_651_);
                        if v___x_653_ == 0 {
                            return v___x_653_;
                        } else {
                            v_x_643_ = v_rhs_650_;
                            v_x_644_ = v_rhs_652_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_655_ = 0;
                        return v___x_655_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_instBEqExpr_beq___boxed(
    mut v_x_656_: *mut crate::leanh::LeanObject,
    mut v_x_657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_658_: u8 = 0;
    let mut v_r_659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_656_, v_x_657_);
    crate::leanh::lean_dec_ref(v_x_657_);
    crate::leanh::lean_dec_ref(v_x_656_);
    v_r_659_ = crate::leanh::lean_box((v_res_658_) as usize);
    return v_r_659_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg(
    mut v_ctx_662_: *mut crate::leanh::LeanObject,
    mut v_idx_663_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_vars_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arbitrary_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_vars_664_ = crate::leanh::lean_ctor_get(v_ctx_662_, 3);
    v_arbitrary_665_ = crate::leanh::lean_ctor_get(v_ctx_662_, 4);
    v___x_666_ = l_List_get_x3fInternal___redArg(v_vars_664_, v_idx_663_);
    if crate::leanh::lean_obj_tag(v___x_666_) == 0 {
        let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_667_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_arbitrary_665_);
        v___x_668_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_668_, 0, v_arbitrary_665_);
        crate::leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
        return v___x_668_;
    } else {
        let mut v_val_669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_669_ = crate::leanh::lean_ctor_get(v___x_666_, 0);
        crate::leanh::lean_inc(v_val_669_);
        crate::leanh::lean_dec_ref_known(v___x_666_, 1);
        return v_val_669_;
    }
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg___boxed(
    mut v_ctx_670_: *mut crate::leanh::LeanObject,
    mut v_idx_671_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_670_, v_idx_671_);
    crate::leanh::lean_dec_ref(v_ctx_670_);
    return v_res_672_;
}
pub unsafe fn l_Lean_Data_AC_Context_var(
    mut v_00_u03b1_673_: *mut crate::leanh::LeanObject,
    mut v_ctx_674_: *mut crate::leanh::LeanObject,
    mut v_idx_675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_674_, v_idx_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___boxed(
    mut v_00_u03b1_677_: *mut crate::leanh::LeanObject,
    mut v_ctx_678_: *mut crate::leanh::LeanObject,
    mut v_idx_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_Data_AC_Context_var(v_00_u03b1_677_, v_ctx_678_, v_idx_679_);
    crate::leanh::lean_dec_ref(v_ctx_678_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0(
    mut v_ctx_681_: *mut crate::leanh::LeanObject,
    mut v_x_682_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_681_, v_x_682_);
    v_neutral_684_ = crate::leanh::lean_ctor_get(v___x_683_, 1);
    crate::leanh::lean_inc(v_neutral_684_);
    crate::leanh::lean_dec_ref(v___x_683_);
    if crate::leanh::lean_obj_tag(v_neutral_684_) == 0 {
        let mut v___x_685_: u8 = 0;
        v___x_685_ = 0;
        return v___x_685_;
    } else {
        let mut v___x_686_: u8 = 0;
        crate::leanh::lean_dec_ref_known(v_neutral_684_, 1);
        v___x_686_ = 1;
        return v___x_686_;
    }
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0___boxed(
    mut v_ctx_687_: *mut crate::leanh::LeanObject,
    mut v_x_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_689_: u8 = 0;
    let mut v_r_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Lean_Data_AC_instContextInformationContext___lam__0(v_ctx_687_, v_x_688_);
    crate::leanh::lean_dec_ref(v_ctx_687_);
    v_r_690_ = crate::leanh::lean_box((v_res_689_) as usize);
    return v_r_690_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__1(
    mut v_ctx_691_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_comm_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_comm_692_ = crate::leanh::lean_ctor_get(v_ctx_691_, 1);
    if crate::leanh::lean_obj_tag(v_comm_692_) == 0 {
        let mut v___x_693_: u8 = 0;
        v___x_693_ = 0;
        return v___x_693_;
    } else {
        let mut v___x_694_: u8 = 0;
        v___x_694_ = 1;
        return v___x_694_;
    }
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__1___boxed(
    mut v_ctx_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_696_: u8 = 0;
    let mut v_r_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Data_AC_instContextInformationContext___lam__1(v_ctx_695_);
    crate::leanh::lean_dec_ref(v_ctx_695_);
    v_r_697_ = crate::leanh::lean_box((v_res_696_) as usize);
    return v_r_697_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__2(
    mut v_ctx_698_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_idem_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_idem_699_ = crate::leanh::lean_ctor_get(v_ctx_698_, 2);
    if crate::leanh::lean_obj_tag(v_idem_699_) == 0 {
        let mut v___x_700_: u8 = 0;
        v___x_700_ = 0;
        return v___x_700_;
    } else {
        let mut v___x_701_: u8 = 0;
        v___x_701_ = 1;
        return v___x_701_;
    }
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__2___boxed(
    mut v_ctx_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: u8 = 0;
    let mut v_r_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lean_Data_AC_instContextInformationContext___lam__2(v_ctx_702_);
    crate::leanh::lean_dec_ref(v_ctx_702_);
    v_r_704_ = crate::leanh::lean_box((v_res_703_) as usize);
    return v_r_704_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext(
    mut v_00_u03b1_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_Data_AC_instContextInformationContext___closed__3;
    return v___x_713_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0(
    mut v_ctx_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_arbitrary_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_arbitrary_715_ = crate::leanh::lean_ctor_get(v_ctx_714_, 4);
    crate::leanh::lean_inc(v_arbitrary_715_);
    return v_arbitrary_715_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed(
    mut v_ctx_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Data_AC_instEvalInformationContext___lam__0(v_ctx_716_);
    crate::leanh::lean_dec_ref(v_ctx_716_);
    return v_res_717_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__1(
    mut v_ctx_718_: *mut crate::leanh::LeanObject,
    mut v___y_719_: *mut crate::leanh::LeanObject,
    mut v___y_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_op_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_op_721_ = crate::leanh::lean_ctor_get(v_ctx_718_, 0);
    crate::leanh::lean_inc(v_op_721_);
    crate::leanh::lean_dec_ref(v_ctx_718_);
    v___x_722_ = crate::leanh::lean_apply_2(v_op_721_, v___y_719_, v___y_720_);
    return v___x_722_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2(
    mut v_ctx_723_: *mut crate::leanh::LeanObject,
    mut v_idx_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_723_, v_idx_724_);
    v_value_726_ = crate::leanh::lean_ctor_get(v___x_725_, 0);
    crate::leanh::lean_inc(v_value_726_);
    crate::leanh::lean_dec_ref(v___x_725_);
    return v_value_726_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed(
    mut v_ctx_727_: *mut crate::leanh::LeanObject,
    mut v_idx_728_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Data_AC_instEvalInformationContext___lam__2(v_ctx_727_, v_idx_728_);
    crate::leanh::lean_dec_ref(v_ctx_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext(
    mut v_00_u03b1_737_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_Data_AC_instEvalInformationContext___closed__3;
    return v___x_738_;
}
pub unsafe fn l_Lean_Data_AC_eval___redArg(
    mut v_inst_739_: *mut crate::leanh::LeanObject,
    mut v_ctx_740_: *mut crate::leanh::LeanObject,
    mut v_x_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_741_) == 0 {
        let mut v_x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_evalVar_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_742_ = crate::leanh::lean_ctor_get(v_x_741_, 0);
        crate::leanh::lean_inc(v_x_742_);
        crate::leanh::lean_dec_ref_known(v_x_741_, 1);
        v_evalVar_743_ = crate::leanh::lean_ctor_get(v_inst_739_, 2);
        crate::leanh::lean_inc(v_evalVar_743_);
        crate::leanh::lean_dec_ref(v_inst_739_);
        v___x_744_ = crate::leanh::lean_apply_2(v_evalVar_743_, v_ctx_740_, v_x_742_);
        return v___x_744_;
    } else {
        let mut v_lhs_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_evalOp_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_745_ = crate::leanh::lean_ctor_get(v_x_741_, 0);
        crate::leanh::lean_inc_ref(v_lhs_745_);
        v_rhs_746_ = crate::leanh::lean_ctor_get(v_x_741_, 1);
        crate::leanh::lean_inc_ref(v_rhs_746_);
        crate::leanh::lean_dec_ref_known(v_x_741_, 2);
        v_evalOp_747_ = crate::leanh::lean_ctor_get(v_inst_739_, 1);
        crate::leanh::lean_inc(v_evalOp_747_);
        crate::leanh::lean_inc_n(v_ctx_740_, 2);
        crate::leanh::lean_inc_ref(v_inst_739_);
        v___x_748_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_lhs_745_);
        v___x_749_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_rhs_746_);
        v___x_750_ = crate::leanh::lean_apply_3(v_evalOp_747_, v_ctx_740_, v___x_748_, v___x_749_);
        return v___x_750_;
    }
}
pub unsafe fn l_Lean_Data_AC_eval(
    mut v_00_u03b1_751_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_752_: *mut crate::leanh::LeanObject,
    mut v_inst_753_: *mut crate::leanh::LeanObject,
    mut v_ctx_754_: *mut crate::leanh::LeanObject,
    mut v_x_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = l_Lean_Data_AC_eval___redArg(v_inst_753_, v_ctx_754_, v_x_755_);
    return v___x_756_;
}
pub unsafe fn l_Lean_Data_AC_Expr_toList(
    mut v_x_757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_757_) == 0 {
        let mut v_x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_x_758_ = crate::leanh::lean_ctor_get(v_x_757_, 0);
        v___x_759_ = crate::leanh::lean_box(0);
        crate::leanh::lean_inc(v_x_758_);
        v___x_760_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_760_, 0, v_x_758_);
        crate::leanh::lean_ctor_set(v___x_760_, 1, v___x_759_);
        return v___x_760_;
    } else {
        let mut v_lhs_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_lhs_761_ = crate::leanh::lean_ctor_get(v_x_757_, 0);
        v_rhs_762_ = crate::leanh::lean_ctor_get(v_x_757_, 1);
        v___x_763_ = l_Lean_Data_AC_Expr_toList(v_lhs_761_);
        v___x_764_ = l_Lean_Data_AC_Expr_toList(v_rhs_762_);
        v___x_765_ = l_List_appendTR___redArg(v___x_763_, v___x_764_);
        return v___x_765_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_toList___boxed(
    mut v_x_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lean_Data_AC_Expr_toList(v_x_766_);
    crate::leanh::lean_dec_ref(v_x_766_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Data_AC_evalList___redArg(
    mut v_inst_768_: *mut crate::leanh::LeanObject,
    mut v_ctx_769_: *mut crate::leanh::LeanObject,
    mut v_x_770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_770_) == 0 {
        let mut v_arbitrary_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_arbitrary_771_ = crate::leanh::lean_ctor_get(v_inst_768_, 0);
        crate::leanh::lean_inc(v_arbitrary_771_);
        crate::leanh::lean_dec_ref(v_inst_768_);
        v___x_772_ = crate::leanh::lean_apply_1(v_arbitrary_771_, v_ctx_769_);
        return v___x_772_;
    } else {
        let mut v_tail_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_773_ = crate::leanh::lean_ctor_get(v_x_770_, 1);
        if crate::leanh::lean_obj_tag(v_tail_773_) == 0 {
            let mut v_head_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalVar_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_head_774_ = crate::leanh::lean_ctor_get(v_x_770_, 0);
            crate::leanh::lean_inc(v_head_774_);
            crate::leanh::lean_dec_ref_known(v_x_770_, 2);
            v_evalVar_775_ = crate::leanh::lean_ctor_get(v_inst_768_, 2);
            crate::leanh::lean_inc(v_evalVar_775_);
            crate::leanh::lean_dec_ref(v_inst_768_);
            v___x_776_ = crate::leanh::lean_apply_2(v_evalVar_775_, v_ctx_769_, v_head_774_);
            return v___x_776_;
        } else {
            let mut v_head_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalOp_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalVar_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_773_);
            v_head_777_ = crate::leanh::lean_ctor_get(v_x_770_, 0);
            crate::leanh::lean_inc(v_head_777_);
            crate::leanh::lean_dec_ref_known(v_x_770_, 2);
            v_evalOp_778_ = crate::leanh::lean_ctor_get(v_inst_768_, 1);
            crate::leanh::lean_inc(v_evalOp_778_);
            v_evalVar_779_ = crate::leanh::lean_ctor_get(v_inst_768_, 2);
            crate::leanh::lean_inc(v_evalVar_779_);
            crate::leanh::lean_inc_n(v_ctx_769_, 2);
            v___x_780_ = crate::leanh::lean_apply_2(v_evalVar_779_, v_ctx_769_, v_head_777_);
            v___x_781_ = l_Lean_Data_AC_evalList___redArg(v_inst_768_, v_ctx_769_, v_tail_773_);
            v___x_782_ =
                crate::leanh::lean_apply_3(v_evalOp_778_, v_ctx_769_, v___x_780_, v___x_781_);
            return v___x_782_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_evalList(
    mut v_00_u03b1_783_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_784_: *mut crate::leanh::LeanObject,
    mut v_inst_785_: *mut crate::leanh::LeanObject,
    mut v_ctx_786_: *mut crate::leanh::LeanObject,
    mut v_x_787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_Data_AC_evalList___redArg(v_inst_785_, v_ctx_786_, v_x_787_);
    return v___x_788_;
}
pub unsafe fn l_Lean_Data_AC_insert(
    mut v_x_789_: *mut crate::leanh::LeanObject,
    mut v_x_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_797_: u8 = 0;
    let mut v___x_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_802_: u8 = 0;
    let mut v_unused_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_790_) == 0 {
                    v___x_791_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_791_, 0, v_x_789_);
                    crate::leanh::lean_ctor_set(v___x_791_, 1, v_x_790_);
                    return v___x_791_;
                } else {
                    v_head_792_ = crate::leanh::lean_ctor_get(v_x_790_, 0);
                    v_tail_793_ = crate::leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_794_ = lean_nat_dec_lt(v_x_789_, v_head_792_);
                    if v___x_794_ == 0 {
                        crate::leanh::lean_inc(v_tail_793_);
                        crate::leanh::lean_inc(v_head_792_);
                        v_isSharedCheck_802_ = (!crate::leanh::lean_is_exclusive(v_x_790_)) as u8;
                        if v_isSharedCheck_802_ == 0 {
                            v_unused_803_ = crate::leanh::lean_ctor_get(v_x_790_, 1);
                            crate::leanh::lean_dec(v_unused_803_);
                            v_unused_804_ = crate::leanh::lean_ctor_get(v_x_790_, 0);
                            crate::leanh::lean_dec(v_unused_804_);
                            v___x_796_ = v_x_790_;
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_790_);
                            v___x_796_ = crate::leanh::lean_box(0);
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_805_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_805_, 0, v_x_789_);
                        crate::leanh::lean_ctor_set(v___x_805_, 1, v_x_790_);
                        return v___x_805_;
                    }
                }
            }
            1 => {
                v___x_798_ = l_Lean_Data_AC_insert(v_x_789_, v_tail_793_);
                if v_isShared_797_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_796_, 1, v___x_798_);
                    v___x_800_ = v___x_796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_801_, 0, v_head_792_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
                    v___x_800_ = v_reuseFailAlloc_801_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_sort_loop(
    mut v_a_806_: *mut crate::leanh::LeanObject,
    mut v_a_807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_807_) == 0 {
                    return v_a_806_;
                } else {
                    v_head_808_ = crate::leanh::lean_ctor_get(v_a_807_, 0);
                    crate::leanh::lean_inc(v_head_808_);
                    v_tail_809_ = crate::leanh::lean_ctor_get(v_a_807_, 1);
                    crate::leanh::lean_inc(v_tail_809_);
                    crate::leanh::lean_dec_ref_known(v_a_807_, 2);
                    v___x_810_ = l_Lean_Data_AC_insert(v_head_808_, v_a_806_);
                    v_a_806_ = v___x_810_;
                    v_a_807_ = v_tail_809_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_sort(
    mut v_xs_812_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = crate::leanh::lean_box(0);
    v___x_814_ = l_Lean_Data_AC_sort_loop(v___x_813_, v_xs_812_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Data_AC_mergeIdem_loop(
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_a_816_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_816_) == 0 {
                    v___x_817_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_817_, 0, v_a_815_);
                    crate::leanh::lean_ctor_set(v___x_817_, 1, v_a_816_);
                    return v___x_817_;
                } else {
                    v_head_818_ = crate::leanh::lean_ctor_get(v_a_816_, 0);
                    v_tail_819_ = crate::leanh::lean_ctor_get(v_a_816_, 1);
                    v_isSharedCheck_829_ = (!crate::leanh::lean_is_exclusive(v_a_816_)) as u8;
                    if v_isSharedCheck_829_ == 0 {
                        v___x_821_ = v_a_816_;
                        v_isShared_822_ = v_isSharedCheck_829_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_819_);
                        crate::leanh::lean_inc(v_head_818_);
                        crate::leanh::lean_dec(v_a_816_);
                        v___x_821_ = crate::leanh::lean_box(0);
                        v_isShared_822_ = v_isSharedCheck_829_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_823_ = lean_nat_dec_eq(v_a_815_, v_head_818_);
                if v___x_823_ == 0 {
                    v___x_824_ = l_Lean_Data_AC_mergeIdem_loop(v_head_818_, v_tail_819_);
                    if v_isShared_822_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_821_, 1, v___x_824_);
                        crate::leanh::lean_ctor_set(v___x_821_, 0, v_a_815_);
                        v___x_826_ = v___x_821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_827_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_815_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
                        v___x_826_ = v_reuseFailAlloc_827_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_821_);
                    crate::leanh::lean_dec(v_head_818_);
                    v_a_816_ = v_tail_819_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_826_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_mergeIdem(
    mut v_xs_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_xs_830_) == 0 {
        return v_xs_830_;
    } else {
        let mut v_head_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_831_ = crate::leanh::lean_ctor_get(v_xs_830_, 0);
        crate::leanh::lean_inc(v_head_831_);
        v_tail_832_ = crate::leanh::lean_ctor_get(v_xs_830_, 1);
        crate::leanh::lean_inc(v_tail_832_);
        crate::leanh::lean_dec_ref_known(v_xs_830_, 2);
        v___x_833_ = l_Lean_Data_AC_mergeIdem_loop(v_head_831_, v_tail_832_);
        return v___x_833_;
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop___redArg(
    mut v_info_834_: *mut crate::leanh::LeanObject,
    mut v_ctx_835_: *mut crate::leanh::LeanObject,
    mut v_a_836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v_isNeutral_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_836_) == 0 {
                    crate::leanh::lean_dec(v_ctx_835_);
                    crate::leanh::lean_dec_ref(v_info_834_);
                    return v_a_836_;
                } else {
                    v_head_837_ = crate::leanh::lean_ctor_get(v_a_836_, 0);
                    v_tail_838_ = crate::leanh::lean_ctor_get(v_a_836_, 1);
                    v_isSharedCheck_850_ = (!crate::leanh::lean_is_exclusive(v_a_836_)) as u8;
                    if v_isSharedCheck_850_ == 0 {
                        v___x_840_ = v_a_836_;
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_838_);
                        crate::leanh::lean_inc(v_head_837_);
                        crate::leanh::lean_dec(v_a_836_);
                        v___x_840_ = crate::leanh::lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_isNeutral_842_ = crate::leanh::lean_ctor_get(v_info_834_, 0);
                crate::leanh::lean_inc_ref(v_isNeutral_842_);
                crate::leanh::lean_inc(v_head_837_);
                crate::leanh::lean_inc(v_ctx_835_);
                v___x_843_ = crate::leanh::lean_apply_2(v_isNeutral_842_, v_ctx_835_, v_head_837_);
                v___x_844_ = (crate::leanh::lean_unbox(v___x_843_) as u8);
                if v___x_844_ == 0 {
                    v___x_845_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(
                        v_info_834_,
                        v_ctx_835_,
                        v_tail_838_,
                    );
                    if v_isShared_841_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_840_, 1, v___x_845_);
                        v___x_847_ = v___x_840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 0, v_head_837_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
                        v___x_847_ = v_reuseFailAlloc_848_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_840_);
                    crate::leanh::lean_dec(v_head_837_);
                    v_a_836_ = v_tail_838_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                return v___x_847_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop(
    mut v_00_u03b1_851_: *mut crate::leanh::LeanObject,
    mut v_info_852_: *mut crate::leanh::LeanObject,
    mut v_ctx_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_852_, v_ctx_853_, v_a_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals___redArg(
    mut v_info_856_: *mut crate::leanh::LeanObject,
    mut v_ctx_857_: *mut crate::leanh::LeanObject,
    mut v_x_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_858_) == 0 {
        crate::leanh::lean_dec(v_ctx_857_);
        crate::leanh::lean_dec_ref(v_info_856_);
        return v_x_858_;
    } else {
        let mut v_head_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_859_ = crate::leanh::lean_ctor_get(v_x_858_, 0);
        crate::leanh::lean_inc(v_head_859_);
        v___x_860_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_856_, v_ctx_857_, v_x_858_);
        if crate::leanh::lean_obj_tag(v___x_860_) == 0 {
            let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_861_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_861_, 0, v_head_859_);
            crate::leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
            return v___x_861_;
        } else {
            crate::leanh::lean_dec(v_head_859_);
            return v___x_860_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals(
    mut v_00_u03b1_862_: *mut crate::leanh::LeanObject,
    mut v_info_863_: *mut crate::leanh::LeanObject,
    mut v_ctx_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_863_, v_ctx_864_, v_x_865_);
    return v___x_866_;
}
pub unsafe fn l_Lean_Data_AC_norm___redArg(
    mut v_info_867_: *mut crate::leanh::LeanObject,
    mut v_ctx_868_: *mut crate::leanh::LeanObject,
    mut v_e_869_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isComm_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIdem_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isComm_870_ = crate::leanh::lean_ctor_get(v_info_867_, 1);
                crate::leanh::lean_inc_ref(v_isComm_870_);
                v_isIdem_871_ = crate::leanh::lean_ctor_get(v_info_867_, 2);
                crate::leanh::lean_inc_ref(v_isIdem_871_);
                v_xs_877_ = l_Lean_Data_AC_Expr_toList(v_e_869_);
                crate::leanh::lean_inc_n(v_ctx_868_, 2);
                v_xs_878_ =
                    l_Lean_Data_AC_removeNeutrals___redArg(v_info_867_, v_ctx_868_, v_xs_877_);
                v___x_879_ = crate::leanh::lean_apply_1(v_isComm_870_, v_ctx_868_);
                v___x_880_ = (crate::leanh::lean_unbox(v___x_879_) as u8);
                if v___x_880_ == 0 {
                    v___y_873_ = v_xs_878_;
                    state = 1;
                    continue;
                } else {
                    v___x_881_ = l_Lean_Data_AC_sort(v_xs_878_);
                    v___y_873_ = v___x_881_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_874_ = crate::leanh::lean_apply_1(v_isIdem_871_, v_ctx_868_);
                v___x_875_ = (crate::leanh::lean_unbox(v___x_874_) as u8);
                if v___x_875_ == 0 {
                    return v___y_873_;
                } else {
                    v___x_876_ = l_Lean_Data_AC_mergeIdem(v___y_873_);
                    return v___x_876_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Data_AC_norm___redArg___boxed(
    mut v_info_882_: *mut crate::leanh::LeanObject,
    mut v_ctx_883_: *mut crate::leanh::LeanObject,
    mut v_e_884_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_Data_AC_norm___redArg(v_info_882_, v_ctx_883_, v_e_884_);
    crate::leanh::lean_dec_ref(v_e_884_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Data_AC_norm(
    mut v_00_u03b1_886_: *mut crate::leanh::LeanObject,
    mut v_info_887_: *mut crate::leanh::LeanObject,
    mut v_ctx_888_: *mut crate::leanh::LeanObject,
    mut v_e_889_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Lean_Data_AC_norm___redArg(v_info_887_, v_ctx_888_, v_e_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Data_AC_norm___boxed(
    mut v_00_u03b1_891_: *mut crate::leanh::LeanObject,
    mut v_info_892_: *mut crate::leanh::LeanObject,
    mut v_ctx_893_: *mut crate::leanh::LeanObject,
    mut v_e_894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lean_Data_AC_norm(v_00_u03b1_891_, v_info_892_, v_ctx_893_, v_e_894_);
    crate::leanh::lean_dec_ref(v_e_894_);
    return v_res_895_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(
    mut v_x_896_: *mut crate::leanh::LeanObject,
    mut v_h__1_897_: *mut crate::leanh::LeanObject,
    mut v_h__2_898_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_896_) == 0 {
        let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_898_);
        v___x_899_ = crate::leanh::lean_box(0);
        v___x_900_ = crate::leanh::lean_apply_1(v_h__1_897_, v___x_899_);
        return v___x_900_;
    } else {
        let mut v_head_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_897_);
        v_head_901_ = crate::leanh::lean_ctor_get(v_x_896_, 0);
        crate::leanh::lean_inc(v_head_901_);
        v_tail_902_ = crate::leanh::lean_ctor_get(v_x_896_, 1);
        crate::leanh::lean_inc(v_tail_902_);
        crate::leanh::lean_dec_ref_known(v_x_896_, 2);
        v___x_903_ = crate::leanh::lean_apply_2(v_h__2_898_, v_head_901_, v_tail_902_);
        return v___x_903_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(
    mut v_motive_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
    mut v_h__1_906_: *mut crate::leanh::LeanObject,
    mut v_h__2_907_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_905_) == 0 {
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_907_);
        v___x_908_ = crate::leanh::lean_box(0);
        v___x_909_ = crate::leanh::lean_apply_1(v_h__1_906_, v___x_908_);
        return v___x_909_;
    } else {
        let mut v_head_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_906_);
        v_head_910_ = crate::leanh::lean_ctor_get(v_x_905_, 0);
        crate::leanh::lean_inc(v_head_910_);
        v_tail_911_ = crate::leanh::lean_ctor_get(v_x_905_, 1);
        crate::leanh::lean_inc(v_tail_911_);
        crate::leanh::lean_dec_ref_known(v_x_905_, 2);
        v___x_912_ = crate::leanh::lean_apply_2(v_h__2_907_, v_head_910_, v_tail_911_);
        return v___x_912_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(
    mut v_x_913_: *mut crate::leanh::LeanObject,
    mut v_x_914_: *mut crate::leanh::LeanObject,
    mut v_h__1_915_: *mut crate::leanh::LeanObject,
    mut v_h__2_916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_914_) == 0 {
        let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_915_);
        v___x_917_ = crate::leanh::lean_apply_1(v_h__2_916_, v_x_913_);
        return v___x_917_;
    } else {
        let mut v_head_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_916_);
        v_head_918_ = crate::leanh::lean_ctor_get(v_x_914_, 0);
        crate::leanh::lean_inc(v_head_918_);
        v_tail_919_ = crate::leanh::lean_ctor_get(v_x_914_, 1);
        crate::leanh::lean_inc(v_tail_919_);
        crate::leanh::lean_dec_ref_known(v_x_914_, 2);
        v___x_920_ = crate::leanh::lean_apply_3(v_h__1_915_, v_x_913_, v_head_918_, v_tail_919_);
        return v___x_920_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(
    mut v_motive_921_: *mut crate::leanh::LeanObject,
    mut v_x_922_: *mut crate::leanh::LeanObject,
    mut v_x_923_: *mut crate::leanh::LeanObject,
    mut v_h__1_924_: *mut crate::leanh::LeanObject,
    mut v_h__2_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_923_) == 0 {
        let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_924_);
        v___x_926_ = crate::leanh::lean_apply_1(v_h__2_925_, v_x_922_);
        return v___x_926_;
    } else {
        let mut v_head_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_925_);
        v_head_927_ = crate::leanh::lean_ctor_get(v_x_923_, 0);
        crate::leanh::lean_inc(v_head_927_);
        v_tail_928_ = crate::leanh::lean_ctor_get(v_x_923_, 1);
        crate::leanh::lean_inc(v_tail_928_);
        crate::leanh::lean_dec_ref_known(v_x_923_, 2);
        v___x_929_ = crate::leanh::lean_apply_3(v_h__1_924_, v_x_922_, v_head_927_, v_tail_928_);
        return v___x_929_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_930_: *mut crate::leanh::LeanObject,
    mut v_h__1_931_: *mut crate::leanh::LeanObject,
    mut v_h__2_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_930_) == 0 {
        let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_931_);
        v___x_933_ = crate::leanh::lean_box(0);
        v___x_934_ = crate::leanh::lean_apply_1(v_h__2_932_, v___x_933_);
        return v___x_934_;
    } else {
        let mut v_val_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_932_);
        v_val_935_ = crate::leanh::lean_ctor_get(v_x_930_, 0);
        crate::leanh::lean_inc(v_val_935_);
        crate::leanh::lean_dec_ref_known(v_x_930_, 1);
        v___x_936_ = crate::leanh::lean_apply_1(v_h__1_931_, v_val_935_);
        return v___x_936_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_937_: *mut crate::leanh::LeanObject,
    mut v_motive_938_: *mut crate::leanh::LeanObject,
    mut v_x_939_: *mut crate::leanh::LeanObject,
    mut v_h__1_940_: *mut crate::leanh::LeanObject,
    mut v_h__2_941_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_939_) == 0 {
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_940_);
        v___x_942_ = crate::leanh::lean_box(0);
        v___x_943_ = crate::leanh::lean_apply_1(v_h__2_941_, v___x_942_);
        return v___x_943_;
    } else {
        let mut v_val_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_941_);
        v_val_944_ = crate::leanh::lean_ctor_get(v_x_939_, 0);
        crate::leanh::lean_inc(v_val_944_);
        crate::leanh::lean_dec_ref_known(v_x_939_, 1);
        v___x_945_ = crate::leanh::lean_apply_1(v_h__1_940_, v_val_944_);
        return v___x_945_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(
    mut v_x_946_: *mut crate::leanh::LeanObject,
    mut v_h__1_947_: *mut crate::leanh::LeanObject,
    mut v_h__2_948_: *mut crate::leanh::LeanObject,
    mut v_h__3_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_946_) == 0 {
        let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_949_);
        crate::leanh::lean_dec(v_h__2_948_);
        v___x_950_ = crate::leanh::lean_box(0);
        v___x_951_ = crate::leanh::lean_apply_1(v_h__1_947_, v___x_950_);
        return v___x_951_;
    } else {
        let mut v_tail_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_947_);
        v_tail_952_ = crate::leanh::lean_ctor_get(v_x_946_, 1);
        if crate::leanh::lean_obj_tag(v_tail_952_) == 0 {
            let mut v_head_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_949_);
            v_head_953_ = crate::leanh::lean_ctor_get(v_x_946_, 0);
            crate::leanh::lean_inc(v_head_953_);
            crate::leanh::lean_dec_ref_known(v_x_946_, 2);
            v___x_954_ = crate::leanh::lean_apply_1(v_h__2_948_, v_head_953_);
            return v___x_954_;
        } else {
            let mut v_head_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_952_);
            crate::leanh::lean_dec(v_h__2_948_);
            v_head_955_ = crate::leanh::lean_ctor_get(v_x_946_, 0);
            crate::leanh::lean_inc(v_head_955_);
            crate::leanh::lean_dec_ref_known(v_x_946_, 2);
            v___x_956_ = crate::leanh::lean_apply_3(
                v_h__3_949_,
                v_head_955_,
                v_tail_952_,
                crate::leanh::lean_box(0),
            );
            return v___x_956_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(
    mut v_motive_957_: *mut crate::leanh::LeanObject,
    mut v_x_958_: *mut crate::leanh::LeanObject,
    mut v_h__1_959_: *mut crate::leanh::LeanObject,
    mut v_h__2_960_: *mut crate::leanh::LeanObject,
    mut v_h__3_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_958_) == 0 {
        let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_961_);
        crate::leanh::lean_dec(v_h__2_960_);
        v___x_962_ = crate::leanh::lean_box(0);
        v___x_963_ = crate::leanh::lean_apply_1(v_h__1_959_, v___x_962_);
        return v___x_963_;
    } else {
        let mut v_tail_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_959_);
        v_tail_964_ = crate::leanh::lean_ctor_get(v_x_958_, 1);
        if crate::leanh::lean_obj_tag(v_tail_964_) == 0 {
            let mut v_head_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_961_);
            v_head_965_ = crate::leanh::lean_ctor_get(v_x_958_, 0);
            crate::leanh::lean_inc(v_head_965_);
            crate::leanh::lean_dec_ref_known(v_x_958_, 2);
            v___x_966_ = crate::leanh::lean_apply_1(v_h__2_960_, v_head_965_);
            return v___x_966_;
        } else {
            let mut v_head_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_tail_964_);
            crate::leanh::lean_dec(v_h__2_960_);
            v_head_967_ = crate::leanh::lean_ctor_get(v_x_958_, 0);
            crate::leanh::lean_inc(v_head_967_);
            crate::leanh::lean_dec_ref_known(v_x_958_, 2);
            v___x_968_ = crate::leanh::lean_apply_3(
                v_h__3_961_,
                v_head_967_,
                v_tail_964_,
                crate::leanh::lean_box(0),
            );
            return v___x_968_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(
    mut v_x_969_: *mut crate::leanh::LeanObject,
    mut v_x_970_: *mut crate::leanh::LeanObject,
    mut v_h__1_971_: *mut crate::leanh::LeanObject,
    mut v_h__2_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_970_) == 0 {
        let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_972_);
        v___x_973_ = crate::leanh::lean_apply_1(v_h__1_971_, v_x_969_);
        return v___x_973_;
    } else {
        let mut v_head_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_971_);
        v_head_974_ = crate::leanh::lean_ctor_get(v_x_970_, 0);
        crate::leanh::lean_inc(v_head_974_);
        v_tail_975_ = crate::leanh::lean_ctor_get(v_x_970_, 1);
        crate::leanh::lean_inc(v_tail_975_);
        crate::leanh::lean_dec_ref_known(v_x_970_, 2);
        v___x_976_ = crate::leanh::lean_apply_3(v_h__2_972_, v_x_969_, v_head_974_, v_tail_975_);
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(
    mut v_motive_977_: *mut crate::leanh::LeanObject,
    mut v_x_978_: *mut crate::leanh::LeanObject,
    mut v_x_979_: *mut crate::leanh::LeanObject,
    mut v_h__1_980_: *mut crate::leanh::LeanObject,
    mut v_h__2_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_979_) == 0 {
        let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_981_);
        v___x_982_ = crate::leanh::lean_apply_1(v_h__1_980_, v_x_978_);
        return v___x_982_;
    } else {
        let mut v_head_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_980_);
        v_head_983_ = crate::leanh::lean_ctor_get(v_x_979_, 0);
        crate::leanh::lean_inc(v_head_983_);
        v_tail_984_ = crate::leanh::lean_ctor_get(v_x_979_, 1);
        crate::leanh::lean_inc(v_tail_984_);
        crate::leanh::lean_dec_ref_known(v_x_979_, 2);
        v___x_985_ = crate::leanh::lean_apply_3(v_h__2_981_, v_x_978_, v_head_983_, v_tail_984_);
        return v___x_985_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(
    mut v_x_986_: *mut crate::leanh::LeanObject,
    mut v_h__1_987_: *mut crate::leanh::LeanObject,
    mut v_h__2_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_986_) == 0 {
        let mut v_x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_988_);
        v_x_989_ = crate::leanh::lean_ctor_get(v_x_986_, 0);
        crate::leanh::lean_inc(v_x_989_);
        crate::leanh::lean_dec_ref_known(v_x_986_, 1);
        v___x_990_ = crate::leanh::lean_apply_1(v_h__1_987_, v_x_989_);
        return v___x_990_;
    } else {
        let mut v_lhs_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_987_);
        v_lhs_991_ = crate::leanh::lean_ctor_get(v_x_986_, 0);
        crate::leanh::lean_inc_ref(v_lhs_991_);
        v_rhs_992_ = crate::leanh::lean_ctor_get(v_x_986_, 1);
        crate::leanh::lean_inc_ref(v_rhs_992_);
        crate::leanh::lean_dec_ref_known(v_x_986_, 2);
        v___x_993_ = crate::leanh::lean_apply_2(v_h__2_988_, v_lhs_991_, v_rhs_992_);
        return v___x_993_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(
    mut v_motive_994_: *mut crate::leanh::LeanObject,
    mut v_x_995_: *mut crate::leanh::LeanObject,
    mut v_h__1_996_: *mut crate::leanh::LeanObject,
    mut v_h__2_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_995_) == 0 {
        let mut v_x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_997_);
        v_x_998_ = crate::leanh::lean_ctor_get(v_x_995_, 0);
        crate::leanh::lean_inc(v_x_998_);
        crate::leanh::lean_dec_ref_known(v_x_995_, 1);
        v___x_999_ = crate::leanh::lean_apply_1(v_h__1_996_, v_x_998_);
        return v___x_999_;
    } else {
        let mut v_lhs_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_996_);
        v_lhs_1000_ = crate::leanh::lean_ctor_get(v_x_995_, 0);
        crate::leanh::lean_inc_ref(v_lhs_1000_);
        v_rhs_1001_ = crate::leanh::lean_ctor_get(v_x_995_, 1);
        crate::leanh::lean_inc_ref(v_rhs_1001_);
        crate::leanh::lean_dec_ref_known(v_x_995_, 2);
        v___x_1002_ = crate::leanh::lean_apply_2(v_h__2_997_, v_lhs_1000_, v_rhs_1001_);
        return v___x_1002_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(
    mut v_x_1003_: *mut crate::leanh::LeanObject,
    mut v_h__1_1004_: *mut crate::leanh::LeanObject,
    mut v_h__2_1005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1003_) == 0 {
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1004_);
        v___x_1006_ = crate::leanh::lean_box(0);
        v___x_1007_ = crate::leanh::lean_apply_1(v_h__2_1005_, v___x_1006_);
        return v___x_1007_;
    } else {
        let mut v_head_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1005_);
        v_head_1008_ = crate::leanh::lean_ctor_get(v_x_1003_, 0);
        crate::leanh::lean_inc(v_head_1008_);
        v_tail_1009_ = crate::leanh::lean_ctor_get(v_x_1003_, 1);
        crate::leanh::lean_inc(v_tail_1009_);
        crate::leanh::lean_dec_ref_known(v_x_1003_, 2);
        v___x_1010_ = crate::leanh::lean_apply_2(v_h__1_1004_, v_head_1008_, v_tail_1009_);
        return v___x_1010_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(
    mut v_motive_1011_: *mut crate::leanh::LeanObject,
    mut v_x_1012_: *mut crate::leanh::LeanObject,
    mut v_h__1_1013_: *mut crate::leanh::LeanObject,
    mut v_h__2_1014_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1012_) == 0 {
        let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1013_);
        v___x_1015_ = crate::leanh::lean_box(0);
        v___x_1016_ = crate::leanh::lean_apply_1(v_h__2_1014_, v___x_1015_);
        return v___x_1016_;
    } else {
        let mut v_head_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1014_);
        v_head_1017_ = crate::leanh::lean_ctor_get(v_x_1012_, 0);
        crate::leanh::lean_inc(v_head_1017_);
        v_tail_1018_ = crate::leanh::lean_ctor_get(v_x_1012_, 1);
        crate::leanh::lean_inc(v_tail_1018_);
        crate::leanh::lean_dec_ref_known(v_x_1012_, 2);
        v___x_1019_ = crate::leanh::lean_apply_2(v_h__1_1013_, v_head_1017_, v_tail_1018_);
        return v___x_1019_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
    mut v_x_1020_: u8,
    mut v_h__1_1021_: *mut crate::leanh::LeanObject,
    mut v_h__2_1022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1020_ == 0 {
        let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1021_);
        v___x_1023_ = crate::leanh::lean_box(0);
        v___x_1024_ = crate::leanh::lean_apply_1(v_h__2_1022_, v___x_1023_);
        return v___x_1024_;
    } else {
        let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1022_);
        v___x_1025_ = crate::leanh::lean_box(0);
        v___x_1026_ = crate::leanh::lean_apply_1(v_h__1_1021_, v___x_1025_);
        return v___x_1026_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(
    mut v_x_1027_: *mut crate::leanh::LeanObject,
    mut v_h__1_1028_: *mut crate::leanh::LeanObject,
    mut v_h__2_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_26__boxed_1030_: u8 = 0;
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1030_ = (crate::leanh::lean_unbox(v_x_1027_) as u8);
    v_res_1031_ =
        l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
            v_x_26__boxed_1030_,
            v_h__1_1028_,
            v_h__2_1029_,
        );
    return v_res_1031_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
    mut v_motive_1032_: *mut crate::leanh::LeanObject,
    mut v_x_1033_: u8,
    mut v_h__1_1034_: *mut crate::leanh::LeanObject,
    mut v_h__2_1035_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if v_x_1033_ == 0 {
        let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1034_);
        v___x_1036_ = crate::leanh::lean_box(0);
        v___x_1037_ = crate::leanh::lean_apply_1(v_h__2_1035_, v___x_1036_);
        return v___x_1037_;
    } else {
        let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1035_);
        v___x_1038_ = crate::leanh::lean_box(0);
        v___x_1039_ = crate::leanh::lean_apply_1(v_h__1_1034_, v___x_1038_);
        return v___x_1039_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(
    mut v_motive_1040_: *mut crate::leanh::LeanObject,
    mut v_x_1041_: *mut crate::leanh::LeanObject,
    mut v_h__1_1042_: *mut crate::leanh::LeanObject,
    mut v_h__2_1043_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_37__boxed_1044_: u8 = 0;
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1044_ = (crate::leanh::lean_unbox(v_x_1041_) as u8);
    v_res_1045_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
        v_motive_1040_,
        v_x_37__boxed_1044_,
        v_h__1_1042_,
        v_h__2_1043_,
    );
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(
    mut v_x_1046_: *mut crate::leanh::LeanObject,
    mut v_h__1_1047_: *mut crate::leanh::LeanObject,
    mut v_h__2_1048_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1046_) == 0 {
        let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1048_);
        v___x_1049_ = crate::leanh::lean_box(0);
        v___x_1050_ = crate::leanh::lean_apply_1(v_h__1_1047_, v___x_1049_);
        return v___x_1050_;
    } else {
        let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1047_);
        v___x_1051_ =
            crate::leanh::lean_apply_2(v_h__2_1048_, v_x_1046_, crate::leanh::lean_box(0));
        return v___x_1051_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(
    mut v_motive_1052_: *mut crate::leanh::LeanObject,
    mut v_x_1053_: *mut crate::leanh::LeanObject,
    mut v_h__1_1054_: *mut crate::leanh::LeanObject,
    mut v_h__2_1055_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1053_) == 0 {
        let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1055_);
        v___x_1056_ = crate::leanh::lean_box(0);
        v___x_1057_ = crate::leanh::lean_apply_1(v_h__1_1054_, v___x_1056_);
        return v___x_1057_;
    } else {
        let mut v___x_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1054_);
        v___x_1058_ =
            crate::leanh::lean_apply_2(v_h__2_1055_, v_x_1053_, crate::leanh::lean_box(0));
        return v___x_1058_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_AC(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_AC(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_AC(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_AC(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_AC(builtin);
}

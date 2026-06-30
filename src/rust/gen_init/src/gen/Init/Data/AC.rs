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
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Data_AC_instInhabitedExpr_default___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr_default: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__0_value: leanh::LeanStringObject<22> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Data_AC_instReprExpr_repr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__1_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Data_AC_instReprExpr_repr___closed__5_value: leanh::LeanStringObject<21> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
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
static mut l_Lean_Data_AC_instReprExpr_repr___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__6_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value)
                as *mut leanh::LeanObject,
            (((1 as usize) << 1) | 1) as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instReprExpr_repr___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instReprExpr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instReprExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Data_AC_instReprExpr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instBEqExpr___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instBEqExpr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Data_AC_instBEqExpr: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__0_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__1_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__2_value:
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
    m_fun: l_Lean_Data_AC_instContextInformationContext___lam__2___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_AC_instContextInformationContext___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__0_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__1_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__1 as *const core::ffi::c_void,
    m_arity: 3,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__2_value:
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
    m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Data_AC_instEvalInformationContext___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__3_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx(
    mut v_x_530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_530_) == 0 {
        let mut v___x_531_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_531_ = leanh::lean_unsigned_to_nat(0);
        return v___x_531_;
    } else {
        let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_532_ = leanh::lean_unsigned_to_nat(1);
        return v___x_532_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx___boxed(
    mut v_x_533_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_534_ = l_Lean_Data_AC_Expr_ctorIdx(v_x_533_);
    leanh::lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___redArg(
    mut v_t_535_: *mut leanh::LeanObject,
    mut v_k_536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_535_) == 0 {
        let mut v_x_537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_537_ = leanh::lean_ctor_get(v_t_535_, 0);
        leanh::lean_inc(v_x_537_);
        leanh::lean_dec_ref_known(v_t_535_, 1);
        v___x_538_ = leanh::lean_apply_1(v_k_536_, v_x_537_);
        return v___x_538_;
    } else {
        let mut v_lhs_539_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_540_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lhs_539_ = leanh::lean_ctor_get(v_t_535_, 0);
        leanh::lean_inc_ref(v_lhs_539_);
        v_rhs_540_ = leanh::lean_ctor_get(v_t_535_, 1);
        leanh::lean_inc_ref(v_rhs_540_);
        leanh::lean_dec_ref_known(v_t_535_, 2);
        v___x_541_ = leanh::lean_apply_2(v_k_536_, v_lhs_539_, v_rhs_540_);
        return v___x_541_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim(
    mut v_motive_542_: *mut leanh::LeanObject,
    mut v_ctorIdx_543_: *mut leanh::LeanObject,
    mut v_t_544_: *mut leanh::LeanObject,
    mut v_h_545_: *mut leanh::LeanObject,
    mut v_k_546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_544_, v_k_546_);
    return v___x_547_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___boxed(
    mut v_motive_548_: *mut leanh::LeanObject,
    mut v_ctorIdx_549_: *mut leanh::LeanObject,
    mut v_t_550_: *mut leanh::LeanObject,
    mut v_h_551_: *mut leanh::LeanObject,
    mut v_k_552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_553_ =
        l_Lean_Data_AC_Expr_ctorElim(v_motive_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
    leanh::lean_dec(v_ctorIdx_549_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim___redArg(
    mut v_t_554_: *mut leanh::LeanObject,
    mut v_var_555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_554_, v_var_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim(
    mut v_motive_557_: *mut leanh::LeanObject,
    mut v_t_558_: *mut leanh::LeanObject,
    mut v_h_559_: *mut leanh::LeanObject,
    mut v_var_560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_558_, v_var_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim___redArg(
    mut v_t_562_: *mut leanh::LeanObject,
    mut v_op_563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_562_, v_op_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim(
    mut v_motive_565_: *mut leanh::LeanObject,
    mut v_t_566_: *mut leanh::LeanObject,
    mut v_h_567_: *mut leanh::LeanObject,
    mut v_op_568_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_569_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_569_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_566_, v_op_568_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__3() -> *mut leanh::LeanObject
{
    let mut v___x_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_580_ = leanh::lean_unsigned_to_nat(2);
    v___x_581_ = lean_nat_to_int(v___x_580_);
    return v___x_581_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__4() -> *mut leanh::LeanObject
{
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_582_ = leanh::lean_unsigned_to_nat(1);
    v___x_583_ = lean_nat_to_int(v___x_582_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Data_AC_instReprExpr_repr(
    mut v_x_590_: *mut leanh::LeanObject,
    mut v_prec_591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___y_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_612_: u8 = 0;
    let mut v_lhs_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_590_) == 0 {
                    v_x_592_ = leanh::lean_ctor_get(v_x_590_, 0);
                    v_isSharedCheck_612_ = (!leanh::lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_612_ == 0 {
                        v___x_594_ = v_x_590_;
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_x_592_);
                        leanh::lean_dec(v_x_590_);
                        v___x_594_ = leanh::lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_613_ = leanh::lean_ctor_get(v_x_590_, 0);
                    v_rhs_614_ = leanh::lean_ctor_get(v_x_590_, 1);
                    v_isSharedCheck_637_ = (!leanh::lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_637_ == 0 {
                        v___x_616_ = v_x_590_;
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_rhs_614_);
                        leanh::lean_inc(v_lhs_613_);
                        leanh::lean_dec(v_x_590_);
                        v___x_616_ = leanh::lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_608_ = leanh::lean_unsigned_to_nat(1024);
                v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_591_);
                if v___x_609_ == 0 {
                    v___x_610_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_597_ = v___x_610_;
                    state = 2;
                    continue;
                } else {
                    v___x_611_ = leanh::lean_obj_once(
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
                    leanh::lean_ctor_set_tag(v___x_594_, 3);
                    leanh::lean_ctor_set(v___x_594_, 0, v___x_599_);
                    v___x_601_ = v___x_594_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_607_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
                    v___x_601_ = v_reuseFailAlloc_607_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_602_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_602_, 0, v___x_598_);
                leanh::lean_ctor_set(v___x_602_, 1, v___x_601_);
                leanh::lean_inc(v___y_597_);
                v___x_603_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_603_, 0, v___y_597_);
                leanh::lean_ctor_set(v___x_603_, 1, v___x_602_);
                v___x_604_ = 0;
                v___x_605_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_605_, 0, v___x_603_);
                leanh::lean_ctor_set_uint8(
                    v___x_605_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_591_);
                return v___x_606_;
            }
            4 => {
                v___x_618_ = leanh::lean_unsigned_to_nat(1024);
                v___x_634_ = lean_nat_dec_le(v___x_618_, v_prec_591_);
                if v___x_634_ == 0 {
                    v___x_635_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_620_ = v___x_635_;
                    state = 5;
                    continue;
                } else {
                    v___x_636_ = leanh::lean_obj_once(
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
                v___x_621_ = leanh::lean_box(1);
                v___x_622_ = l_Lean_Data_AC_instReprExpr_repr___closed__7;
                v___x_623_ = l_Lean_Data_AC_instReprExpr_repr(v_lhs_613_, v___x_618_);
                if v_isShared_617_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_616_, 5);
                    leanh::lean_ctor_set(v___x_616_, 1, v___x_623_);
                    leanh::lean_ctor_set(v___x_616_, 0, v___x_622_);
                    v___x_625_ = v___x_616_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_623_);
                    v___x_625_ = v_reuseFailAlloc_633_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_626_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_626_, 0, v___x_625_);
                leanh::lean_ctor_set(v___x_626_, 1, v___x_621_);
                v___x_627_ = l_Lean_Data_AC_instReprExpr_repr(v_rhs_614_, v___x_618_);
                v___x_628_ = leanh::lean_alloc_ctor(5, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_628_, 0, v___x_626_);
                leanh::lean_ctor_set(v___x_628_, 1, v___x_627_);
                leanh::lean_inc(v___y_620_);
                v___x_629_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_629_, 0, v___y_620_);
                leanh::lean_ctor_set(v___x_629_, 1, v___x_628_);
                v___x_630_ = 0;
                v___x_631_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_631_, 0, v___x_629_);
                leanh::lean_ctor_set_uint8(
                    v___x_631_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
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
    mut v_x_638_: *mut leanh::LeanObject,
    mut v_prec_639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Lean_Data_AC_instReprExpr_repr(v_x_638_, v_prec_639_);
    leanh::lean_dec(v_prec_639_);
    return v_res_640_;
}
pub unsafe fn l_Lean_Data_AC_instBEqExpr_beq(
    mut v_x_643_: *mut leanh::LeanObject,
    mut v_x_644_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_x_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v_lhs_649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lhs_651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_643_) == 0 {
                    if leanh::lean_obj_tag(v_x_644_) == 0 {
                        v_x_645_ = leanh::lean_ctor_get(v_x_643_, 0);
                        v_x_646_ = leanh::lean_ctor_get(v_x_644_, 0);
                        v___x_647_ = lean_nat_dec_eq(v_x_645_, v_x_646_);
                        return v___x_647_;
                    } else {
                        v___x_648_ = 0;
                        return v___x_648_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_644_) == 1 {
                        v_lhs_649_ = leanh::lean_ctor_get(v_x_643_, 0);
                        v_rhs_650_ = leanh::lean_ctor_get(v_x_643_, 1);
                        v_lhs_651_ = leanh::lean_ctor_get(v_x_644_, 0);
                        v_rhs_652_ = leanh::lean_ctor_get(v_x_644_, 1);
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
    mut v_x_656_: *mut leanh::LeanObject,
    mut v_x_657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_658_: u8 = 0;
    let mut v_r_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_656_, v_x_657_);
    leanh::lean_dec_ref(v_x_657_);
    leanh::lean_dec_ref(v_x_656_);
    v_r_659_ = leanh::lean_box((v_res_658_) as usize);
    return v_r_659_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg(
    mut v_ctx_662_: *mut leanh::LeanObject,
    mut v_idx_663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vars_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_arbitrary_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_vars_664_ = leanh::lean_ctor_get(v_ctx_662_, 3);
    v_arbitrary_665_ = leanh::lean_ctor_get(v_ctx_662_, 4);
    v___x_666_ = l_List_get_x3fInternal___redArg(v_vars_664_, v_idx_663_);
    if leanh::lean_obj_tag(v___x_666_) == 0 {
        let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_667_ = leanh::lean_box(0);
        leanh::lean_inc(v_arbitrary_665_);
        v___x_668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_668_, 0, v_arbitrary_665_);
        leanh::lean_ctor_set(v___x_668_, 1, v___x_667_);
        return v___x_668_;
    } else {
        let mut v_val_669_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_669_ = leanh::lean_ctor_get(v___x_666_, 0);
        leanh::lean_inc(v_val_669_);
        leanh::lean_dec_ref_known(v___x_666_, 1);
        return v_val_669_;
    }
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg___boxed(
    mut v_ctx_670_: *mut leanh::LeanObject,
    mut v_idx_671_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_670_, v_idx_671_);
    leanh::lean_dec_ref(v_ctx_670_);
    return v_res_672_;
}
pub unsafe fn l_Lean_Data_AC_Context_var(
    mut v_00_u03b1_673_: *mut leanh::LeanObject,
    mut v_ctx_674_: *mut leanh::LeanObject,
    mut v_idx_675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_674_, v_idx_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___boxed(
    mut v_00_u03b1_677_: *mut leanh::LeanObject,
    mut v_ctx_678_: *mut leanh::LeanObject,
    mut v_idx_679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_Data_AC_Context_var(v_00_u03b1_677_, v_ctx_678_, v_idx_679_);
    leanh::lean_dec_ref(v_ctx_678_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0(
    mut v_ctx_681_: *mut leanh::LeanObject,
    mut v_x_682_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_neutral_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_681_, v_x_682_);
    v_neutral_684_ = leanh::lean_ctor_get(v___x_683_, 1);
    leanh::lean_inc(v_neutral_684_);
    leanh::lean_dec_ref(v___x_683_);
    if leanh::lean_obj_tag(v_neutral_684_) == 0 {
        let mut v___x_685_: u8 = 0;
        v___x_685_ = 0;
        return v___x_685_;
    } else {
        let mut v___x_686_: u8 = 0;
        leanh::lean_dec_ref_known(v_neutral_684_, 1);
        v___x_686_ = 1;
        return v___x_686_;
    }
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0___boxed(
    mut v_ctx_687_: *mut leanh::LeanObject,
    mut v_x_688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_689_: u8 = 0;
    let mut v_r_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Lean_Data_AC_instContextInformationContext___lam__0(v_ctx_687_, v_x_688_);
    leanh::lean_dec_ref(v_ctx_687_);
    v_r_690_ = leanh::lean_box((v_res_689_) as usize);
    return v_r_690_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__1(
    mut v_ctx_691_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_comm_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_comm_692_ = leanh::lean_ctor_get(v_ctx_691_, 1);
    if leanh::lean_obj_tag(v_comm_692_) == 0 {
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
    mut v_ctx_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_696_: u8 = 0;
    let mut v_r_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Data_AC_instContextInformationContext___lam__1(v_ctx_695_);
    leanh::lean_dec_ref(v_ctx_695_);
    v_r_697_ = leanh::lean_box((v_res_696_) as usize);
    return v_r_697_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__2(
    mut v_ctx_698_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_idem_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_idem_699_ = leanh::lean_ctor_get(v_ctx_698_, 2);
    if leanh::lean_obj_tag(v_idem_699_) == 0 {
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
    mut v_ctx_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_703_: u8 = 0;
    let mut v_r_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lean_Data_AC_instContextInformationContext___lam__2(v_ctx_702_);
    leanh::lean_dec_ref(v_ctx_702_);
    v_r_704_ = leanh::lean_box((v_res_703_) as usize);
    return v_r_704_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext(
    mut v_00_u03b1_712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_Data_AC_instContextInformationContext___closed__3;
    return v___x_713_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0(
    mut v_ctx_714_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_arbitrary_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_arbitrary_715_ = leanh::lean_ctor_get(v_ctx_714_, 4);
    leanh::lean_inc(v_arbitrary_715_);
    return v_arbitrary_715_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed(
    mut v_ctx_716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Data_AC_instEvalInformationContext___lam__0(v_ctx_716_);
    leanh::lean_dec_ref(v_ctx_716_);
    return v_res_717_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__1(
    mut v_ctx_718_: *mut leanh::LeanObject,
    mut v___y_719_: *mut leanh::LeanObject,
    mut v___y_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_op_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_op_721_ = leanh::lean_ctor_get(v_ctx_718_, 0);
    leanh::lean_inc(v_op_721_);
    leanh::lean_dec_ref(v_ctx_718_);
    v___x_722_ = leanh::lean_apply_2(v_op_721_, v___y_719_, v___y_720_);
    return v___x_722_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2(
    mut v_ctx_723_: *mut leanh::LeanObject,
    mut v_idx_724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_723_, v_idx_724_);
    v_value_726_ = leanh::lean_ctor_get(v___x_725_, 0);
    leanh::lean_inc(v_value_726_);
    leanh::lean_dec_ref(v___x_725_);
    return v_value_726_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed(
    mut v_ctx_727_: *mut leanh::LeanObject,
    mut v_idx_728_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Data_AC_instEvalInformationContext___lam__2(v_ctx_727_, v_idx_728_);
    leanh::lean_dec_ref(v_ctx_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext(
    mut v_00_u03b1_737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_738_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_Data_AC_instEvalInformationContext___closed__3;
    return v___x_738_;
}
pub unsafe fn l_Lean_Data_AC_eval___redArg(
    mut v_inst_739_: *mut leanh::LeanObject,
    mut v_ctx_740_: *mut leanh::LeanObject,
    mut v_x_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_741_) == 0 {
        let mut v_x_742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_evalVar_743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_742_ = leanh::lean_ctor_get(v_x_741_, 0);
        leanh::lean_inc(v_x_742_);
        leanh::lean_dec_ref_known(v_x_741_, 1);
        v_evalVar_743_ = leanh::lean_ctor_get(v_inst_739_, 2);
        leanh::lean_inc(v_evalVar_743_);
        leanh::lean_dec_ref(v_inst_739_);
        v___x_744_ = leanh::lean_apply_2(v_evalVar_743_, v_ctx_740_, v_x_742_);
        return v___x_744_;
    } else {
        let mut v_lhs_745_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_746_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_evalOp_747_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lhs_745_ = leanh::lean_ctor_get(v_x_741_, 0);
        leanh::lean_inc_ref(v_lhs_745_);
        v_rhs_746_ = leanh::lean_ctor_get(v_x_741_, 1);
        leanh::lean_inc_ref(v_rhs_746_);
        leanh::lean_dec_ref_known(v_x_741_, 2);
        v_evalOp_747_ = leanh::lean_ctor_get(v_inst_739_, 1);
        leanh::lean_inc(v_evalOp_747_);
        leanh::lean_inc_n(v_ctx_740_, 2);
        leanh::lean_inc_ref(v_inst_739_);
        v___x_748_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_lhs_745_);
        v___x_749_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_rhs_746_);
        v___x_750_ = leanh::lean_apply_3(v_evalOp_747_, v_ctx_740_, v___x_748_, v___x_749_);
        return v___x_750_;
    }
}
pub unsafe fn l_Lean_Data_AC_eval(
    mut v_00_u03b1_751_: *mut leanh::LeanObject,
    mut v_00_u03b2_752_: *mut leanh::LeanObject,
    mut v_inst_753_: *mut leanh::LeanObject,
    mut v_ctx_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ = l_Lean_Data_AC_eval___redArg(v_inst_753_, v_ctx_754_, v_x_755_);
    return v___x_756_;
}
pub unsafe fn l_Lean_Data_AC_Expr_toList(
    mut v_x_757_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_757_) == 0 {
        let mut v_x_758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_x_758_ = leanh::lean_ctor_get(v_x_757_, 0);
        v___x_759_ = leanh::lean_box(0);
        leanh::lean_inc(v_x_758_);
        v___x_760_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_760_, 0, v_x_758_);
        leanh::lean_ctor_set(v___x_760_, 1, v___x_759_);
        return v___x_760_;
    } else {
        let mut v_lhs_761_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_762_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_lhs_761_ = leanh::lean_ctor_get(v_x_757_, 0);
        v_rhs_762_ = leanh::lean_ctor_get(v_x_757_, 1);
        v___x_763_ = l_Lean_Data_AC_Expr_toList(v_lhs_761_);
        v___x_764_ = l_Lean_Data_AC_Expr_toList(v_rhs_762_);
        v___x_765_ = l_List_appendTR___redArg(v___x_763_, v___x_764_);
        return v___x_765_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_toList___boxed(
    mut v_x_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lean_Data_AC_Expr_toList(v_x_766_);
    leanh::lean_dec_ref(v_x_766_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Data_AC_evalList___redArg(
    mut v_inst_768_: *mut leanh::LeanObject,
    mut v_ctx_769_: *mut leanh::LeanObject,
    mut v_x_770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_770_) == 0 {
        let mut v_arbitrary_771_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_arbitrary_771_ = leanh::lean_ctor_get(v_inst_768_, 0);
        leanh::lean_inc(v_arbitrary_771_);
        leanh::lean_dec_ref(v_inst_768_);
        v___x_772_ = leanh::lean_apply_1(v_arbitrary_771_, v_ctx_769_);
        return v___x_772_;
    } else {
        let mut v_tail_773_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_tail_773_ = leanh::lean_ctor_get(v_x_770_, 1);
        if leanh::lean_obj_tag(v_tail_773_) == 0 {
            let mut v_head_774_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalVar_775_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_head_774_ = leanh::lean_ctor_get(v_x_770_, 0);
            leanh::lean_inc(v_head_774_);
            leanh::lean_dec_ref_known(v_x_770_, 2);
            v_evalVar_775_ = leanh::lean_ctor_get(v_inst_768_, 2);
            leanh::lean_inc(v_evalVar_775_);
            leanh::lean_dec_ref(v_inst_768_);
            v___x_776_ = leanh::lean_apply_2(v_evalVar_775_, v_ctx_769_, v_head_774_);
            return v___x_776_;
        } else {
            let mut v_head_777_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalOp_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_evalVar_779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_773_);
            v_head_777_ = leanh::lean_ctor_get(v_x_770_, 0);
            leanh::lean_inc(v_head_777_);
            leanh::lean_dec_ref_known(v_x_770_, 2);
            v_evalOp_778_ = leanh::lean_ctor_get(v_inst_768_, 1);
            leanh::lean_inc(v_evalOp_778_);
            v_evalVar_779_ = leanh::lean_ctor_get(v_inst_768_, 2);
            leanh::lean_inc(v_evalVar_779_);
            leanh::lean_inc_n(v_ctx_769_, 2);
            v___x_780_ = leanh::lean_apply_2(v_evalVar_779_, v_ctx_769_, v_head_777_);
            v___x_781_ = l_Lean_Data_AC_evalList___redArg(v_inst_768_, v_ctx_769_, v_tail_773_);
            v___x_782_ =
                leanh::lean_apply_3(v_evalOp_778_, v_ctx_769_, v___x_780_, v___x_781_);
            return v___x_782_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_evalList(
    mut v_00_u03b1_783_: *mut leanh::LeanObject,
    mut v_00_u03b2_784_: *mut leanh::LeanObject,
    mut v_inst_785_: *mut leanh::LeanObject,
    mut v_ctx_786_: *mut leanh::LeanObject,
    mut v_x_787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_Data_AC_evalList___redArg(v_inst_785_, v_ctx_786_, v_x_787_);
    return v___x_788_;
}
pub unsafe fn l_Lean_Data_AC_insert(
    mut v_x_789_: *mut leanh::LeanObject,
    mut v_x_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_797_: u8 = 0;
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_802_: u8 = 0;
    let mut v_unused_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_790_) == 0 {
                    v___x_791_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_791_, 0, v_x_789_);
                    leanh::lean_ctor_set(v___x_791_, 1, v_x_790_);
                    return v___x_791_;
                } else {
                    v_head_792_ = leanh::lean_ctor_get(v_x_790_, 0);
                    v_tail_793_ = leanh::lean_ctor_get(v_x_790_, 1);
                    v___x_794_ = lean_nat_dec_lt(v_x_789_, v_head_792_);
                    if v___x_794_ == 0 {
                        leanh::lean_inc(v_tail_793_);
                        leanh::lean_inc(v_head_792_);
                        v_isSharedCheck_802_ = (!leanh::lean_is_exclusive(v_x_790_)) as u8;
                        if v_isSharedCheck_802_ == 0 {
                            v_unused_803_ = leanh::lean_ctor_get(v_x_790_, 1);
                            leanh::lean_dec(v_unused_803_);
                            v_unused_804_ = leanh::lean_ctor_get(v_x_790_, 0);
                            leanh::lean_dec(v_unused_804_);
                            v___x_796_ = v_x_790_;
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_790_);
                            v___x_796_ = leanh::lean_box(0);
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_805_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_805_, 0, v_x_789_);
                        leanh::lean_ctor_set(v___x_805_, 1, v_x_790_);
                        return v___x_805_;
                    }
                }
            }
            1 => {
                v___x_798_ = l_Lean_Data_AC_insert(v_x_789_, v_tail_793_);
                if v_isShared_797_ == 0 {
                    leanh::lean_ctor_set(v___x_796_, 1, v___x_798_);
                    v___x_800_ = v___x_796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_801_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_801_, 0, v_head_792_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
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
    mut v_a_806_: *mut leanh::LeanObject,
    mut v_a_807_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_807_) == 0 {
                    return v_a_806_;
                } else {
                    v_head_808_ = leanh::lean_ctor_get(v_a_807_, 0);
                    leanh::lean_inc(v_head_808_);
                    v_tail_809_ = leanh::lean_ctor_get(v_a_807_, 1);
                    leanh::lean_inc(v_tail_809_);
                    leanh::lean_dec_ref_known(v_a_807_, 2);
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
    mut v_xs_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_813_ = leanh::lean_box(0);
    v___x_814_ = l_Lean_Data_AC_sort_loop(v___x_813_, v_xs_812_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Data_AC_mergeIdem_loop(
    mut v_a_815_: *mut leanh::LeanObject,
    mut v_a_816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_816_) == 0 {
                    v___x_817_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_817_, 0, v_a_815_);
                    leanh::lean_ctor_set(v___x_817_, 1, v_a_816_);
                    return v___x_817_;
                } else {
                    v_head_818_ = leanh::lean_ctor_get(v_a_816_, 0);
                    v_tail_819_ = leanh::lean_ctor_get(v_a_816_, 1);
                    v_isSharedCheck_829_ = (!leanh::lean_is_exclusive(v_a_816_)) as u8;
                    if v_isSharedCheck_829_ == 0 {
                        v___x_821_ = v_a_816_;
                        v_isShared_822_ = v_isSharedCheck_829_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_819_);
                        leanh::lean_inc(v_head_818_);
                        leanh::lean_dec(v_a_816_);
                        v___x_821_ = leanh::lean_box(0);
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
                        leanh::lean_ctor_set(v___x_821_, 1, v___x_824_);
                        leanh::lean_ctor_set(v___x_821_, 0, v_a_815_);
                        v___x_826_ = v___x_821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_827_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_815_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
                        v___x_826_ = v_reuseFailAlloc_827_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_821_);
                    leanh::lean_dec(v_head_818_);
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
    mut v_xs_830_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_xs_830_) == 0 {
        return v_xs_830_;
    } else {
        let mut v_head_831_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_831_ = leanh::lean_ctor_get(v_xs_830_, 0);
        leanh::lean_inc(v_head_831_);
        v_tail_832_ = leanh::lean_ctor_get(v_xs_830_, 1);
        leanh::lean_inc(v_tail_832_);
        leanh::lean_dec_ref_known(v_xs_830_, 2);
        v___x_833_ = l_Lean_Data_AC_mergeIdem_loop(v_head_831_, v_tail_832_);
        return v___x_833_;
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop___redArg(
    mut v_info_834_: *mut leanh::LeanObject,
    mut v_ctx_835_: *mut leanh::LeanObject,
    mut v_a_836_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v_isNeutral_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_836_) == 0 {
                    leanh::lean_dec(v_ctx_835_);
                    leanh::lean_dec_ref(v_info_834_);
                    return v_a_836_;
                } else {
                    v_head_837_ = leanh::lean_ctor_get(v_a_836_, 0);
                    v_tail_838_ = leanh::lean_ctor_get(v_a_836_, 1);
                    v_isSharedCheck_850_ = (!leanh::lean_is_exclusive(v_a_836_)) as u8;
                    if v_isSharedCheck_850_ == 0 {
                        v___x_840_ = v_a_836_;
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_838_);
                        leanh::lean_inc(v_head_837_);
                        leanh::lean_dec(v_a_836_);
                        v___x_840_ = leanh::lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_isNeutral_842_ = leanh::lean_ctor_get(v_info_834_, 0);
                leanh::lean_inc_ref(v_isNeutral_842_);
                leanh::lean_inc(v_head_837_);
                leanh::lean_inc(v_ctx_835_);
                v___x_843_ = leanh::lean_apply_2(v_isNeutral_842_, v_ctx_835_, v_head_837_);
                v___x_844_ = (leanh::lean_unbox(v___x_843_) as u8);
                if v___x_844_ == 0 {
                    v___x_845_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(
                        v_info_834_,
                        v_ctx_835_,
                        v_tail_838_,
                    );
                    if v_isShared_841_ == 0 {
                        leanh::lean_ctor_set(v___x_840_, 1, v___x_845_);
                        v___x_847_ = v___x_840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_848_, 0, v_head_837_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
                        v___x_847_ = v_reuseFailAlloc_848_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_840_);
                    leanh::lean_dec(v_head_837_);
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
    mut v_00_u03b1_851_: *mut leanh::LeanObject,
    mut v_info_852_: *mut leanh::LeanObject,
    mut v_ctx_853_: *mut leanh::LeanObject,
    mut v_a_854_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_852_, v_ctx_853_, v_a_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals___redArg(
    mut v_info_856_: *mut leanh::LeanObject,
    mut v_ctx_857_: *mut leanh::LeanObject,
    mut v_x_858_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_858_) == 0 {
        leanh::lean_dec(v_ctx_857_);
        leanh::lean_dec_ref(v_info_856_);
        return v_x_858_;
    } else {
        let mut v_head_859_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_head_859_ = leanh::lean_ctor_get(v_x_858_, 0);
        leanh::lean_inc(v_head_859_);
        v___x_860_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_856_, v_ctx_857_, v_x_858_);
        if leanh::lean_obj_tag(v___x_860_) == 0 {
            let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_861_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
            leanh::lean_ctor_set(v___x_861_, 0, v_head_859_);
            leanh::lean_ctor_set(v___x_861_, 1, v___x_860_);
            return v___x_861_;
        } else {
            leanh::lean_dec(v_head_859_);
            return v___x_860_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals(
    mut v_00_u03b1_862_: *mut leanh::LeanObject,
    mut v_info_863_: *mut leanh::LeanObject,
    mut v_ctx_864_: *mut leanh::LeanObject,
    mut v_x_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_863_, v_ctx_864_, v_x_865_);
    return v___x_866_;
}
pub unsafe fn l_Lean_Data_AC_norm___redArg(
    mut v_info_867_: *mut leanh::LeanObject,
    mut v_ctx_868_: *mut leanh::LeanObject,
    mut v_e_869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isComm_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isIdem_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isComm_870_ = leanh::lean_ctor_get(v_info_867_, 1);
                leanh::lean_inc_ref(v_isComm_870_);
                v_isIdem_871_ = leanh::lean_ctor_get(v_info_867_, 2);
                leanh::lean_inc_ref(v_isIdem_871_);
                v_xs_877_ = l_Lean_Data_AC_Expr_toList(v_e_869_);
                leanh::lean_inc_n(v_ctx_868_, 2);
                v_xs_878_ =
                    l_Lean_Data_AC_removeNeutrals___redArg(v_info_867_, v_ctx_868_, v_xs_877_);
                v___x_879_ = leanh::lean_apply_1(v_isComm_870_, v_ctx_868_);
                v___x_880_ = (leanh::lean_unbox(v___x_879_) as u8);
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
                v___x_874_ = leanh::lean_apply_1(v_isIdem_871_, v_ctx_868_);
                v___x_875_ = (leanh::lean_unbox(v___x_874_) as u8);
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
    mut v_info_882_: *mut leanh::LeanObject,
    mut v_ctx_883_: *mut leanh::LeanObject,
    mut v_e_884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_Data_AC_norm___redArg(v_info_882_, v_ctx_883_, v_e_884_);
    leanh::lean_dec_ref(v_e_884_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Data_AC_norm(
    mut v_00_u03b1_886_: *mut leanh::LeanObject,
    mut v_info_887_: *mut leanh::LeanObject,
    mut v_ctx_888_: *mut leanh::LeanObject,
    mut v_e_889_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Lean_Data_AC_norm___redArg(v_info_887_, v_ctx_888_, v_e_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Data_AC_norm___boxed(
    mut v_00_u03b1_891_: *mut leanh::LeanObject,
    mut v_info_892_: *mut leanh::LeanObject,
    mut v_ctx_893_: *mut leanh::LeanObject,
    mut v_e_894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lean_Data_AC_norm(v_00_u03b1_891_, v_info_892_, v_ctx_893_, v_e_894_);
    leanh::lean_dec_ref(v_e_894_);
    return v_res_895_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(
    mut v_x_896_: *mut leanh::LeanObject,
    mut v_h__1_897_: *mut leanh::LeanObject,
    mut v_h__2_898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_896_) == 0 {
        let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_898_);
        v___x_899_ = leanh::lean_box(0);
        v___x_900_ = leanh::lean_apply_1(v_h__1_897_, v___x_899_);
        return v___x_900_;
    } else {
        let mut v_head_901_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_902_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_897_);
        v_head_901_ = leanh::lean_ctor_get(v_x_896_, 0);
        leanh::lean_inc(v_head_901_);
        v_tail_902_ = leanh::lean_ctor_get(v_x_896_, 1);
        leanh::lean_inc(v_tail_902_);
        leanh::lean_dec_ref_known(v_x_896_, 2);
        v___x_903_ = leanh::lean_apply_2(v_h__2_898_, v_head_901_, v_tail_902_);
        return v___x_903_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(
    mut v_motive_904_: *mut leanh::LeanObject,
    mut v_x_905_: *mut leanh::LeanObject,
    mut v_h__1_906_: *mut leanh::LeanObject,
    mut v_h__2_907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_905_) == 0 {
        let mut v___x_908_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_907_);
        v___x_908_ = leanh::lean_box(0);
        v___x_909_ = leanh::lean_apply_1(v_h__1_906_, v___x_908_);
        return v___x_909_;
    } else {
        let mut v_head_910_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_911_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_906_);
        v_head_910_ = leanh::lean_ctor_get(v_x_905_, 0);
        leanh::lean_inc(v_head_910_);
        v_tail_911_ = leanh::lean_ctor_get(v_x_905_, 1);
        leanh::lean_inc(v_tail_911_);
        leanh::lean_dec_ref_known(v_x_905_, 2);
        v___x_912_ = leanh::lean_apply_2(v_h__2_907_, v_head_910_, v_tail_911_);
        return v___x_912_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(
    mut v_x_913_: *mut leanh::LeanObject,
    mut v_x_914_: *mut leanh::LeanObject,
    mut v_h__1_915_: *mut leanh::LeanObject,
    mut v_h__2_916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_914_) == 0 {
        let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_915_);
        v___x_917_ = leanh::lean_apply_1(v_h__2_916_, v_x_913_);
        return v___x_917_;
    } else {
        let mut v_head_918_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_919_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_916_);
        v_head_918_ = leanh::lean_ctor_get(v_x_914_, 0);
        leanh::lean_inc(v_head_918_);
        v_tail_919_ = leanh::lean_ctor_get(v_x_914_, 1);
        leanh::lean_inc(v_tail_919_);
        leanh::lean_dec_ref_known(v_x_914_, 2);
        v___x_920_ = leanh::lean_apply_3(v_h__1_915_, v_x_913_, v_head_918_, v_tail_919_);
        return v___x_920_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(
    mut v_motive_921_: *mut leanh::LeanObject,
    mut v_x_922_: *mut leanh::LeanObject,
    mut v_x_923_: *mut leanh::LeanObject,
    mut v_h__1_924_: *mut leanh::LeanObject,
    mut v_h__2_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_923_) == 0 {
        let mut v___x_926_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_924_);
        v___x_926_ = leanh::lean_apply_1(v_h__2_925_, v_x_922_);
        return v___x_926_;
    } else {
        let mut v_head_927_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_928_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_925_);
        v_head_927_ = leanh::lean_ctor_get(v_x_923_, 0);
        leanh::lean_inc(v_head_927_);
        v_tail_928_ = leanh::lean_ctor_get(v_x_923_, 1);
        leanh::lean_inc(v_tail_928_);
        leanh::lean_dec_ref_known(v_x_923_, 2);
        v___x_929_ = leanh::lean_apply_3(v_h__1_924_, v_x_922_, v_head_927_, v_tail_928_);
        return v___x_929_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_930_: *mut leanh::LeanObject,
    mut v_h__1_931_: *mut leanh::LeanObject,
    mut v_h__2_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_930_) == 0 {
        let mut v___x_933_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_931_);
        v___x_933_ = leanh::lean_box(0);
        v___x_934_ = leanh::lean_apply_1(v_h__2_932_, v___x_933_);
        return v___x_934_;
    } else {
        let mut v_val_935_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_932_);
        v_val_935_ = leanh::lean_ctor_get(v_x_930_, 0);
        leanh::lean_inc(v_val_935_);
        leanh::lean_dec_ref_known(v_x_930_, 1);
        v___x_936_ = leanh::lean_apply_1(v_h__1_931_, v_val_935_);
        return v___x_936_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_937_: *mut leanh::LeanObject,
    mut v_motive_938_: *mut leanh::LeanObject,
    mut v_x_939_: *mut leanh::LeanObject,
    mut v_h__1_940_: *mut leanh::LeanObject,
    mut v_h__2_941_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_939_) == 0 {
        let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_940_);
        v___x_942_ = leanh::lean_box(0);
        v___x_943_ = leanh::lean_apply_1(v_h__2_941_, v___x_942_);
        return v___x_943_;
    } else {
        let mut v_val_944_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_941_);
        v_val_944_ = leanh::lean_ctor_get(v_x_939_, 0);
        leanh::lean_inc(v_val_944_);
        leanh::lean_dec_ref_known(v_x_939_, 1);
        v___x_945_ = leanh::lean_apply_1(v_h__1_940_, v_val_944_);
        return v___x_945_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(
    mut v_x_946_: *mut leanh::LeanObject,
    mut v_h__1_947_: *mut leanh::LeanObject,
    mut v_h__2_948_: *mut leanh::LeanObject,
    mut v_h__3_949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_946_) == 0 {
        let mut v___x_950_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_949_);
        leanh::lean_dec(v_h__2_948_);
        v___x_950_ = leanh::lean_box(0);
        v___x_951_ = leanh::lean_apply_1(v_h__1_947_, v___x_950_);
        return v___x_951_;
    } else {
        let mut v_tail_952_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_947_);
        v_tail_952_ = leanh::lean_ctor_get(v_x_946_, 1);
        if leanh::lean_obj_tag(v_tail_952_) == 0 {
            let mut v_head_953_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_949_);
            v_head_953_ = leanh::lean_ctor_get(v_x_946_, 0);
            leanh::lean_inc(v_head_953_);
            leanh::lean_dec_ref_known(v_x_946_, 2);
            v___x_954_ = leanh::lean_apply_1(v_h__2_948_, v_head_953_);
            return v___x_954_;
        } else {
            let mut v_head_955_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_952_);
            leanh::lean_dec(v_h__2_948_);
            v_head_955_ = leanh::lean_ctor_get(v_x_946_, 0);
            leanh::lean_inc(v_head_955_);
            leanh::lean_dec_ref_known(v_x_946_, 2);
            v___x_956_ = leanh::lean_apply_3(
                v_h__3_949_,
                v_head_955_,
                v_tail_952_,
                leanh::lean_box(0),
            );
            return v___x_956_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(
    mut v_motive_957_: *mut leanh::LeanObject,
    mut v_x_958_: *mut leanh::LeanObject,
    mut v_h__1_959_: *mut leanh::LeanObject,
    mut v_h__2_960_: *mut leanh::LeanObject,
    mut v_h__3_961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_958_) == 0 {
        let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_961_);
        leanh::lean_dec(v_h__2_960_);
        v___x_962_ = leanh::lean_box(0);
        v___x_963_ = leanh::lean_apply_1(v_h__1_959_, v___x_962_);
        return v___x_963_;
    } else {
        let mut v_tail_964_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_959_);
        v_tail_964_ = leanh::lean_ctor_get(v_x_958_, 1);
        if leanh::lean_obj_tag(v_tail_964_) == 0 {
            let mut v_head_965_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_961_);
            v_head_965_ = leanh::lean_ctor_get(v_x_958_, 0);
            leanh::lean_inc(v_head_965_);
            leanh::lean_dec_ref_known(v_x_958_, 2);
            v___x_966_ = leanh::lean_apply_1(v_h__2_960_, v_head_965_);
            return v___x_966_;
        } else {
            let mut v_head_967_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc(v_tail_964_);
            leanh::lean_dec(v_h__2_960_);
            v_head_967_ = leanh::lean_ctor_get(v_x_958_, 0);
            leanh::lean_inc(v_head_967_);
            leanh::lean_dec_ref_known(v_x_958_, 2);
            v___x_968_ = leanh::lean_apply_3(
                v_h__3_961_,
                v_head_967_,
                v_tail_964_,
                leanh::lean_box(0),
            );
            return v___x_968_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(
    mut v_x_969_: *mut leanh::LeanObject,
    mut v_x_970_: *mut leanh::LeanObject,
    mut v_h__1_971_: *mut leanh::LeanObject,
    mut v_h__2_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_970_) == 0 {
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_972_);
        v___x_973_ = leanh::lean_apply_1(v_h__1_971_, v_x_969_);
        return v___x_973_;
    } else {
        let mut v_head_974_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_975_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_971_);
        v_head_974_ = leanh::lean_ctor_get(v_x_970_, 0);
        leanh::lean_inc(v_head_974_);
        v_tail_975_ = leanh::lean_ctor_get(v_x_970_, 1);
        leanh::lean_inc(v_tail_975_);
        leanh::lean_dec_ref_known(v_x_970_, 2);
        v___x_976_ = leanh::lean_apply_3(v_h__2_972_, v_x_969_, v_head_974_, v_tail_975_);
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(
    mut v_motive_977_: *mut leanh::LeanObject,
    mut v_x_978_: *mut leanh::LeanObject,
    mut v_x_979_: *mut leanh::LeanObject,
    mut v_h__1_980_: *mut leanh::LeanObject,
    mut v_h__2_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_979_) == 0 {
        let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_981_);
        v___x_982_ = leanh::lean_apply_1(v_h__1_980_, v_x_978_);
        return v___x_982_;
    } else {
        let mut v_head_983_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_980_);
        v_head_983_ = leanh::lean_ctor_get(v_x_979_, 0);
        leanh::lean_inc(v_head_983_);
        v_tail_984_ = leanh::lean_ctor_get(v_x_979_, 1);
        leanh::lean_inc(v_tail_984_);
        leanh::lean_dec_ref_known(v_x_979_, 2);
        v___x_985_ = leanh::lean_apply_3(v_h__2_981_, v_x_978_, v_head_983_, v_tail_984_);
        return v___x_985_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(
    mut v_x_986_: *mut leanh::LeanObject,
    mut v_h__1_987_: *mut leanh::LeanObject,
    mut v_h__2_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_986_) == 0 {
        let mut v_x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_988_);
        v_x_989_ = leanh::lean_ctor_get(v_x_986_, 0);
        leanh::lean_inc(v_x_989_);
        leanh::lean_dec_ref_known(v_x_986_, 1);
        v___x_990_ = leanh::lean_apply_1(v_h__1_987_, v_x_989_);
        return v___x_990_;
    } else {
        let mut v_lhs_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_992_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_987_);
        v_lhs_991_ = leanh::lean_ctor_get(v_x_986_, 0);
        leanh::lean_inc_ref(v_lhs_991_);
        v_rhs_992_ = leanh::lean_ctor_get(v_x_986_, 1);
        leanh::lean_inc_ref(v_rhs_992_);
        leanh::lean_dec_ref_known(v_x_986_, 2);
        v___x_993_ = leanh::lean_apply_2(v_h__2_988_, v_lhs_991_, v_rhs_992_);
        return v___x_993_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(
    mut v_motive_994_: *mut leanh::LeanObject,
    mut v_x_995_: *mut leanh::LeanObject,
    mut v_h__1_996_: *mut leanh::LeanObject,
    mut v_h__2_997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_995_) == 0 {
        let mut v_x_998_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_997_);
        v_x_998_ = leanh::lean_ctor_get(v_x_995_, 0);
        leanh::lean_inc(v_x_998_);
        leanh::lean_dec_ref_known(v_x_995_, 1);
        v___x_999_ = leanh::lean_apply_1(v_h__1_996_, v_x_998_);
        return v___x_999_;
    } else {
        let mut v_lhs_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_996_);
        v_lhs_1000_ = leanh::lean_ctor_get(v_x_995_, 0);
        leanh::lean_inc_ref(v_lhs_1000_);
        v_rhs_1001_ = leanh::lean_ctor_get(v_x_995_, 1);
        leanh::lean_inc_ref(v_rhs_1001_);
        leanh::lean_dec_ref_known(v_x_995_, 2);
        v___x_1002_ = leanh::lean_apply_2(v_h__2_997_, v_lhs_1000_, v_rhs_1001_);
        return v___x_1002_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(
    mut v_x_1003_: *mut leanh::LeanObject,
    mut v_h__1_1004_: *mut leanh::LeanObject,
    mut v_h__2_1005_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1003_) == 0 {
        let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1004_);
        v___x_1006_ = leanh::lean_box(0);
        v___x_1007_ = leanh::lean_apply_1(v_h__2_1005_, v___x_1006_);
        return v___x_1007_;
    } else {
        let mut v_head_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1005_);
        v_head_1008_ = leanh::lean_ctor_get(v_x_1003_, 0);
        leanh::lean_inc(v_head_1008_);
        v_tail_1009_ = leanh::lean_ctor_get(v_x_1003_, 1);
        leanh::lean_inc(v_tail_1009_);
        leanh::lean_dec_ref_known(v_x_1003_, 2);
        v___x_1010_ = leanh::lean_apply_2(v_h__1_1004_, v_head_1008_, v_tail_1009_);
        return v___x_1010_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(
    mut v_motive_1011_: *mut leanh::LeanObject,
    mut v_x_1012_: *mut leanh::LeanObject,
    mut v_h__1_1013_: *mut leanh::LeanObject,
    mut v_h__2_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1012_) == 0 {
        let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1013_);
        v___x_1015_ = leanh::lean_box(0);
        v___x_1016_ = leanh::lean_apply_1(v_h__2_1014_, v___x_1015_);
        return v___x_1016_;
    } else {
        let mut v_head_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1014_);
        v_head_1017_ = leanh::lean_ctor_get(v_x_1012_, 0);
        leanh::lean_inc(v_head_1017_);
        v_tail_1018_ = leanh::lean_ctor_get(v_x_1012_, 1);
        leanh::lean_inc(v_tail_1018_);
        leanh::lean_dec_ref_known(v_x_1012_, 2);
        v___x_1019_ = leanh::lean_apply_2(v_h__1_1013_, v_head_1017_, v_tail_1018_);
        return v___x_1019_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
    mut v_x_1020_: u8,
    mut v_h__1_1021_: *mut leanh::LeanObject,
    mut v_h__2_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1020_ == 0 {
        let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1021_);
        v___x_1023_ = leanh::lean_box(0);
        v___x_1024_ = leanh::lean_apply_1(v_h__2_1022_, v___x_1023_);
        return v___x_1024_;
    } else {
        let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1022_);
        v___x_1025_ = leanh::lean_box(0);
        v___x_1026_ = leanh::lean_apply_1(v_h__1_1021_, v___x_1025_);
        return v___x_1026_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(
    mut v_x_1027_: *mut leanh::LeanObject,
    mut v_h__1_1028_: *mut leanh::LeanObject,
    mut v_h__2_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_26__boxed_1030_: u8 = 0;
    let mut v_res_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1030_ = (leanh::lean_unbox(v_x_1027_) as u8);
    v_res_1031_ =
        l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
            v_x_26__boxed_1030_,
            v_h__1_1028_,
            v_h__2_1029_,
        );
    return v_res_1031_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
    mut v_motive_1032_: *mut leanh::LeanObject,
    mut v_x_1033_: u8,
    mut v_h__1_1034_: *mut leanh::LeanObject,
    mut v_h__2_1035_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1033_ == 0 {
        let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1034_);
        v___x_1036_ = leanh::lean_box(0);
        v___x_1037_ = leanh::lean_apply_1(v_h__2_1035_, v___x_1036_);
        return v___x_1037_;
    } else {
        let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1035_);
        v___x_1038_ = leanh::lean_box(0);
        v___x_1039_ = leanh::lean_apply_1(v_h__1_1034_, v___x_1038_);
        return v___x_1039_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(
    mut v_motive_1040_: *mut leanh::LeanObject,
    mut v_x_1041_: *mut leanh::LeanObject,
    mut v_h__1_1042_: *mut leanh::LeanObject,
    mut v_h__2_1043_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_37__boxed_1044_: u8 = 0;
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1044_ = (leanh::lean_unbox(v_x_1041_) as u8);
    v_res_1045_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
        v_motive_1040_,
        v_x_37__boxed_1044_,
        v_h__1_1042_,
        v_h__2_1043_,
    );
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(
    mut v_x_1046_: *mut leanh::LeanObject,
    mut v_h__1_1047_: *mut leanh::LeanObject,
    mut v_h__2_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1046_) == 0 {
        let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1048_);
        v___x_1049_ = leanh::lean_box(0);
        v___x_1050_ = leanh::lean_apply_1(v_h__1_1047_, v___x_1049_);
        return v___x_1050_;
    } else {
        let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1047_);
        v___x_1051_ =
            leanh::lean_apply_2(v_h__2_1048_, v_x_1046_, leanh::lean_box(0));
        return v___x_1051_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(
    mut v_motive_1052_: *mut leanh::LeanObject,
    mut v_x_1053_: *mut leanh::LeanObject,
    mut v_h__1_1054_: *mut leanh::LeanObject,
    mut v_h__2_1055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1053_) == 0 {
        let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1055_);
        v___x_1056_ = leanh::lean_box(0);
        v___x_1057_ = leanh::lean_apply_1(v_h__1_1054_, v___x_1056_);
        return v___x_1057_;
    } else {
        let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1054_);
        v___x_1058_ =
            leanh::lean_apply_2(v_h__2_1055_, v_x_1053_, leanh::lean_box(0));
        return v___x_1058_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_AC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_AC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_AC(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_AC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_AC(builtin);
}
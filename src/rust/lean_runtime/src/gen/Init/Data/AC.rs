// Lean compiler output
// Module: Init.Data.AC
// Imports: Init.GetElem Init.ByCases Init.PropLemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Basic::l_List_appendTR___redArg;
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::GetElem::{
    initialize_Init_GetElem, l_List_get_x3fInternal___redArg, runtime_initialize_Init_GetElem,
};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Data_AC_instInhabitedExpr_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Data_AC_instInhabitedExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__0_value: LeanStringObject<22> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Data_AC_instReprExpr_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__2_value) as *mut LeanObject;
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Data_AC_instReprExpr_repr___closed__5_value: LeanStringObject<21> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Data_AC_instReprExpr_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__6_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr_repr___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__6_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Data_AC_instReprExpr_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr_repr___closed__7_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instReprExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instReprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Data_AC_instReprExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instReprExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instBEqExpr___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Data_AC_instBEqExpr_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Data_AC_instBEqExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Data_AC_instBEqExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instContextInformationContext___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instContextInformationContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instContextInformationContext___lam__1___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instContextInformationContext___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instContextInformationContext___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instContextInformationContext___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instContextInformationContext___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instContextInformationContext___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instContextInformationContext___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed
            as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instEvalInformationContext___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__1_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__1 as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instEvalInformationContext___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__2_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed
            as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Data_AC_instEvalInformationContext___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Data_AC_instEvalInformationContext___closed__3_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__1_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__2_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Data_AC_instEvalInformationContext___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Data_AC_instEvalInformationContext___closed__3_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx(mut v_x_530_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_530_) == 0 {
        let mut v___x_531_: *mut LeanObject = core::ptr::null_mut();
        v___x_531_ = lean_unsigned_to_nat(0);
        return v___x_531_;
    } else {
        let mut v___x_532_: *mut LeanObject = core::ptr::null_mut();
        v___x_532_ = lean_unsigned_to_nat(1);
        return v___x_532_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorIdx___boxed(
    mut v_x_533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_534_: *mut LeanObject = core::ptr::null_mut();
    v_res_534_ = l_Lean_Data_AC_Expr_ctorIdx(v_x_533_);
    lean_dec_ref(v_x_533_);
    return v_res_534_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___redArg(
    mut v_t_535_: *mut LeanObject,
    mut v_k_536_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_535_) == 0 {
        let mut v_x_537_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_538_: *mut LeanObject = core::ptr::null_mut();
        v_x_537_ = lean_ctor_get(v_t_535_, 0);
        lean_inc(v_x_537_);
        lean_dec_ref_known(v_t_535_, 1);
        v___x_538_ = lean_apply_1(v_k_536_, v_x_537_);
        return v___x_538_;
    } else {
        let mut v_lhs_539_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_540_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_541_: *mut LeanObject = core::ptr::null_mut();
        v_lhs_539_ = lean_ctor_get(v_t_535_, 0);
        lean_inc_ref(v_lhs_539_);
        v_rhs_540_ = lean_ctor_get(v_t_535_, 1);
        lean_inc_ref(v_rhs_540_);
        lean_dec_ref_known(v_t_535_, 2);
        v___x_541_ = lean_apply_2(v_k_536_, v_lhs_539_, v_rhs_540_);
        return v___x_541_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim(
    mut v_motive_542_: *mut LeanObject,
    mut v_ctorIdx_543_: *mut LeanObject,
    mut v_t_544_: *mut LeanObject,
    mut v_h_545_: *mut LeanObject,
    mut v_k_546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
    v___x_547_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_544_, v_k_546_);
    return v___x_547_;
}
pub unsafe fn l_Lean_Data_AC_Expr_ctorElim___boxed(
    mut v_motive_548_: *mut LeanObject,
    mut v_ctorIdx_549_: *mut LeanObject,
    mut v_t_550_: *mut LeanObject,
    mut v_h_551_: *mut LeanObject,
    mut v_k_552_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_553_: *mut LeanObject = core::ptr::null_mut();
    v_res_553_ =
        l_Lean_Data_AC_Expr_ctorElim(v_motive_548_, v_ctorIdx_549_, v_t_550_, v_h_551_, v_k_552_);
    lean_dec(v_ctorIdx_549_);
    return v_res_553_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim___redArg(
    mut v_t_554_: *mut LeanObject,
    mut v_var_555_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
    v___x_556_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_554_, v_var_555_);
    return v___x_556_;
}
pub unsafe fn l_Lean_Data_AC_Expr_var_elim(
    mut v_motive_557_: *mut LeanObject,
    mut v_t_558_: *mut LeanObject,
    mut v_h_559_: *mut LeanObject,
    mut v_var_560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_561_: *mut LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_558_, v_var_560_);
    return v___x_561_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim___redArg(
    mut v_t_562_: *mut LeanObject,
    mut v_op_563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_564_: *mut LeanObject = core::ptr::null_mut();
    v___x_564_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_562_, v_op_563_);
    return v___x_564_;
}
pub unsafe fn l_Lean_Data_AC_Expr_op_elim(
    mut v_motive_565_: *mut LeanObject,
    mut v_t_566_: *mut LeanObject,
    mut v_h_567_: *mut LeanObject,
    mut v_op_568_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = l_Lean_Data_AC_Expr_ctorElim___redArg(v_t_566_, v_op_568_);
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__3() -> *mut LeanObject {
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    v___x_580_ = lean_unsigned_to_nat(2);
    v___x_581_ = lean_nat_to_int(v___x_580_);
    return v___x_581_;
}
pub unsafe fn _init_l_Lean_Data_AC_instReprExpr_repr___closed__4() -> *mut LeanObject {
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_583_: *mut LeanObject = core::ptr::null_mut();
    v___x_582_ = lean_unsigned_to_nat(1);
    v___x_583_ = lean_nat_to_int(v___x_582_);
    return v___x_583_;
}
pub unsafe fn l_Lean_Data_AC_instReprExpr_repr(
    mut v_x_590_: *mut LeanObject,
    mut v_prec_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_595_: u8 = 0;
    let mut v___y_597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_612_: u8 = 0;
    let mut v_lhs_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_617_: u8 = 0;
    let mut v___x_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_630_: u8 = 0;
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: u8 = 0;
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_637_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_590_) == 0 {
                    v_x_592_ = lean_ctor_get(v_x_590_, 0);
                    v_isSharedCheck_612_ = (!lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_612_ == 0 {
                        v___x_594_ = v_x_590_;
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_592_);
                        lean_dec(v_x_590_);
                        v___x_594_ = lean_box(0);
                        v_isShared_595_ = v_isSharedCheck_612_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_613_ = lean_ctor_get(v_x_590_, 0);
                    v_rhs_614_ = lean_ctor_get(v_x_590_, 1);
                    v_isSharedCheck_637_ = (!lean_is_exclusive(v_x_590_)) as u8;
                    if v_isSharedCheck_637_ == 0 {
                        v___x_616_ = v_x_590_;
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_rhs_614_);
                        lean_inc(v_lhs_613_);
                        lean_dec(v_x_590_);
                        v___x_616_ = lean_box(0);
                        v_isShared_617_ = v_isSharedCheck_637_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_608_ = lean_unsigned_to_nat(1024);
                v___x_609_ = lean_nat_dec_le(v___x_608_, v_prec_591_);
                if v___x_609_ == 0 {
                    v___x_610_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_597_ = v___x_610_;
                    state = 2;
                    continue;
                } else {
                    v___x_611_ = lean_obj_once(
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
                    lean_ctor_set_tag(v___x_594_, 3);
                    lean_ctor_set(v___x_594_, 0, v___x_599_);
                    v___x_601_ = v___x_594_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_607_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_607_, 0, v___x_599_);
                    v___x_601_ = v_reuseFailAlloc_607_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_602_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_602_, 0, v___x_598_);
                lean_ctor_set(v___x_602_, 1, v___x_601_);
                lean_inc(v___y_597_);
                v___x_603_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_603_, 0, v___y_597_);
                lean_ctor_set(v___x_603_, 1, v___x_602_);
                v___x_604_ = 0;
                v___x_605_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_605_, 0, v___x_603_);
                lean_ctor_set_uint8(
                    v___x_605_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_604_,
                );
                v___x_606_ = l_Repr_addAppParen(v___x_605_, v_prec_591_);
                return v___x_606_;
            }
            4 => {
                v___x_618_ = lean_unsigned_to_nat(1024);
                v___x_634_ = lean_nat_dec_le(v___x_618_, v_prec_591_);
                if v___x_634_ == 0 {
                    v___x_635_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Data_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Data_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_620_ = v___x_635_;
                    state = 5;
                    continue;
                } else {
                    v___x_636_ = lean_obj_once(
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
                v___x_621_ = lean_box(1);
                v___x_622_ = l_Lean_Data_AC_instReprExpr_repr___closed__7;
                v___x_623_ = l_Lean_Data_AC_instReprExpr_repr(v_lhs_613_, v___x_618_);
                if v_isShared_617_ == 0 {
                    lean_ctor_set_tag(v___x_616_, 5);
                    lean_ctor_set(v___x_616_, 1, v___x_623_);
                    lean_ctor_set(v___x_616_, 0, v___x_622_);
                    v___x_625_ = v___x_616_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_633_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_633_, 0, v___x_622_);
                    lean_ctor_set(v_reuseFailAlloc_633_, 1, v___x_623_);
                    v___x_625_ = v_reuseFailAlloc_633_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_626_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_626_, 0, v___x_625_);
                lean_ctor_set(v___x_626_, 1, v___x_621_);
                v___x_627_ = l_Lean_Data_AC_instReprExpr_repr(v_rhs_614_, v___x_618_);
                v___x_628_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_628_, 0, v___x_626_);
                lean_ctor_set(v___x_628_, 1, v___x_627_);
                lean_inc(v___y_620_);
                v___x_629_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_629_, 0, v___y_620_);
                lean_ctor_set(v___x_629_, 1, v___x_628_);
                v___x_630_ = 0;
                v___x_631_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_631_, 0, v___x_629_);
                lean_ctor_set_uint8(
                    v___x_631_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
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
    mut v_x_638_: *mut LeanObject,
    mut v_prec_639_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_640_: *mut LeanObject = core::ptr::null_mut();
    v_res_640_ = l_Lean_Data_AC_instReprExpr_repr(v_x_638_, v_prec_639_);
    lean_dec(v_prec_639_);
    return v_res_640_;
}
pub unsafe fn l_Lean_Data_AC_instBEqExpr_beq(
    mut v_x_643_: *mut LeanObject,
    mut v_x_644_: *mut LeanObject,
) -> u8 {
    let mut v_x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: u8 = 0;
    let mut v___x_648_: u8 = 0;
    let mut v_lhs_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_655_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_643_) == 0 {
                    if lean_obj_tag(v_x_644_) == 0 {
                        v_x_645_ = lean_ctor_get(v_x_643_, 0);
                        v_x_646_ = lean_ctor_get(v_x_644_, 0);
                        v___x_647_ = lean_nat_dec_eq(v_x_645_, v_x_646_);
                        return v___x_647_;
                    } else {
                        v___x_648_ = 0;
                        return v___x_648_;
                    }
                } else {
                    if lean_obj_tag(v_x_644_) == 1 {
                        v_lhs_649_ = lean_ctor_get(v_x_643_, 0);
                        v_rhs_650_ = lean_ctor_get(v_x_643_, 1);
                        v_lhs_651_ = lean_ctor_get(v_x_644_, 0);
                        v_rhs_652_ = lean_ctor_get(v_x_644_, 1);
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
    mut v_x_656_: *mut LeanObject,
    mut v_x_657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_658_: u8 = 0;
    let mut v_r_659_: *mut LeanObject = core::ptr::null_mut();
    v_res_658_ = l_Lean_Data_AC_instBEqExpr_beq(v_x_656_, v_x_657_);
    lean_dec_ref(v_x_657_);
    lean_dec_ref(v_x_656_);
    v_r_659_ = lean_box((v_res_658_) as usize);
    return v_r_659_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg(
    mut v_ctx_662_: *mut LeanObject,
    mut v_idx_663_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arbitrary_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    v_vars_664_ = lean_ctor_get(v_ctx_662_, 3);
    v_arbitrary_665_ = lean_ctor_get(v_ctx_662_, 4);
    v___x_666_ = l_List_get_x3fInternal___redArg(v_vars_664_, v_idx_663_);
    if lean_obj_tag(v___x_666_) == 0 {
        let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
        v___x_667_ = lean_box(0);
        lean_inc(v_arbitrary_665_);
        v___x_668_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_668_, 0, v_arbitrary_665_);
        lean_ctor_set(v___x_668_, 1, v___x_667_);
        return v___x_668_;
    } else {
        let mut v_val_669_: *mut LeanObject = core::ptr::null_mut();
        v_val_669_ = lean_ctor_get(v___x_666_, 0);
        lean_inc(v_val_669_);
        lean_dec_ref_known(v___x_666_, 1);
        return v_val_669_;
    }
}
pub unsafe fn l_Lean_Data_AC_Context_var___redArg___boxed(
    mut v_ctx_670_: *mut LeanObject,
    mut v_idx_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_672_: *mut LeanObject = core::ptr::null_mut();
    v_res_672_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_670_, v_idx_671_);
    lean_dec_ref(v_ctx_670_);
    return v_res_672_;
}
pub unsafe fn l_Lean_Data_AC_Context_var(
    mut v_00_u03b1_673_: *mut LeanObject,
    mut v_ctx_674_: *mut LeanObject,
    mut v_idx_675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    v___x_676_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_674_, v_idx_675_);
    return v___x_676_;
}
pub unsafe fn l_Lean_Data_AC_Context_var___boxed(
    mut v_00_u03b1_677_: *mut LeanObject,
    mut v_ctx_678_: *mut LeanObject,
    mut v_idx_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ = l_Lean_Data_AC_Context_var(v_00_u03b1_677_, v_ctx_678_, v_idx_679_);
    lean_dec_ref(v_ctx_678_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0(
    mut v_ctx_681_: *mut LeanObject,
    mut v_x_682_: *mut LeanObject,
) -> u8 {
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_neutral_684_: *mut LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_681_, v_x_682_);
    v_neutral_684_ = lean_ctor_get(v___x_683_, 1);
    lean_inc(v_neutral_684_);
    lean_dec_ref(v___x_683_);
    if lean_obj_tag(v_neutral_684_) == 0 {
        let mut v___x_685_: u8 = 0;
        v___x_685_ = 0;
        return v___x_685_;
    } else {
        let mut v___x_686_: u8 = 0;
        lean_dec_ref_known(v_neutral_684_, 1);
        v___x_686_ = 1;
        return v___x_686_;
    }
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__0___boxed(
    mut v_ctx_687_: *mut LeanObject,
    mut v_x_688_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_689_: u8 = 0;
    let mut v_r_690_: *mut LeanObject = core::ptr::null_mut();
    v_res_689_ = l_Lean_Data_AC_instContextInformationContext___lam__0(v_ctx_687_, v_x_688_);
    lean_dec_ref(v_ctx_687_);
    v_r_690_ = lean_box((v_res_689_) as usize);
    return v_r_690_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__1(
    mut v_ctx_691_: *mut LeanObject,
) -> u8 {
    let mut v_comm_692_: *mut LeanObject = core::ptr::null_mut();
    v_comm_692_ = lean_ctor_get(v_ctx_691_, 1);
    if lean_obj_tag(v_comm_692_) == 0 {
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
    mut v_ctx_695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_696_: u8 = 0;
    let mut v_r_697_: *mut LeanObject = core::ptr::null_mut();
    v_res_696_ = l_Lean_Data_AC_instContextInformationContext___lam__1(v_ctx_695_);
    lean_dec_ref(v_ctx_695_);
    v_r_697_ = lean_box((v_res_696_) as usize);
    return v_r_697_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext___lam__2(
    mut v_ctx_698_: *mut LeanObject,
) -> u8 {
    let mut v_idem_699_: *mut LeanObject = core::ptr::null_mut();
    v_idem_699_ = lean_ctor_get(v_ctx_698_, 2);
    if lean_obj_tag(v_idem_699_) == 0 {
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
    mut v_ctx_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_703_: u8 = 0;
    let mut v_r_704_: *mut LeanObject = core::ptr::null_mut();
    v_res_703_ = l_Lean_Data_AC_instContextInformationContext___lam__2(v_ctx_702_);
    lean_dec_ref(v_ctx_702_);
    v_r_704_ = lean_box((v_res_703_) as usize);
    return v_r_704_;
}
pub unsafe fn l_Lean_Data_AC_instContextInformationContext(
    mut v_00_u03b1_712_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    v___x_713_ = l_Lean_Data_AC_instContextInformationContext___closed__3;
    return v___x_713_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0(
    mut v_ctx_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_arbitrary_715_: *mut LeanObject = core::ptr::null_mut();
    v_arbitrary_715_ = lean_ctor_get(v_ctx_714_, 4);
    lean_inc(v_arbitrary_715_);
    return v_arbitrary_715_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__0___boxed(
    mut v_ctx_716_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_717_: *mut LeanObject = core::ptr::null_mut();
    v_res_717_ = l_Lean_Data_AC_instEvalInformationContext___lam__0(v_ctx_716_);
    lean_dec_ref(v_ctx_716_);
    return v_res_717_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__1(
    mut v_ctx_718_: *mut LeanObject,
    mut v___y_719_: *mut LeanObject,
    mut v___y_720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_op_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v_op_721_ = lean_ctor_get(v_ctx_718_, 0);
    lean_inc(v_op_721_);
    lean_dec_ref(v_ctx_718_);
    v___x_722_ = lean_apply_2(v_op_721_, v___y_719_, v___y_720_);
    return v___x_722_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2(
    mut v_ctx_723_: *mut LeanObject,
    mut v_idx_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_726_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_Data_AC_Context_var___redArg(v_ctx_723_, v_idx_724_);
    v_value_726_ = lean_ctor_get(v___x_725_, 0);
    lean_inc(v_value_726_);
    lean_dec_ref(v___x_725_);
    return v_value_726_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext___lam__2___boxed(
    mut v_ctx_727_: *mut LeanObject,
    mut v_idx_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_729_ = l_Lean_Data_AC_instEvalInformationContext___lam__2(v_ctx_727_, v_idx_728_);
    lean_dec_ref(v_ctx_727_);
    return v_res_729_;
}
pub unsafe fn l_Lean_Data_AC_instEvalInformationContext(
    mut v_00_u03b1_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_738_: *mut LeanObject = core::ptr::null_mut();
    v___x_738_ = l_Lean_Data_AC_instEvalInformationContext___closed__3;
    return v___x_738_;
}
pub unsafe fn l_Lean_Data_AC_eval___redArg(
    mut v_inst_739_: *mut LeanObject,
    mut v_ctx_740_: *mut LeanObject,
    mut v_x_741_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_741_) == 0 {
        let mut v_x_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v_evalVar_743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
        v_x_742_ = lean_ctor_get(v_x_741_, 0);
        lean_inc(v_x_742_);
        lean_dec_ref_known(v_x_741_, 1);
        v_evalVar_743_ = lean_ctor_get(v_inst_739_, 2);
        lean_inc(v_evalVar_743_);
        lean_dec_ref(v_inst_739_);
        v___x_744_ = lean_apply_2(v_evalVar_743_, v_ctx_740_, v_x_742_);
        return v___x_744_;
    } else {
        let mut v_lhs_745_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_746_: *mut LeanObject = core::ptr::null_mut();
        let mut v_evalOp_747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
        v_lhs_745_ = lean_ctor_get(v_x_741_, 0);
        lean_inc_ref(v_lhs_745_);
        v_rhs_746_ = lean_ctor_get(v_x_741_, 1);
        lean_inc_ref(v_rhs_746_);
        lean_dec_ref_known(v_x_741_, 2);
        v_evalOp_747_ = lean_ctor_get(v_inst_739_, 1);
        lean_inc(v_evalOp_747_);
        lean_inc_n(v_ctx_740_, 2);
        lean_inc_ref(v_inst_739_);
        v___x_748_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_lhs_745_);
        v___x_749_ = l_Lean_Data_AC_eval___redArg(v_inst_739_, v_ctx_740_, v_rhs_746_);
        v___x_750_ = lean_apply_3(v_evalOp_747_, v_ctx_740_, v___x_748_, v___x_749_);
        return v___x_750_;
    }
}
pub unsafe fn l_Lean_Data_AC_eval(
    mut v_00_u03b1_751_: *mut LeanObject,
    mut v_00_u03b2_752_: *mut LeanObject,
    mut v_inst_753_: *mut LeanObject,
    mut v_ctx_754_: *mut LeanObject,
    mut v_x_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ = l_Lean_Data_AC_eval___redArg(v_inst_753_, v_ctx_754_, v_x_755_);
    return v___x_756_;
}
pub unsafe fn l_Lean_Data_AC_Expr_toList(mut v_x_757_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_757_) == 0 {
        let mut v_x_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
        v_x_758_ = lean_ctor_get(v_x_757_, 0);
        v___x_759_ = lean_box(0);
        lean_inc(v_x_758_);
        v___x_760_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_760_, 0, v_x_758_);
        lean_ctor_set(v___x_760_, 1, v___x_759_);
        return v___x_760_;
    } else {
        let mut v_lhs_761_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
        v_lhs_761_ = lean_ctor_get(v_x_757_, 0);
        v_rhs_762_ = lean_ctor_get(v_x_757_, 1);
        v___x_763_ = l_Lean_Data_AC_Expr_toList(v_lhs_761_);
        v___x_764_ = l_Lean_Data_AC_Expr_toList(v_rhs_762_);
        v___x_765_ = l_List_appendTR___redArg(v___x_763_, v___x_764_);
        return v___x_765_;
    }
}
pub unsafe fn l_Lean_Data_AC_Expr_toList___boxed(mut v_x_766_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_767_: *mut LeanObject = core::ptr::null_mut();
    v_res_767_ = l_Lean_Data_AC_Expr_toList(v_x_766_);
    lean_dec_ref(v_x_766_);
    return v_res_767_;
}
pub unsafe fn l_Lean_Data_AC_evalList___redArg(
    mut v_inst_768_: *mut LeanObject,
    mut v_ctx_769_: *mut LeanObject,
    mut v_x_770_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_770_) == 0 {
        let mut v_arbitrary_771_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
        v_arbitrary_771_ = lean_ctor_get(v_inst_768_, 0);
        lean_inc(v_arbitrary_771_);
        lean_dec_ref(v_inst_768_);
        v___x_772_ = lean_apply_1(v_arbitrary_771_, v_ctx_769_);
        return v___x_772_;
    } else {
        let mut v_tail_773_: *mut LeanObject = core::ptr::null_mut();
        v_tail_773_ = lean_ctor_get(v_x_770_, 1);
        if lean_obj_tag(v_tail_773_) == 0 {
            let mut v_head_774_: *mut LeanObject = core::ptr::null_mut();
            let mut v_evalVar_775_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
            v_head_774_ = lean_ctor_get(v_x_770_, 0);
            lean_inc(v_head_774_);
            lean_dec_ref_known(v_x_770_, 2);
            v_evalVar_775_ = lean_ctor_get(v_inst_768_, 2);
            lean_inc(v_evalVar_775_);
            lean_dec_ref(v_inst_768_);
            v___x_776_ = lean_apply_2(v_evalVar_775_, v_ctx_769_, v_head_774_);
            return v___x_776_;
        } else {
            let mut v_head_777_: *mut LeanObject = core::ptr::null_mut();
            let mut v_evalOp_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v_evalVar_779_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_773_);
            v_head_777_ = lean_ctor_get(v_x_770_, 0);
            lean_inc(v_head_777_);
            lean_dec_ref_known(v_x_770_, 2);
            v_evalOp_778_ = lean_ctor_get(v_inst_768_, 1);
            lean_inc(v_evalOp_778_);
            v_evalVar_779_ = lean_ctor_get(v_inst_768_, 2);
            lean_inc(v_evalVar_779_);
            lean_inc_n(v_ctx_769_, 2);
            v___x_780_ = lean_apply_2(v_evalVar_779_, v_ctx_769_, v_head_777_);
            v___x_781_ = l_Lean_Data_AC_evalList___redArg(v_inst_768_, v_ctx_769_, v_tail_773_);
            v___x_782_ = lean_apply_3(v_evalOp_778_, v_ctx_769_, v___x_780_, v___x_781_);
            return v___x_782_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_evalList(
    mut v_00_u03b1_783_: *mut LeanObject,
    mut v_00_u03b2_784_: *mut LeanObject,
    mut v_inst_785_: *mut LeanObject,
    mut v_ctx_786_: *mut LeanObject,
    mut v_x_787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    v___x_788_ = l_Lean_Data_AC_evalList___redArg(v_inst_785_, v_ctx_786_, v_x_787_);
    return v___x_788_;
}
pub unsafe fn l_Lean_Data_AC_insert(
    mut v_x_789_: *mut LeanObject,
    mut v_x_790_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: u8 = 0;
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_797_: u8 = 0;
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_802_: u8 = 0;
    let mut v_unused_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_790_) == 0 {
                    v___x_791_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_791_, 0, v_x_789_);
                    lean_ctor_set(v___x_791_, 1, v_x_790_);
                    return v___x_791_;
                } else {
                    v_head_792_ = lean_ctor_get(v_x_790_, 0);
                    v_tail_793_ = lean_ctor_get(v_x_790_, 1);
                    v___x_794_ = lean_nat_dec_lt(v_x_789_, v_head_792_);
                    if v___x_794_ == 0 {
                        lean_inc(v_tail_793_);
                        lean_inc(v_head_792_);
                        v_isSharedCheck_802_ = (!lean_is_exclusive(v_x_790_)) as u8;
                        if v_isSharedCheck_802_ == 0 {
                            v_unused_803_ = lean_ctor_get(v_x_790_, 1);
                            lean_dec(v_unused_803_);
                            v_unused_804_ = lean_ctor_get(v_x_790_, 0);
                            lean_dec(v_unused_804_);
                            v___x_796_ = v_x_790_;
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_790_);
                            v___x_796_ = lean_box(0);
                            v_isShared_797_ = v_isSharedCheck_802_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_805_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_805_, 0, v_x_789_);
                        lean_ctor_set(v___x_805_, 1, v_x_790_);
                        return v___x_805_;
                    }
                }
            }
            1 => {
                v___x_798_ = l_Lean_Data_AC_insert(v_x_789_, v_tail_793_);
                if v_isShared_797_ == 0 {
                    lean_ctor_set(v___x_796_, 1, v___x_798_);
                    v___x_800_ = v___x_796_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_801_, 0, v_head_792_);
                    lean_ctor_set(v_reuseFailAlloc_801_, 1, v___x_798_);
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
    mut v_a_806_: *mut LeanObject,
    mut v_a_807_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_807_) == 0 {
                    return v_a_806_;
                } else {
                    v_head_808_ = lean_ctor_get(v_a_807_, 0);
                    lean_inc(v_head_808_);
                    v_tail_809_ = lean_ctor_get(v_a_807_, 1);
                    lean_inc(v_tail_809_);
                    lean_dec_ref_known(v_a_807_, 2);
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
pub unsafe fn l_Lean_Data_AC_sort(mut v_xs_812_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    v___x_813_ = lean_box(0);
    v___x_814_ = l_Lean_Data_AC_sort_loop(v___x_813_, v_xs_812_);
    return v___x_814_;
}
pub unsafe fn l_Lean_Data_AC_mergeIdem_loop(
    mut v_a_815_: *mut LeanObject,
    mut v_a_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_822_: u8 = 0;
    let mut v___x_823_: u8 = 0;
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_816_) == 0 {
                    v___x_817_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_817_, 0, v_a_815_);
                    lean_ctor_set(v___x_817_, 1, v_a_816_);
                    return v___x_817_;
                } else {
                    v_head_818_ = lean_ctor_get(v_a_816_, 0);
                    v_tail_819_ = lean_ctor_get(v_a_816_, 1);
                    v_isSharedCheck_829_ = (!lean_is_exclusive(v_a_816_)) as u8;
                    if v_isSharedCheck_829_ == 0 {
                        v___x_821_ = v_a_816_;
                        v_isShared_822_ = v_isSharedCheck_829_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_819_);
                        lean_inc(v_head_818_);
                        lean_dec(v_a_816_);
                        v___x_821_ = lean_box(0);
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
                        lean_ctor_set(v___x_821_, 1, v___x_824_);
                        lean_ctor_set(v___x_821_, 0, v_a_815_);
                        v___x_826_ = v___x_821_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_827_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_827_, 0, v_a_815_);
                        lean_ctor_set(v_reuseFailAlloc_827_, 1, v___x_824_);
                        v___x_826_ = v_reuseFailAlloc_827_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_821_);
                    lean_dec(v_head_818_);
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
pub unsafe fn l_Lean_Data_AC_mergeIdem(mut v_xs_830_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_xs_830_) == 0 {
        return v_xs_830_;
    } else {
        let mut v_head_831_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_832_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
        v_head_831_ = lean_ctor_get(v_xs_830_, 0);
        lean_inc(v_head_831_);
        v_tail_832_ = lean_ctor_get(v_xs_830_, 1);
        lean_inc(v_tail_832_);
        lean_dec_ref_known(v_xs_830_, 2);
        v___x_833_ = l_Lean_Data_AC_mergeIdem_loop(v_head_831_, v_tail_832_);
        return v___x_833_;
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals_loop___redArg(
    mut v_info_834_: *mut LeanObject,
    mut v_ctx_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v_isNeutral_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_850_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_836_) == 0 {
                    lean_dec(v_ctx_835_);
                    lean_dec_ref(v_info_834_);
                    return v_a_836_;
                } else {
                    v_head_837_ = lean_ctor_get(v_a_836_, 0);
                    v_tail_838_ = lean_ctor_get(v_a_836_, 1);
                    v_isSharedCheck_850_ = (!lean_is_exclusive(v_a_836_)) as u8;
                    if v_isSharedCheck_850_ == 0 {
                        v___x_840_ = v_a_836_;
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_838_);
                        lean_inc(v_head_837_);
                        lean_dec(v_a_836_);
                        v___x_840_ = lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_850_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_isNeutral_842_ = lean_ctor_get(v_info_834_, 0);
                lean_inc_ref(v_isNeutral_842_);
                lean_inc(v_head_837_);
                lean_inc(v_ctx_835_);
                v___x_843_ = lean_apply_2(v_isNeutral_842_, v_ctx_835_, v_head_837_);
                v___x_844_ = (lean_unbox(v___x_843_) as u8);
                if v___x_844_ == 0 {
                    v___x_845_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(
                        v_info_834_,
                        v_ctx_835_,
                        v_tail_838_,
                    );
                    if v_isShared_841_ == 0 {
                        lean_ctor_set(v___x_840_, 1, v___x_845_);
                        v___x_847_ = v___x_840_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_848_, 0, v_head_837_);
                        lean_ctor_set(v_reuseFailAlloc_848_, 1, v___x_845_);
                        v___x_847_ = v_reuseFailAlloc_848_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_840_);
                    lean_dec(v_head_837_);
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
    mut v_00_u03b1_851_: *mut LeanObject,
    mut v_info_852_: *mut LeanObject,
    mut v_ctx_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    v___x_855_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_852_, v_ctx_853_, v_a_854_);
    return v___x_855_;
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals___redArg(
    mut v_info_856_: *mut LeanObject,
    mut v_ctx_857_: *mut LeanObject,
    mut v_x_858_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_858_) == 0 {
        lean_dec(v_ctx_857_);
        lean_dec_ref(v_info_856_);
        return v_x_858_;
    } else {
        let mut v_head_859_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
        v_head_859_ = lean_ctor_get(v_x_858_, 0);
        lean_inc(v_head_859_);
        v___x_860_ = l_Lean_Data_AC_removeNeutrals_loop___redArg(v_info_856_, v_ctx_857_, v_x_858_);
        if lean_obj_tag(v___x_860_) == 0 {
            let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
            v___x_861_ = lean_alloc_ctor(1, 2, (0) as u32);
            lean_ctor_set(v___x_861_, 0, v_head_859_);
            lean_ctor_set(v___x_861_, 1, v___x_860_);
            return v___x_861_;
        } else {
            lean_dec(v_head_859_);
            return v___x_860_;
        }
    }
}
pub unsafe fn l_Lean_Data_AC_removeNeutrals(
    mut v_00_u03b1_862_: *mut LeanObject,
    mut v_info_863_: *mut LeanObject,
    mut v_ctx_864_: *mut LeanObject,
    mut v_x_865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    v___x_866_ = l_Lean_Data_AC_removeNeutrals___redArg(v_info_863_, v_ctx_864_, v_x_865_);
    return v___x_866_;
}
pub unsafe fn l_Lean_Data_AC_norm___redArg(
    mut v_info_867_: *mut LeanObject,
    mut v_ctx_868_: *mut LeanObject,
    mut v_e_869_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isComm_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isIdem_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_875_: u8 = 0;
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_isComm_870_ = lean_ctor_get(v_info_867_, 1);
                lean_inc_ref(v_isComm_870_);
                v_isIdem_871_ = lean_ctor_get(v_info_867_, 2);
                lean_inc_ref(v_isIdem_871_);
                v_xs_877_ = l_Lean_Data_AC_Expr_toList(v_e_869_);
                lean_inc_n(v_ctx_868_, 2);
                v_xs_878_ =
                    l_Lean_Data_AC_removeNeutrals___redArg(v_info_867_, v_ctx_868_, v_xs_877_);
                v___x_879_ = lean_apply_1(v_isComm_870_, v_ctx_868_);
                v___x_880_ = (lean_unbox(v___x_879_) as u8);
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
                v___x_874_ = lean_apply_1(v_isIdem_871_, v_ctx_868_);
                v___x_875_ = (lean_unbox(v___x_874_) as u8);
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
    mut v_info_882_: *mut LeanObject,
    mut v_ctx_883_: *mut LeanObject,
    mut v_e_884_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_885_: *mut LeanObject = core::ptr::null_mut();
    v_res_885_ = l_Lean_Data_AC_norm___redArg(v_info_882_, v_ctx_883_, v_e_884_);
    lean_dec_ref(v_e_884_);
    return v_res_885_;
}
pub unsafe fn l_Lean_Data_AC_norm(
    mut v_00_u03b1_886_: *mut LeanObject,
    mut v_info_887_: *mut LeanObject,
    mut v_ctx_888_: *mut LeanObject,
    mut v_e_889_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = l_Lean_Data_AC_norm___redArg(v_info_887_, v_ctx_888_, v_e_889_);
    return v___x_890_;
}
pub unsafe fn l_Lean_Data_AC_norm___boxed(
    mut v_00_u03b1_891_: *mut LeanObject,
    mut v_info_892_: *mut LeanObject,
    mut v_ctx_893_: *mut LeanObject,
    mut v_e_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ = l_Lean_Data_AC_norm(v_00_u03b1_891_, v_info_892_, v_ctx_893_, v_e_894_);
    lean_dec_ref(v_e_894_);
    return v_res_895_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter___redArg(
    mut v_x_896_: *mut LeanObject,
    mut v_h__1_897_: *mut LeanObject,
    mut v_h__2_898_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_896_) == 0 {
        let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_898_);
        v___x_899_ = lean_box(0);
        v___x_900_ = lean_apply_1(v_h__1_897_, v___x_899_);
        return v___x_900_;
    } else {
        let mut v_head_901_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_902_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_897_);
        v_head_901_ = lean_ctor_get(v_x_896_, 0);
        lean_inc(v_head_901_);
        v_tail_902_ = lean_ctor_get(v_x_896_, 1);
        lean_inc(v_tail_902_);
        lean_dec_ref_known(v_x_896_, 2);
        v___x_903_ = lean_apply_2(v_h__2_898_, v_head_901_, v_tail_902_);
        return v___x_903_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_insert_match__1_splitter(
    mut v_motive_904_: *mut LeanObject,
    mut v_x_905_: *mut LeanObject,
    mut v_h__1_906_: *mut LeanObject,
    mut v_h__2_907_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_905_) == 0 {
        let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_907_);
        v___x_908_ = lean_box(0);
        v___x_909_ = lean_apply_1(v_h__1_906_, v___x_908_);
        return v___x_909_;
    } else {
        let mut v_head_910_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_911_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_906_);
        v_head_910_ = lean_ctor_get(v_x_905_, 0);
        lean_inc(v_head_910_);
        v_tail_911_ = lean_ctor_get(v_x_905_, 1);
        lean_inc(v_tail_911_);
        lean_dec_ref_known(v_x_905_, 2);
        v___x_912_ = lean_apply_2(v_h__2_907_, v_head_910_, v_tail_911_);
        return v___x_912_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter___redArg(
    mut v_x_913_: *mut LeanObject,
    mut v_x_914_: *mut LeanObject,
    mut v_h__1_915_: *mut LeanObject,
    mut v_h__2_916_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_914_) == 0 {
        let mut v___x_917_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_915_);
        v___x_917_ = lean_apply_1(v_h__2_916_, v_x_913_);
        return v___x_917_;
    } else {
        let mut v_head_918_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_919_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_916_);
        v_head_918_ = lean_ctor_get(v_x_914_, 0);
        lean_inc(v_head_918_);
        v_tail_919_ = lean_ctor_get(v_x_914_, 1);
        lean_inc(v_tail_919_);
        lean_dec_ref_known(v_x_914_, 2);
        v___x_920_ = lean_apply_3(v_h__1_915_, v_x_913_, v_head_918_, v_tail_919_);
        return v___x_920_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_mergeIdem_loop_match__1_splitter(
    mut v_motive_921_: *mut LeanObject,
    mut v_x_922_: *mut LeanObject,
    mut v_x_923_: *mut LeanObject,
    mut v_h__1_924_: *mut LeanObject,
    mut v_h__2_925_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_923_) == 0 {
        let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_924_);
        v___x_926_ = lean_apply_1(v_h__2_925_, v_x_922_);
        return v___x_926_;
    } else {
        let mut v_head_927_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_925_);
        v_head_927_ = lean_ctor_get(v_x_923_, 0);
        lean_inc(v_head_927_);
        v_tail_928_ = lean_ctor_get(v_x_923_, 1);
        lean_inc(v_tail_928_);
        lean_dec_ref_known(v_x_923_, 2);
        v___x_929_ = lean_apply_3(v_h__1_924_, v_x_922_, v_head_927_, v_tail_928_);
        return v___x_929_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter___redArg(
    mut v_x_930_: *mut LeanObject,
    mut v_h__1_931_: *mut LeanObject,
    mut v_h__2_932_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_930_) == 0 {
        let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_934_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_931_);
        v___x_933_ = lean_box(0);
        v___x_934_ = lean_apply_1(v_h__2_932_, v___x_933_);
        return v___x_934_;
    } else {
        let mut v_val_935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_932_);
        v_val_935_ = lean_ctor_get(v_x_930_, 0);
        lean_inc(v_val_935_);
        lean_dec_ref_known(v_x_930_, 1);
        v___x_936_ = lean_apply_1(v_h__1_931_, v_val_935_);
        return v___x_936_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Option_isSome_match__1_splitter(
    mut v_00_u03b1_937_: *mut LeanObject,
    mut v_motive_938_: *mut LeanObject,
    mut v_x_939_: *mut LeanObject,
    mut v_h__1_940_: *mut LeanObject,
    mut v_h__2_941_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_939_) == 0 {
        let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_940_);
        v___x_942_ = lean_box(0);
        v___x_943_ = lean_apply_1(v_h__2_941_, v___x_942_);
        return v___x_943_;
    } else {
        let mut v_val_944_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_941_);
        v_val_944_ = lean_ctor_get(v_x_939_, 0);
        lean_inc(v_val_944_);
        lean_dec_ref_known(v_x_939_, 1);
        v___x_945_ = lean_apply_1(v_h__1_940_, v_val_944_);
        return v___x_945_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter___redArg(
    mut v_x_946_: *mut LeanObject,
    mut v_h__1_947_: *mut LeanObject,
    mut v_h__2_948_: *mut LeanObject,
    mut v_h__3_949_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_946_) == 0 {
        let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_949_);
        lean_dec(v_h__2_948_);
        v___x_950_ = lean_box(0);
        v___x_951_ = lean_apply_1(v_h__1_947_, v___x_950_);
        return v___x_951_;
    } else {
        let mut v_tail_952_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_947_);
        v_tail_952_ = lean_ctor_get(v_x_946_, 1);
        if lean_obj_tag(v_tail_952_) == 0 {
            let mut v_head_953_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_949_);
            v_head_953_ = lean_ctor_get(v_x_946_, 0);
            lean_inc(v_head_953_);
            lean_dec_ref_known(v_x_946_, 2);
            v___x_954_ = lean_apply_1(v_h__2_948_, v_head_953_);
            return v___x_954_;
        } else {
            let mut v_head_955_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_952_);
            lean_dec(v_h__2_948_);
            v_head_955_ = lean_ctor_get(v_x_946_, 0);
            lean_inc(v_head_955_);
            lean_dec_ref_known(v_x_946_, 2);
            v___x_956_ = lean_apply_3(v_h__3_949_, v_head_955_, v_tail_952_, lean_box(0));
            return v___x_956_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_evalList_match__1_splitter(
    mut v_motive_957_: *mut LeanObject,
    mut v_x_958_: *mut LeanObject,
    mut v_h__1_959_: *mut LeanObject,
    mut v_h__2_960_: *mut LeanObject,
    mut v_h__3_961_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_958_) == 0 {
        let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_961_);
        lean_dec(v_h__2_960_);
        v___x_962_ = lean_box(0);
        v___x_963_ = lean_apply_1(v_h__1_959_, v___x_962_);
        return v___x_963_;
    } else {
        let mut v_tail_964_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_959_);
        v_tail_964_ = lean_ctor_get(v_x_958_, 1);
        if lean_obj_tag(v_tail_964_) == 0 {
            let mut v_head_965_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_961_);
            v_head_965_ = lean_ctor_get(v_x_958_, 0);
            lean_inc(v_head_965_);
            lean_dec_ref_known(v_x_958_, 2);
            v___x_966_ = lean_apply_1(v_h__2_960_, v_head_965_);
            return v___x_966_;
        } else {
            let mut v_head_967_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
            lean_inc(v_tail_964_);
            lean_dec(v_h__2_960_);
            v_head_967_ = lean_ctor_get(v_x_958_, 0);
            lean_inc(v_head_967_);
            lean_dec_ref_known(v_x_958_, 2);
            v___x_968_ = lean_apply_3(v_h__3_961_, v_head_967_, v_tail_964_, lean_box(0));
            return v___x_968_;
        }
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter___redArg(
    mut v_x_969_: *mut LeanObject,
    mut v_x_970_: *mut LeanObject,
    mut v_h__1_971_: *mut LeanObject,
    mut v_h__2_972_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_970_) == 0 {
        let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_972_);
        v___x_973_ = lean_apply_1(v_h__1_971_, v_x_969_);
        return v___x_973_;
    } else {
        let mut v_head_974_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_975_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_971_);
        v_head_974_ = lean_ctor_get(v_x_970_, 0);
        lean_inc(v_head_974_);
        v_tail_975_ = lean_ctor_get(v_x_970_, 1);
        lean_inc(v_tail_975_);
        lean_dec_ref_known(v_x_970_, 2);
        v___x_976_ = lean_apply_3(v_h__2_972_, v_x_969_, v_head_974_, v_tail_975_);
        return v___x_976_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_sort_loop_match__1_splitter(
    mut v_motive_977_: *mut LeanObject,
    mut v_x_978_: *mut LeanObject,
    mut v_x_979_: *mut LeanObject,
    mut v_h__1_980_: *mut LeanObject,
    mut v_h__2_981_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_979_) == 0 {
        let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_981_);
        v___x_982_ = lean_apply_1(v_h__1_980_, v_x_978_);
        return v___x_982_;
    } else {
        let mut v_head_983_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_984_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_980_);
        v_head_983_ = lean_ctor_get(v_x_979_, 0);
        lean_inc(v_head_983_);
        v_tail_984_ = lean_ctor_get(v_x_979_, 1);
        lean_inc(v_tail_984_);
        lean_dec_ref_known(v_x_979_, 2);
        v___x_985_ = lean_apply_3(v_h__2_981_, v_x_978_, v_head_983_, v_tail_984_);
        return v___x_985_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter___redArg(
    mut v_x_986_: *mut LeanObject,
    mut v_h__1_987_: *mut LeanObject,
    mut v_h__2_988_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_986_) == 0 {
        let mut v_x_989_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_988_);
        v_x_989_ = lean_ctor_get(v_x_986_, 0);
        lean_inc(v_x_989_);
        lean_dec_ref_known(v_x_986_, 1);
        v___x_990_ = lean_apply_1(v_h__1_987_, v_x_989_);
        return v___x_990_;
    } else {
        let mut v_lhs_991_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_992_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_987_);
        v_lhs_991_ = lean_ctor_get(v_x_986_, 0);
        lean_inc_ref(v_lhs_991_);
        v_rhs_992_ = lean_ctor_get(v_x_986_, 1);
        lean_inc_ref(v_rhs_992_);
        lean_dec_ref_known(v_x_986_, 2);
        v___x_993_ = lean_apply_2(v_h__2_988_, v_lhs_991_, v_rhs_992_);
        return v___x_993_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_eval_match__1_splitter(
    mut v_motive_994_: *mut LeanObject,
    mut v_x_995_: *mut LeanObject,
    mut v_h__1_996_: *mut LeanObject,
    mut v_h__2_997_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_995_) == 0 {
        let mut v_x_998_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_997_);
        v_x_998_ = lean_ctor_get(v_x_995_, 0);
        lean_inc(v_x_998_);
        lean_dec_ref_known(v_x_995_, 1);
        v___x_999_ = lean_apply_1(v_h__1_996_, v_x_998_);
        return v___x_999_;
    } else {
        let mut v_lhs_1000_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_1001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_996_);
        v_lhs_1000_ = lean_ctor_get(v_x_995_, 0);
        lean_inc_ref(v_lhs_1000_);
        v_rhs_1001_ = lean_ctor_get(v_x_995_, 1);
        lean_inc_ref(v_rhs_1001_);
        lean_dec_ref_known(v_x_995_, 2);
        v___x_1002_ = lean_apply_2(v_h__2_997_, v_lhs_1000_, v_rhs_1001_);
        return v___x_1002_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter___redArg(
    mut v_x_1003_: *mut LeanObject,
    mut v_h__1_1004_: *mut LeanObject,
    mut v_h__2_1005_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1003_) == 0 {
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1004_);
        v___x_1006_ = lean_box(0);
        v___x_1007_ = lean_apply_1(v_h__2_1005_, v___x_1006_);
        return v___x_1007_;
    } else {
        let mut v_head_1008_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1009_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1005_);
        v_head_1008_ = lean_ctor_get(v_x_1003_, 0);
        lean_inc(v_head_1008_);
        v_tail_1009_ = lean_ctor_get(v_x_1003_, 1);
        lean_inc(v_tail_1009_);
        lean_dec_ref_known(v_x_1003_, 2);
        v___x_1010_ = lean_apply_2(v_h__1_1004_, v_head_1008_, v_tail_1009_);
        return v___x_1010_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__3_splitter(
    mut v_motive_1011_: *mut LeanObject,
    mut v_x_1012_: *mut LeanObject,
    mut v_h__1_1013_: *mut LeanObject,
    mut v_h__2_1014_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1012_) == 0 {
        let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1013_);
        v___x_1015_ = lean_box(0);
        v___x_1016_ = lean_apply_1(v_h__2_1014_, v___x_1015_);
        return v___x_1016_;
    } else {
        let mut v_head_1017_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1018_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1014_);
        v_head_1017_ = lean_ctor_get(v_x_1012_, 0);
        lean_inc(v_head_1017_);
        v_tail_1018_ = lean_ctor_get(v_x_1012_, 1);
        lean_inc(v_tail_1018_);
        lean_dec_ref_known(v_x_1012_, 2);
        v___x_1019_ = lean_apply_2(v_h__1_1013_, v_head_1017_, v_tail_1018_);
        return v___x_1019_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
    mut v_x_1020_: u8,
    mut v_h__1_1021_: *mut LeanObject,
    mut v_h__2_1022_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1020_ == 0 {
        let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1021_);
        v___x_1023_ = lean_box(0);
        v___x_1024_ = lean_apply_1(v_h__2_1022_, v___x_1023_);
        return v___x_1024_;
    } else {
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1022_);
        v___x_1025_ = lean_box(0);
        v___x_1026_ = lean_apply_1(v_h__1_1021_, v___x_1025_);
        return v___x_1026_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg___boxed(
    mut v_x_1027_: *mut LeanObject,
    mut v_h__1_1028_: *mut LeanObject,
    mut v_h__2_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_26__boxed_1030_: u8 = 0;
    let mut v_res_1031_: *mut LeanObject = core::ptr::null_mut();
    v_x_26__boxed_1030_ = (lean_unbox(v_x_1027_) as u8);
    v_res_1031_ =
        l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___redArg(
            v_x_26__boxed_1030_,
            v_h__1_1028_,
            v_h__2_1029_,
        );
    return v_res_1031_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
    mut v_motive_1032_: *mut LeanObject,
    mut v_x_1033_: u8,
    mut v_h__1_1034_: *mut LeanObject,
    mut v_h__2_1035_: *mut LeanObject,
) -> *mut LeanObject {
    if v_x_1033_ == 0 {
        let mut v___x_1036_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1034_);
        v___x_1036_ = lean_box(0);
        v___x_1037_ = lean_apply_1(v_h__2_1035_, v___x_1036_);
        return v___x_1037_;
    } else {
        let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1039_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1035_);
        v___x_1038_ = lean_box(0);
        v___x_1039_ = lean_apply_1(v_h__1_1034_, v___x_1038_);
        return v___x_1039_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter___boxed(
    mut v_motive_1040_: *mut LeanObject,
    mut v_x_1041_: *mut LeanObject,
    mut v_h__1_1042_: *mut LeanObject,
    mut v_h__2_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_37__boxed_1044_: u8 = 0;
    let mut v_res_1045_: *mut LeanObject = core::ptr::null_mut();
    v_x_37__boxed_1044_ = (lean_unbox(v_x_1041_) as u8);
    v_res_1045_ = l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_loop_match__1_splitter(
        v_motive_1040_,
        v_x_37__boxed_1044_,
        v_h__1_1042_,
        v_h__2_1043_,
    );
    return v_res_1045_;
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter___redArg(
    mut v_x_1046_: *mut LeanObject,
    mut v_h__1_1047_: *mut LeanObject,
    mut v_h__2_1048_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1046_) == 0 {
        let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1048_);
        v___x_1049_ = lean_box(0);
        v___x_1050_ = lean_apply_1(v_h__1_1047_, v___x_1049_);
        return v___x_1050_;
    } else {
        let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1047_);
        v___x_1051_ = lean_apply_2(v_h__2_1048_, v_x_1046_, lean_box(0));
        return v___x_1051_;
    }
}
pub unsafe fn l___private_Init_Data_AC_0__Lean_Data_AC_removeNeutrals_match__1_splitter(
    mut v_motive_1052_: *mut LeanObject,
    mut v_x_1053_: *mut LeanObject,
    mut v_h__1_1054_: *mut LeanObject,
    mut v_h__2_1055_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1053_) == 0 {
        let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1055_);
        v___x_1056_ = lean_box(0);
        v___x_1057_ = lean_apply_1(v_h__1_1054_, v___x_1056_);
        return v___x_1057_;
    } else {
        let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1054_);
        v___x_1058_ = lean_apply_2(v_h__2_1055_, v_x_1053_, lean_box(0));
        return v___x_1058_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_GetElem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_AC(builtin);
}

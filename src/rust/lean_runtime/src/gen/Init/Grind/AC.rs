// Lean compiler output
// Module: Init.Grind.AC
// Imports: Init.Data.Bool Init.LawfulBEqTactics Init.Data.RArray Init.Classical
use crate::r#gen::Init::Classical::{initialize_Init_Classical, runtime_initialize_Init_Classical};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::Data::Repr::{l_Nat_reprFast, l_Repr_addAppParen};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Grind_AC_instInhabitedExpr_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instInhabitedExpr_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instInhabitedExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedExpr_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__0_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 69, 120, 112, 114, 46,
            118, 97, 114, 0,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__1_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__0_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__1_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__2_value) as *mut LeanObject;
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__3: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__4_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__5_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 69, 120, 112, 114, 46,
            111, 112, 0,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__6_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__5_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__6_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr_repr___closed__7_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 5,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__6_value)
                as *mut LeanObject,
            (((1 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_Lean_Grind_AC_instReprExpr_repr___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr_repr___closed__7_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_AC_instReprExpr_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_AC_instReprExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instReprExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instBEqExpr___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_AC_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_AC_instBEqExpr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instBEqExpr: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instBEqExpr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value: LeanCtorObject<1> =
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
static mut l_Lean_Grind_AC_instInhabitedSeq_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instInhabitedSeq_default: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instInhabitedSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instInhabitedSeq_default___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__0_value: LeanStringObject<22> =
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
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 101, 113, 46, 118,
            97, 114, 0,
        ],
    };
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__1_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__0_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__1_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__2_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__1_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__2_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__3_value: LeanStringObject<23> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 23,
        m_capacity: 23,
        m_length: 22,
        m_data: [
            76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 65, 67, 46, 83, 101, 113, 46, 99,
            111, 110, 115, 0,
        ],
    };
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__3_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__4_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__3_value) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__4_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq_repr___closed__5_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 5,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__4_value) as *mut LeanObject,
        (((1 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_Lean_Grind_AC_instReprSeq_repr___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq_repr___closed__5_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instReprSeq___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Grind_AC_instReprSeq_repr___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Grind_AC_instReprSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instReprSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instReprSeq___closed__0_value) as *mut LeanObject;
pub static l_Lean_Grind_AC_instBEqSeq___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Grind_AC_instBEqSeq_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Grind_AC_instBEqSeq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instBEqSeq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_AC_instBEqSeq: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Grind_AC_instBEqSeq___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Grind_AC_hugeFuel: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Grind_AC_Expr_ctorIdx(mut v_x_574_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_574_) == 0 {
        let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
        v___x_575_ = lean_unsigned_to_nat(0);
        return v___x_575_;
    } else {
        let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
        v___x_576_ = lean_unsigned_to_nat(1);
        return v___x_576_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_ctorIdx___boxed(
    mut v_x_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Grind_AC_Expr_ctorIdx(v_x_577_);
    lean_dec_ref(v_x_577_);
    return v_res_578_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_ctorElim___redArg(
    mut v_t_579_: *mut LeanObject,
    mut v_k_580_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_579_) == 0 {
        let mut v_x_581_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
        v_x_581_ = lean_ctor_get(v_t_579_, 0);
        lean_inc(v_x_581_);
        lean_dec_ref_known(v_t_579_, 1);
        v___x_582_ = lean_apply_1(v_k_580_, v_x_581_);
        return v___x_582_;
    } else {
        let mut v_lhs_583_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_584_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_585_: *mut LeanObject = core::ptr::null_mut();
        v_lhs_583_ = lean_ctor_get(v_t_579_, 0);
        lean_inc_ref(v_lhs_583_);
        v_rhs_584_ = lean_ctor_get(v_t_579_, 1);
        lean_inc_ref(v_rhs_584_);
        lean_dec_ref_known(v_t_579_, 2);
        v___x_585_ = lean_apply_2(v_k_580_, v_lhs_583_, v_rhs_584_);
        return v___x_585_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_ctorElim(
    mut v_motive_586_: *mut LeanObject,
    mut v_ctorIdx_587_: *mut LeanObject,
    mut v_t_588_: *mut LeanObject,
    mut v_h_589_: *mut LeanObject,
    mut v_k_590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    v___x_591_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_588_, v_k_590_);
    return v___x_591_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_ctorElim___boxed(
    mut v_motive_592_: *mut LeanObject,
    mut v_ctorIdx_593_: *mut LeanObject,
    mut v_t_594_: *mut LeanObject,
    mut v_h_595_: *mut LeanObject,
    mut v_k_596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_597_: *mut LeanObject = core::ptr::null_mut();
    v_res_597_ =
        l_Lean_Grind_AC_Expr_ctorElim(v_motive_592_, v_ctorIdx_593_, v_t_594_, v_h_595_, v_k_596_);
    lean_dec(v_ctorIdx_593_);
    return v_res_597_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_var_elim___redArg(
    mut v_t_598_: *mut LeanObject,
    mut v_var_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_600_: *mut LeanObject = core::ptr::null_mut();
    v___x_600_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_598_, v_var_599_);
    return v___x_600_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_var_elim(
    mut v_motive_601_: *mut LeanObject,
    mut v_t_602_: *mut LeanObject,
    mut v_h_603_: *mut LeanObject,
    mut v_var_604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_605_: *mut LeanObject = core::ptr::null_mut();
    v___x_605_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_602_, v_var_604_);
    return v___x_605_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_op_elim___redArg(
    mut v_t_606_: *mut LeanObject,
    mut v_op_607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    v___x_608_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_606_, v_op_607_);
    return v___x_608_;
}
pub unsafe fn l_Lean_Grind_AC_Expr_op_elim(
    mut v_motive_609_: *mut LeanObject,
    mut v_t_610_: *mut LeanObject,
    mut v_h_611_: *mut LeanObject,
    mut v_op_612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_613_: *mut LeanObject = core::ptr::null_mut();
    v___x_613_ = l_Lean_Grind_AC_Expr_ctorElim___redArg(v_t_610_, v_op_612_);
    return v___x_613_;
}
pub unsafe fn _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3() -> *mut LeanObject {
    let mut v___x_624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    v___x_624_ = lean_unsigned_to_nat(2);
    v___x_625_ = lean_nat_to_int(v___x_624_);
    return v___x_625_;
}
pub unsafe fn _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4() -> *mut LeanObject {
    let mut v___x_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_627_: *mut LeanObject = core::ptr::null_mut();
    v___x_626_ = lean_unsigned_to_nat(1);
    v___x_627_ = lean_nat_to_int(v___x_626_);
    return v___x_627_;
}
pub unsafe fn l_Lean_Grind_AC_instReprExpr_repr(
    mut v_x_634_: *mut LeanObject,
    mut v_prec_635_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_639_: u8 = 0;
    let mut v___y_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: u8 = 0;
    let mut v___x_649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u8 = 0;
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_656_: u8 = 0;
    let mut v_lhs_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_661_: u8 = 0;
    let mut v___x_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: u8 = 0;
    let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_634_) == 0 {
                    v_x_636_ = lean_ctor_get(v_x_634_, 0);
                    v_isSharedCheck_656_ = (!lean_is_exclusive(v_x_634_)) as u8;
                    if v_isSharedCheck_656_ == 0 {
                        v___x_638_ = v_x_634_;
                        v_isShared_639_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_636_);
                        lean_dec(v_x_634_);
                        v___x_638_ = lean_box(0);
                        v_isShared_639_ = v_isSharedCheck_656_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_657_ = lean_ctor_get(v_x_634_, 0);
                    v_rhs_658_ = lean_ctor_get(v_x_634_, 1);
                    v_isSharedCheck_681_ = (!lean_is_exclusive(v_x_634_)) as u8;
                    if v_isSharedCheck_681_ == 0 {
                        v___x_660_ = v_x_634_;
                        v_isShared_661_ = v_isSharedCheck_681_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_rhs_658_);
                        lean_inc(v_lhs_657_);
                        lean_dec(v_x_634_);
                        v___x_660_ = lean_box(0);
                        v_isShared_661_ = v_isSharedCheck_681_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_652_ = lean_unsigned_to_nat(1024);
                v___x_653_ = lean_nat_dec_le(v___x_652_, v_prec_635_);
                if v___x_653_ == 0 {
                    v___x_654_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_641_ = v___x_654_;
                    state = 2;
                    continue;
                } else {
                    v___x_655_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_641_ = v___x_655_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_642_ = l_Lean_Grind_AC_instReprExpr_repr___closed__2;
                v___x_643_ = l_Nat_reprFast(v_x_636_);
                if v_isShared_639_ == 0 {
                    lean_ctor_set_tag(v___x_638_, 3);
                    lean_ctor_set(v___x_638_, 0, v___x_643_);
                    v___x_645_ = v___x_638_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_643_);
                    v___x_645_ = v_reuseFailAlloc_651_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_646_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_646_, 0, v___x_642_);
                lean_ctor_set(v___x_646_, 1, v___x_645_);
                lean_inc(v___y_641_);
                v___x_647_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_647_, 0, v___y_641_);
                lean_ctor_set(v___x_647_, 1, v___x_646_);
                v___x_648_ = 0;
                v___x_649_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_649_, 0, v___x_647_);
                lean_ctor_set_uint8(
                    v___x_649_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_648_,
                );
                v___x_650_ = l_Repr_addAppParen(v___x_649_, v_prec_635_);
                return v___x_650_;
            }
            4 => {
                v___x_662_ = lean_unsigned_to_nat(1024);
                v___x_678_ = lean_nat_dec_le(v___x_662_, v_prec_635_);
                if v___x_678_ == 0 {
                    v___x_679_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_664_ = v___x_679_;
                    state = 5;
                    continue;
                } else {
                    v___x_680_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_664_ = v___x_680_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_665_ = lean_box(1);
                v___x_666_ = l_Lean_Grind_AC_instReprExpr_repr___closed__7;
                v___x_667_ = l_Lean_Grind_AC_instReprExpr_repr(v_lhs_657_, v___x_662_);
                if v_isShared_661_ == 0 {
                    lean_ctor_set_tag(v___x_660_, 5);
                    lean_ctor_set(v___x_660_, 1, v___x_667_);
                    lean_ctor_set(v___x_660_, 0, v___x_666_);
                    v___x_669_ = v___x_660_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_677_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_666_);
                    lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_667_);
                    v___x_669_ = v_reuseFailAlloc_677_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_670_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_670_, 0, v___x_669_);
                lean_ctor_set(v___x_670_, 1, v___x_665_);
                v___x_671_ = l_Lean_Grind_AC_instReprExpr_repr(v_rhs_658_, v___x_662_);
                v___x_672_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_672_, 0, v___x_670_);
                lean_ctor_set(v___x_672_, 1, v___x_671_);
                lean_inc(v___y_664_);
                v___x_673_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_673_, 0, v___y_664_);
                lean_ctor_set(v___x_673_, 1, v___x_672_);
                v___x_674_ = 0;
                v___x_675_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_675_, 0, v___x_673_);
                lean_ctor_set_uint8(
                    v___x_675_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_674_,
                );
                v___x_676_ = l_Repr_addAppParen(v___x_675_, v_prec_635_);
                return v___x_676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_instReprExpr_repr___boxed(
    mut v_x_682_: *mut LeanObject,
    mut v_prec_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_684_: *mut LeanObject = core::ptr::null_mut();
    v_res_684_ = l_Lean_Grind_AC_instReprExpr_repr(v_x_682_, v_prec_683_);
    lean_dec(v_prec_683_);
    return v_res_684_;
}
pub unsafe fn l_Lean_Grind_AC_instBEqExpr_beq(
    mut v_x_687_: *mut LeanObject,
    mut v_x_688_: *mut LeanObject,
) -> u8 {
    let mut v_x_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: u8 = 0;
    let mut v___x_692_: u8 = 0;
    let mut v_lhs_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut v___x_699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_687_) == 0 {
                    if lean_obj_tag(v_x_688_) == 0 {
                        v_x_689_ = lean_ctor_get(v_x_687_, 0);
                        v_x_690_ = lean_ctor_get(v_x_688_, 0);
                        v___x_691_ = lean_nat_dec_eq(v_x_689_, v_x_690_);
                        return v___x_691_;
                    } else {
                        v___x_692_ = 0;
                        return v___x_692_;
                    }
                } else {
                    if lean_obj_tag(v_x_688_) == 1 {
                        v_lhs_693_ = lean_ctor_get(v_x_687_, 0);
                        v_rhs_694_ = lean_ctor_get(v_x_687_, 1);
                        v_lhs_695_ = lean_ctor_get(v_x_688_, 0);
                        v_rhs_696_ = lean_ctor_get(v_x_688_, 1);
                        v___x_697_ = l_Lean_Grind_AC_instBEqExpr_beq(v_lhs_693_, v_lhs_695_);
                        if v___x_697_ == 0 {
                            return v___x_697_;
                        } else {
                            v_x_687_ = v_rhs_694_;
                            v_x_688_ = v_rhs_696_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_699_ = 0;
                        return v___x_699_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_instBEqExpr_beq___boxed(
    mut v_x_700_: *mut LeanObject,
    mut v_x_701_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_702_: u8 = 0;
    let mut v_r_703_: *mut LeanObject = core::ptr::null_mut();
    v_res_702_ = l_Lean_Grind_AC_instBEqExpr_beq(v_x_700_, v_x_701_);
    lean_dec_ref(v_x_701_);
    lean_dec_ref(v_x_700_);
    v_r_703_ = lean_box((v_res_702_) as usize);
    return v_r_703_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_ctorIdx(mut v_x_706_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_706_) == 0 {
        let mut v___x_707_: *mut LeanObject = core::ptr::null_mut();
        v___x_707_ = lean_unsigned_to_nat(0);
        return v___x_707_;
    } else {
        let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
        v___x_708_ = lean_unsigned_to_nat(1);
        return v___x_708_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_ctorIdx___boxed(
    mut v_x_709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_710_: *mut LeanObject = core::ptr::null_mut();
    v_res_710_ = l_Lean_Grind_AC_Seq_ctorIdx(v_x_709_);
    lean_dec_ref(v_x_709_);
    return v_res_710_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_ctorElim___redArg(
    mut v_t_711_: *mut LeanObject,
    mut v_k_712_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_711_) == 0 {
        let mut v_x_713_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_714_: *mut LeanObject = core::ptr::null_mut();
        v_x_713_ = lean_ctor_get(v_t_711_, 0);
        lean_inc(v_x_713_);
        lean_dec_ref_known(v_t_711_, 1);
        v___x_714_ = lean_apply_1(v_k_712_, v_x_713_);
        return v___x_714_;
    } else {
        let mut v_x_715_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_716_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_717_: *mut LeanObject = core::ptr::null_mut();
        v_x_715_ = lean_ctor_get(v_t_711_, 0);
        lean_inc(v_x_715_);
        v_s_716_ = lean_ctor_get(v_t_711_, 1);
        lean_inc_ref(v_s_716_);
        lean_dec_ref_known(v_t_711_, 2);
        v___x_717_ = lean_apply_2(v_k_712_, v_x_715_, v_s_716_);
        return v___x_717_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_ctorElim(
    mut v_motive_718_: *mut LeanObject,
    mut v_ctorIdx_719_: *mut LeanObject,
    mut v_t_720_: *mut LeanObject,
    mut v_h_721_: *mut LeanObject,
    mut v_k_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    v___x_723_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_720_, v_k_722_);
    return v___x_723_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_ctorElim___boxed(
    mut v_motive_724_: *mut LeanObject,
    mut v_ctorIdx_725_: *mut LeanObject,
    mut v_t_726_: *mut LeanObject,
    mut v_h_727_: *mut LeanObject,
    mut v_k_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_729_: *mut LeanObject = core::ptr::null_mut();
    v_res_729_ =
        l_Lean_Grind_AC_Seq_ctorElim(v_motive_724_, v_ctorIdx_725_, v_t_726_, v_h_727_, v_k_728_);
    lean_dec(v_ctorIdx_725_);
    return v_res_729_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_var_elim___redArg(
    mut v_t_730_: *mut LeanObject,
    mut v_var_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_730_, v_var_731_);
    return v___x_732_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_var_elim(
    mut v_motive_733_: *mut LeanObject,
    mut v_t_734_: *mut LeanObject,
    mut v_h_735_: *mut LeanObject,
    mut v_var_736_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    v___x_737_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_734_, v_var_736_);
    return v___x_737_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_cons_elim___redArg(
    mut v_t_738_: *mut LeanObject,
    mut v_cons_739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_740_: *mut LeanObject = core::ptr::null_mut();
    v___x_740_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_738_, v_cons_739_);
    return v___x_740_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_cons_elim(
    mut v_motive_741_: *mut LeanObject,
    mut v_t_742_: *mut LeanObject,
    mut v_h_743_: *mut LeanObject,
    mut v_cons_744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_745_: *mut LeanObject = core::ptr::null_mut();
    v___x_745_ = l_Lean_Grind_AC_Seq_ctorElim___redArg(v_t_742_, v_cons_744_);
    return v___x_745_;
}
pub unsafe fn l_Lean_Grind_AC_instReprSeq_repr(
    mut v_x_762_: *mut LeanObject,
    mut v_prec_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_767_: u8 = 0;
    let mut v___y_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_781_: u8 = 0;
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut v_x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_789_: u8 = 0;
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: u8 = 0;
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: u8 = 0;
    let mut v___x_808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_762_) == 0 {
                    v_x_764_ = lean_ctor_get(v_x_762_, 0);
                    v_isSharedCheck_784_ = (!lean_is_exclusive(v_x_762_)) as u8;
                    if v_isSharedCheck_784_ == 0 {
                        v___x_766_ = v_x_762_;
                        v_isShared_767_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_764_);
                        lean_dec(v_x_762_);
                        v___x_766_ = lean_box(0);
                        v_isShared_767_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_x_785_ = lean_ctor_get(v_x_762_, 0);
                    v_s_786_ = lean_ctor_get(v_x_762_, 1);
                    v_isSharedCheck_810_ = (!lean_is_exclusive(v_x_762_)) as u8;
                    if v_isSharedCheck_810_ == 0 {
                        v___x_788_ = v_x_762_;
                        v_isShared_789_ = v_isSharedCheck_810_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_s_786_);
                        lean_inc(v_x_785_);
                        lean_dec(v_x_762_);
                        v___x_788_ = lean_box(0);
                        v_isShared_789_ = v_isSharedCheck_810_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_780_ = lean_unsigned_to_nat(1024);
                v___x_781_ = lean_nat_dec_le(v___x_780_, v_prec_763_);
                if v___x_781_ == 0 {
                    v___x_782_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_769_ = v___x_782_;
                    state = 2;
                    continue;
                } else {
                    v___x_783_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_769_ = v___x_783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_770_ = l_Lean_Grind_AC_instReprSeq_repr___closed__2;
                v___x_771_ = l_Nat_reprFast(v_x_764_);
                if v_isShared_767_ == 0 {
                    lean_ctor_set_tag(v___x_766_, 3);
                    lean_ctor_set(v___x_766_, 0, v___x_771_);
                    v___x_773_ = v___x_766_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_779_ = lean_alloc_ctor(3, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_771_);
                    v___x_773_ = v_reuseFailAlloc_779_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_774_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_774_, 0, v___x_770_);
                lean_ctor_set(v___x_774_, 1, v___x_773_);
                lean_inc(v___y_769_);
                v___x_775_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_775_, 0, v___y_769_);
                lean_ctor_set(v___x_775_, 1, v___x_774_);
                v___x_776_ = 0;
                v___x_777_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_777_, 0, v___x_775_);
                lean_ctor_set_uint8(
                    v___x_777_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_776_,
                );
                v___x_778_ = l_Repr_addAppParen(v___x_777_, v_prec_763_);
                return v___x_778_;
            }
            4 => {
                v___x_790_ = lean_unsigned_to_nat(1024);
                v___x_807_ = lean_nat_dec_le(v___x_790_, v_prec_763_);
                if v___x_807_ == 0 {
                    v___x_808_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__3_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__3,
                    );
                    v___y_792_ = v___x_808_;
                    state = 5;
                    continue;
                } else {
                    v___x_809_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4),
                        core::ptr::addr_of_mut!(l_Lean_Grind_AC_instReprExpr_repr___closed__4_once),
                        _init_l_Lean_Grind_AC_instReprExpr_repr___closed__4,
                    );
                    v___y_792_ = v___x_809_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_793_ = lean_box(1);
                v___x_794_ = l_Lean_Grind_AC_instReprSeq_repr___closed__5;
                v___x_795_ = l_Nat_reprFast(v_x_785_);
                v___x_796_ = lean_alloc_ctor(3, 1, (0) as u32);
                lean_ctor_set(v___x_796_, 0, v___x_795_);
                if v_isShared_789_ == 0 {
                    lean_ctor_set_tag(v___x_788_, 5);
                    lean_ctor_set(v___x_788_, 1, v___x_796_);
                    lean_ctor_set(v___x_788_, 0, v___x_794_);
                    v___x_798_ = v___x_788_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_806_ = lean_alloc_ctor(5, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_806_, 0, v___x_794_);
                    lean_ctor_set(v_reuseFailAlloc_806_, 1, v___x_796_);
                    v___x_798_ = v_reuseFailAlloc_806_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_799_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_799_, 0, v___x_798_);
                lean_ctor_set(v___x_799_, 1, v___x_793_);
                v___x_800_ = l_Lean_Grind_AC_instReprSeq_repr(v_s_786_, v___x_790_);
                v___x_801_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_801_, 0, v___x_799_);
                lean_ctor_set(v___x_801_, 1, v___x_800_);
                lean_inc(v___y_792_);
                v___x_802_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_802_, 0, v___y_792_);
                lean_ctor_set(v___x_802_, 1, v___x_801_);
                v___x_803_ = 0;
                v___x_804_ = lean_alloc_ctor(6, 1, (1) as u32);
                lean_ctor_set(v___x_804_, 0, v___x_802_);
                lean_ctor_set_uint8(
                    v___x_804_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_803_,
                );
                v___x_805_ = l_Repr_addAppParen(v___x_804_, v_prec_763_);
                return v___x_805_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_instReprSeq_repr___boxed(
    mut v_x_811_: *mut LeanObject,
    mut v_prec_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_813_: *mut LeanObject = core::ptr::null_mut();
    v_res_813_ = l_Lean_Grind_AC_instReprSeq_repr(v_x_811_, v_prec_812_);
    lean_dec(v_prec_812_);
    return v_res_813_;
}
pub unsafe fn l_Lean_Grind_AC_instBEqSeq_beq(
    mut v_x_816_: *mut LeanObject,
    mut v_x_817_: *mut LeanObject,
) -> u8 {
    let mut v_x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: u8 = 0;
    let mut v___x_821_: u8 = 0;
    let mut v_x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_826_: u8 = 0;
    let mut v___x_828_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_816_) == 0 {
                    if lean_obj_tag(v_x_817_) == 0 {
                        v_x_818_ = lean_ctor_get(v_x_816_, 0);
                        v_x_819_ = lean_ctor_get(v_x_817_, 0);
                        v___x_820_ = lean_nat_dec_eq(v_x_818_, v_x_819_);
                        return v___x_820_;
                    } else {
                        v___x_821_ = 0;
                        return v___x_821_;
                    }
                } else {
                    if lean_obj_tag(v_x_817_) == 1 {
                        v_x_822_ = lean_ctor_get(v_x_816_, 0);
                        v_s_823_ = lean_ctor_get(v_x_816_, 1);
                        v_x_824_ = lean_ctor_get(v_x_817_, 0);
                        v_s_825_ = lean_ctor_get(v_x_817_, 1);
                        v___x_826_ = lean_nat_dec_eq(v_x_822_, v_x_824_);
                        if v___x_826_ == 0 {
                            return v___x_826_;
                        } else {
                            v_x_816_ = v_s_823_;
                            v_x_817_ = v_s_825_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_828_ = 0;
                        return v___x_828_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_instBEqSeq_beq___boxed(
    mut v_x_829_: *mut LeanObject,
    mut v_x_830_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_831_: u8 = 0;
    let mut v_r_832_: *mut LeanObject = core::ptr::null_mut();
    v_res_831_ = l_Lean_Grind_AC_instBEqSeq_beq(v_x_829_, v_x_830_);
    lean_dec_ref(v_x_830_);
    lean_dec_ref(v_x_829_);
    v_r_832_ = lean_box((v_res_831_) as usize);
    return v_r_832_;
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter___redArg(
    mut v_x_835_: *mut LeanObject,
    mut v_x_836_: *mut LeanObject,
    mut v_h__1_837_: *mut LeanObject,
    mut v_h__2_838_: *mut LeanObject,
    mut v_h__3_839_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_835_) == 0 {
        lean_dec(v_h__2_838_);
        if lean_obj_tag(v_x_836_) == 0 {
            let mut v_x_840_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_841_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_839_);
            v_x_840_ = lean_ctor_get(v_x_835_, 0);
            lean_inc(v_x_840_);
            lean_dec_ref_known(v_x_835_, 1);
            v_x_841_ = lean_ctor_get(v_x_836_, 0);
            lean_inc(v_x_841_);
            lean_dec_ref_known(v_x_836_, 1);
            v___x_842_ = lean_apply_2(v_h__1_837_, v_x_840_, v_x_841_);
            return v___x_842_;
        } else {
            let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_837_);
            v___x_843_ = lean_apply_4(v_h__3_839_, v_x_835_, v_x_836_, lean_box(0), lean_box(0));
            return v___x_843_;
        }
    } else {
        lean_dec(v_h__1_837_);
        if lean_obj_tag(v_x_836_) == 1 {
            let mut v_x_844_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_845_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_846_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_847_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_839_);
            v_x_844_ = lean_ctor_get(v_x_835_, 0);
            lean_inc(v_x_844_);
            v_s_845_ = lean_ctor_get(v_x_835_, 1);
            lean_inc_ref(v_s_845_);
            lean_dec_ref_known(v_x_835_, 2);
            v_x_846_ = lean_ctor_get(v_x_836_, 0);
            lean_inc(v_x_846_);
            v_s_847_ = lean_ctor_get(v_x_836_, 1);
            lean_inc_ref(v_s_847_);
            lean_dec_ref_known(v_x_836_, 2);
            v___x_848_ = lean_apply_4(v_h__2_838_, v_x_844_, v_s_845_, v_x_846_, v_s_847_);
            return v___x_848_;
        } else {
            let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_838_);
            v___x_849_ = lean_apply_4(v_h__3_839_, v_x_835_, v_x_836_, lean_box(0), lean_box(0));
            return v___x_849_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_instBEqSeq_beq_match__1_splitter(
    mut v_motive_850_: *mut LeanObject,
    mut v_x_851_: *mut LeanObject,
    mut v_x_852_: *mut LeanObject,
    mut v_h__1_853_: *mut LeanObject,
    mut v_h__2_854_: *mut LeanObject,
    mut v_h__3_855_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_851_) == 0 {
        lean_dec(v_h__2_854_);
        if lean_obj_tag(v_x_852_) == 0 {
            let mut v_x_856_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_857_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_855_);
            v_x_856_ = lean_ctor_get(v_x_851_, 0);
            lean_inc(v_x_856_);
            lean_dec_ref_known(v_x_851_, 1);
            v_x_857_ = lean_ctor_get(v_x_852_, 0);
            lean_inc(v_x_857_);
            lean_dec_ref_known(v_x_852_, 1);
            v___x_858_ = lean_apply_2(v_h__1_853_, v_x_856_, v_x_857_);
            return v___x_858_;
        } else {
            let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_853_);
            v___x_859_ = lean_apply_4(v_h__3_855_, v_x_851_, v_x_852_, lean_box(0), lean_box(0));
            return v___x_859_;
        }
    } else {
        lean_dec(v_h__1_853_);
        if lean_obj_tag(v_x_852_) == 1 {
            let mut v_x_860_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_861_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_862_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_863_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_855_);
            v_x_860_ = lean_ctor_get(v_x_851_, 0);
            lean_inc(v_x_860_);
            v_s_861_ = lean_ctor_get(v_x_851_, 1);
            lean_inc_ref(v_s_861_);
            lean_dec_ref_known(v_x_851_, 2);
            v_x_862_ = lean_ctor_get(v_x_852_, 0);
            lean_inc(v_x_862_);
            v_s_863_ = lean_ctor_get(v_x_852_, 1);
            lean_inc_ref(v_s_863_);
            lean_dec_ref_known(v_x_852_, 2);
            v___x_864_ = lean_apply_4(v_h__2_854_, v_x_860_, v_s_861_, v_x_862_, v_s_863_);
            return v___x_864_;
        } else {
            let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_854_);
            v___x_865_ = lean_apply_4(v_h__3_855_, v_x_851_, v_x_852_, lean_box(0), lean_box(0));
            return v___x_865_;
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_toSeq_x27(
    mut v_e_866_: *mut LeanObject,
    mut v_s_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lhs_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_866_) == 0 {
                    v_x_868_ = lean_ctor_get(v_e_866_, 0);
                    lean_inc(v_x_868_);
                    v___x_869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_869_, 0, v_x_868_);
                    lean_ctor_set(v___x_869_, 1, v_s_867_);
                    return v___x_869_;
                } else {
                    v_lhs_870_ = lean_ctor_get(v_e_866_, 0);
                    v_rhs_871_ = lean_ctor_get(v_e_866_, 1);
                    v___x_872_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_rhs_871_, v_s_867_);
                    v_e_866_ = v_lhs_870_;
                    v_s_867_ = v___x_872_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_toSeq_x27___boxed(
    mut v_e_874_: *mut LeanObject,
    mut v_s_875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_876_: *mut LeanObject = core::ptr::null_mut();
    v_res_876_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_e_874_, v_s_875_);
    lean_dec_ref(v_e_874_);
    return v_res_876_;
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter___redArg(
    mut v_e_877_: *mut LeanObject,
    mut v_h__1_878_: *mut LeanObject,
    mut v_h__2_879_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_877_) == 0 {
        let mut v_x_880_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_879_);
        v_x_880_ = lean_ctor_get(v_e_877_, 0);
        lean_inc(v_x_880_);
        lean_dec_ref_known(v_e_877_, 1);
        v___x_881_ = lean_apply_1(v_h__1_878_, v_x_880_);
        return v___x_881_;
    } else {
        let mut v_lhs_882_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_883_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_878_);
        v_lhs_882_ = lean_ctor_get(v_e_877_, 0);
        lean_inc_ref(v_lhs_882_);
        v_rhs_883_ = lean_ctor_get(v_e_877_, 1);
        lean_inc_ref(v_rhs_883_);
        lean_dec_ref_known(v_e_877_, 2);
        v___x_884_ = lean_apply_2(v_h__2_879_, v_lhs_882_, v_rhs_883_);
        return v___x_884_;
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Expr_toSeq_x27_match__1_splitter(
    mut v_motive_885_: *mut LeanObject,
    mut v_e_886_: *mut LeanObject,
    mut v_h__1_887_: *mut LeanObject,
    mut v_h__2_888_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_886_) == 0 {
        let mut v_x_889_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_888_);
        v_x_889_ = lean_ctor_get(v_e_886_, 0);
        lean_inc(v_x_889_);
        lean_dec_ref_known(v_e_886_, 1);
        v___x_890_ = lean_apply_1(v_h__1_887_, v_x_889_);
        return v___x_890_;
    } else {
        let mut v_lhs_891_: *mut LeanObject = core::ptr::null_mut();
        let mut v_rhs_892_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_893_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_887_);
        v_lhs_891_ = lean_ctor_get(v_e_886_, 0);
        lean_inc_ref(v_lhs_891_);
        v_rhs_892_ = lean_ctor_get(v_e_886_, 1);
        lean_inc_ref(v_rhs_892_);
        lean_dec_ref_known(v_e_886_, 2);
        v___x_893_ = lean_apply_2(v_h__2_888_, v_lhs_891_, v_rhs_892_);
        return v___x_893_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Expr_toSeq(mut v_e_894_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_898_: u8 = 0;
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_902_: u8 = 0;
    let mut v_lhs_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rhs_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_894_) == 0 {
                    v_x_895_ = lean_ctor_get(v_e_894_, 0);
                    v_isSharedCheck_902_ = (!lean_is_exclusive(v_e_894_)) as u8;
                    if v_isSharedCheck_902_ == 0 {
                        v___x_897_ = v_e_894_;
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_x_895_);
                        lean_dec(v_e_894_);
                        v___x_897_ = lean_box(0);
                        v_isShared_898_ = v_isSharedCheck_902_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_lhs_903_ = lean_ctor_get(v_e_894_, 0);
                    lean_inc_ref(v_lhs_903_);
                    v_rhs_904_ = lean_ctor_get(v_e_894_, 1);
                    lean_inc_ref(v_rhs_904_);
                    lean_dec_ref_known(v_e_894_, 2);
                    v___x_905_ = l_Lean_Grind_AC_Expr_toSeq(v_rhs_904_);
                    v___x_906_ = l_Lean_Grind_AC_Expr_toSeq_x27(v_lhs_903_, v___x_905_);
                    lean_dec_ref(v_lhs_903_);
                    return v___x_906_;
                }
            }
            1 => {
                if v_isShared_898_ == 0 {
                    v___x_900_ = v___x_897_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_901_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_901_, 0, v_x_895_);
                    v___x_900_ = v_reuseFailAlloc_901_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_900_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_erase0(mut v_s_907_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v_s_x27_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_915_: u8 = 0;
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_917_: u8 = 0;
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_907_) == 0 {
                    return v_s_907_;
                } else {
                    v_x_908_ = lean_ctor_get(v_s_907_, 0);
                    v_s_909_ = lean_ctor_get(v_s_907_, 1);
                    v_isSharedCheck_922_ = (!lean_is_exclusive(v_s_907_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_911_ = v_s_907_;
                        v_isShared_912_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_909_);
                        lean_inc(v_x_908_);
                        lean_dec(v_s_907_);
                        v___x_911_ = lean_box(0);
                        v_isShared_912_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_s_x27_913_ = l_Lean_Grind_AC_Seq_erase0(v_s_909_);
                v___x_914_ = lean_unsigned_to_nat(0);
                v___x_915_ = lean_nat_dec_eq(v_x_908_, v___x_914_);
                if v___x_915_ == 0 {
                    v___x_916_ = l_Lean_Grind_AC_instInhabitedSeq_default___closed__0;
                    v___x_917_ = l_Lean_Grind_AC_instBEqSeq_beq(v_s_x27_913_, v___x_916_);
                    if v___x_917_ == 0 {
                        if v_isShared_912_ == 0 {
                            lean_ctor_set(v___x_911_, 1, v_s_x27_913_);
                            v___x_919_ = v___x_911_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_920_, 0, v_x_908_);
                            lean_ctor_set(v_reuseFailAlloc_920_, 1, v_s_x27_913_);
                            v___x_919_ = v_reuseFailAlloc_920_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_s_x27_913_);
                        lean_del_object(v___x_911_);
                        v___x_921_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_921_, 0, v_x_908_);
                        return v___x_921_;
                    }
                } else {
                    lean_del_object(v___x_911_);
                    lean_dec(v_x_908_);
                    return v_s_x27_913_;
                }
            }
            2 => {
                return v___x_919_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter___redArg(
    mut v_s_923_: *mut LeanObject,
    mut v_h__1_924_: *mut LeanObject,
    mut v_h__2_925_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_923_) == 0 {
        let mut v_x_926_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_925_);
        v_x_926_ = lean_ctor_get(v_s_923_, 0);
        lean_inc(v_x_926_);
        lean_dec_ref_known(v_s_923_, 1);
        v___x_927_ = lean_apply_1(v_h__1_924_, v_x_926_);
        return v___x_927_;
    } else {
        let mut v_x_928_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_929_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_924_);
        v_x_928_ = lean_ctor_get(v_s_923_, 0);
        lean_inc(v_x_928_);
        v_s_929_ = lean_ctor_get(v_s_923_, 1);
        lean_inc_ref(v_s_929_);
        lean_dec_ref_known(v_s_923_, 2);
        v___x_930_ = lean_apply_2(v_h__2_925_, v_x_928_, v_s_929_);
        return v___x_930_;
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_erase0_match__1_splitter(
    mut v_motive_931_: *mut LeanObject,
    mut v_s_932_: *mut LeanObject,
    mut v_h__1_933_: *mut LeanObject,
    mut v_h__2_934_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_932_) == 0 {
        let mut v_x_935_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_934_);
        v_x_935_ = lean_ctor_get(v_s_932_, 0);
        lean_inc(v_x_935_);
        lean_dec_ref_known(v_s_932_, 1);
        v___x_936_ = lean_apply_1(v_h__1_933_, v_x_935_);
        return v___x_936_;
    } else {
        let mut v_x_937_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_933_);
        v_x_937_ = lean_ctor_get(v_s_932_, 0);
        lean_inc(v_x_937_);
        v_s_938_ = lean_ctor_get(v_s_932_, 1);
        lean_inc_ref(v_s_938_);
        lean_dec_ref_known(v_s_932_, 2);
        v___x_939_ = lean_apply_2(v_h__2_934_, v_x_937_, v_s_938_);
        return v___x_939_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_insert(
    mut v_x_940_: *mut LeanObject,
    mut v_s_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: u8 = 0;
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_946_: u8 = 0;
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_951_: u8 = 0;
    let mut v_unused_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: u8 = 0;
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_964_: u8 = 0;
    let mut v_unused_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_941_) == 0 {
                    v_x_942_ = lean_ctor_get(v_s_941_, 0);
                    v___x_943_ = l_Nat_blt(v_x_940_, v_x_942_);
                    if v___x_943_ == 0 {
                        lean_inc(v_x_942_);
                        v_isSharedCheck_951_ = (!lean_is_exclusive(v_s_941_)) as u8;
                        if v_isSharedCheck_951_ == 0 {
                            v_unused_952_ = lean_ctor_get(v_s_941_, 0);
                            lean_dec(v_unused_952_);
                            v___x_945_ = v_s_941_;
                            v_isShared_946_ = v_isSharedCheck_951_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_s_941_);
                            v___x_945_ = lean_box(0);
                            v_isShared_946_ = v_isSharedCheck_951_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_953_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_953_, 0, v_x_940_);
                        lean_ctor_set(v___x_953_, 1, v_s_941_);
                        return v___x_953_;
                    }
                } else {
                    v_x_954_ = lean_ctor_get(v_s_941_, 0);
                    v_s_955_ = lean_ctor_get(v_s_941_, 1);
                    v___x_956_ = l_Nat_blt(v_x_940_, v_x_954_);
                    if v___x_956_ == 0 {
                        lean_inc_ref(v_s_955_);
                        lean_inc(v_x_954_);
                        v_isSharedCheck_964_ = (!lean_is_exclusive(v_s_941_)) as u8;
                        if v_isSharedCheck_964_ == 0 {
                            v_unused_965_ = lean_ctor_get(v_s_941_, 1);
                            lean_dec(v_unused_965_);
                            v_unused_966_ = lean_ctor_get(v_s_941_, 0);
                            lean_dec(v_unused_966_);
                            v___x_958_ = v_s_941_;
                            v_isShared_959_ = v_isSharedCheck_964_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_s_941_);
                            v___x_958_ = lean_box(0);
                            v_isShared_959_ = v_isSharedCheck_964_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_967_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_967_, 0, v_x_940_);
                        lean_ctor_set(v___x_967_, 1, v_s_941_);
                        return v___x_967_;
                    }
                }
            }
            1 => {
                if v_isShared_946_ == 0 {
                    lean_ctor_set(v___x_945_, 0, v_x_940_);
                    v___x_948_ = v___x_945_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_950_, 0, v_x_940_);
                    v___x_948_ = v_reuseFailAlloc_950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_949_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_949_, 0, v_x_942_);
                lean_ctor_set(v___x_949_, 1, v___x_948_);
                return v___x_949_;
            }
            3 => {
                v___x_960_ = l_Lean_Grind_AC_Seq_insert(v_x_940_, v_s_955_);
                if v_isShared_959_ == 0 {
                    lean_ctor_set(v___x_958_, 1, v___x_960_);
                    v___x_962_ = v___x_958_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_963_, 0, v_x_954_);
                    lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_960_);
                    v___x_962_ = v_reuseFailAlloc_963_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_962_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_sort_x27(
    mut v_s_968_: *mut LeanObject,
    mut v_acc_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_968_) == 0 {
                    v_x_970_ = lean_ctor_get(v_s_968_, 0);
                    lean_inc(v_x_970_);
                    lean_dec_ref_known(v_s_968_, 1);
                    v___x_971_ = l_Lean_Grind_AC_Seq_insert(v_x_970_, v_acc_969_);
                    return v___x_971_;
                } else {
                    v_x_972_ = lean_ctor_get(v_s_968_, 0);
                    lean_inc(v_x_972_);
                    v_s_973_ = lean_ctor_get(v_s_968_, 1);
                    lean_inc_ref(v_s_973_);
                    lean_dec_ref_known(v_s_968_, 2);
                    v___x_974_ = l_Lean_Grind_AC_Seq_insert(v_x_972_, v_acc_969_);
                    v_s_968_ = v_s_973_;
                    v_acc_969_ = v___x_974_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_sort(mut v_s_976_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_s_976_) == 0 {
        return v_s_976_;
    } else {
        let mut v_x_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v_s_978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        v_x_977_ = lean_ctor_get(v_s_976_, 0);
        lean_inc(v_x_977_);
        v_s_978_ = lean_ctor_get(v_s_976_, 1);
        lean_inc_ref(v_s_978_);
        lean_dec_ref_known(v_s_976_, 2);
        v___x_979_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_979_, 0, v_x_977_);
        v___x_980_ = l_Lean_Grind_AC_Seq_sort_x27(v_s_978_, v___x_979_);
        return v___x_980_;
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_eraseDup(mut v_s_981_: *mut LeanObject) -> *mut LeanObject {
    let mut v_x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_986_: u8 = 0;
    let mut v_s_x27_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u8 = 0;
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_995_: u8 = 0;
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_999_: u8 = 0;
    let mut v_unused_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_981_) == 0 {
                    return v_s_981_;
                } else {
                    v_x_982_ = lean_ctor_get(v_s_981_, 0);
                    v_s_983_ = lean_ctor_get(v_s_981_, 1);
                    v_isSharedCheck_1006_ = (!lean_is_exclusive(v_s_981_)) as u8;
                    if v_isSharedCheck_1006_ == 0 {
                        v___x_985_ = v_s_981_;
                        v_isShared_986_ = v_isSharedCheck_1006_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_983_);
                        lean_inc(v_x_982_);
                        lean_dec(v_s_981_);
                        v___x_985_ = lean_box(0);
                        v_isShared_986_ = v_isSharedCheck_1006_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_s_x27_987_ = l_Lean_Grind_AC_Seq_eraseDup(v_s_983_);
                if lean_obj_tag(v_s_x27_987_) == 0 {
                    v_x_988_ = lean_ctor_get(v_s_x27_987_, 0);
                    lean_inc(v_x_988_);
                    v___x_989_ = lean_nat_dec_eq(v_x_982_, v_x_988_);
                    lean_dec(v_x_988_);
                    if v___x_989_ == 0 {
                        if v_isShared_986_ == 0 {
                            lean_ctor_set(v___x_985_, 1, v_s_x27_987_);
                            v___x_991_ = v___x_985_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_992_, 0, v_x_982_);
                            lean_ctor_set(v_reuseFailAlloc_992_, 1, v_s_x27_987_);
                            v___x_991_ = v_reuseFailAlloc_992_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_985_);
                        v_isSharedCheck_999_ = (!lean_is_exclusive(v_s_x27_987_)) as u8;
                        if v_isSharedCheck_999_ == 0 {
                            v_unused_1000_ = lean_ctor_get(v_s_x27_987_, 0);
                            lean_dec(v_unused_1000_);
                            v___x_994_ = v_s_x27_987_;
                            v_isShared_995_ = v_isSharedCheck_999_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v_s_x27_987_);
                            v___x_994_ = lean_box(0);
                            v_isShared_995_ = v_isSharedCheck_999_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_x_1001_ = lean_ctor_get(v_s_x27_987_, 0);
                    lean_inc(v_x_1001_);
                    v___x_1002_ = lean_nat_dec_eq(v_x_982_, v_x_1001_);
                    lean_dec(v_x_1001_);
                    if v___x_1002_ == 0 {
                        if v_isShared_986_ == 0 {
                            lean_ctor_set(v___x_985_, 1, v_s_x27_987_);
                            v___x_1004_ = v___x_985_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_x_982_);
                            lean_ctor_set(v_reuseFailAlloc_1005_, 1, v_s_x27_987_);
                            v___x_1004_ = v_reuseFailAlloc_1005_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_985_);
                        lean_dec(v_x_982_);
                        return v_s_x27_987_;
                    }
                }
            }
            2 => {
                return v___x_991_;
            }
            3 => {
                if v_isShared_995_ == 0 {
                    lean_ctor_set(v___x_994_, 0, v_x_982_);
                    v___x_997_ = v___x_994_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_998_, 0, v_x_982_);
                    v___x_997_ = v_reuseFailAlloc_998_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_997_;
            }
            5 => {
                return v___x_1004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_concat(
    mut v_s_u2081_1007_: *mut LeanObject,
    mut v_s_u2082_1008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1015_: u8 = 0;
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1020_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_s_u2081_1007_) == 0 {
                    v_x_1009_ = lean_ctor_get(v_s_u2081_1007_, 0);
                    lean_inc(v_x_1009_);
                    lean_dec_ref_known(v_s_u2081_1007_, 1);
                    v___x_1010_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_1010_, 0, v_x_1009_);
                    lean_ctor_set(v___x_1010_, 1, v_s_u2082_1008_);
                    return v___x_1010_;
                } else {
                    v_x_1011_ = lean_ctor_get(v_s_u2081_1007_, 0);
                    v_s_1012_ = lean_ctor_get(v_s_u2081_1007_, 1);
                    v_isSharedCheck_1020_ = (!lean_is_exclusive(v_s_u2081_1007_)) as u8;
                    if v_isSharedCheck_1020_ == 0 {
                        v___x_1014_ = v_s_u2081_1007_;
                        v_isShared_1015_ = v_isSharedCheck_1020_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_s_1012_);
                        lean_inc(v_x_1011_);
                        lean_dec(v_s_u2081_1007_);
                        v___x_1014_ = lean_box(0);
                        v_isShared_1015_ = v_isSharedCheck_1020_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1016_ = l_Lean_Grind_AC_Seq_concat(v_s_1012_, v_s_u2082_1008_);
                if v_isShared_1015_ == 0 {
                    lean_ctor_set(v___x_1014_, 1, v___x_1016_);
                    v___x_1018_ = v___x_1014_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1019_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 0, v_x_1011_);
                    lean_ctor_set(v_reuseFailAlloc_1019_, 1, v___x_1016_);
                    v___x_1018_ = v_reuseFailAlloc_1019_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1018_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_unionFuel(
    mut v_fuel_1021_: *mut LeanObject,
    mut v_s_u2081_1022_: *mut LeanObject,
    mut v_s_u2082_1023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1025_: u8 = 0;
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_s_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1050_: u8 = 0;
    let mut v_unused_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_unused_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1024_ = lean_unsigned_to_nat(0);
                v_isZero_1025_ = lean_nat_dec_eq(v_fuel_1021_, v_zero_1024_);
                if v_isZero_1025_ == 1 {
                    v___x_1026_ = l_Lean_Grind_AC_Seq_concat(v_s_u2081_1022_, v_s_u2082_1023_);
                    return v___x_1026_;
                } else {
                    if lean_obj_tag(v_s_u2081_1022_) == 0 {
                        if lean_obj_tag(v_s_u2082_1023_) == 0 {
                            v_x_1027_ = lean_ctor_get(v_s_u2081_1022_, 0);
                            v_x_1028_ = lean_ctor_get(v_s_u2082_1023_, 0);
                            v___x_1029_ = l_Nat_blt(v_x_1027_, v_x_1028_);
                            if v___x_1029_ == 0 {
                                lean_inc(v_x_1028_);
                                lean_dec_ref_known(v_s_u2082_1023_, 1);
                                v___x_1030_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1030_, 0, v_x_1028_);
                                lean_ctor_set(v___x_1030_, 1, v_s_u2081_1022_);
                                return v___x_1030_;
                            } else {
                                lean_inc(v_x_1027_);
                                lean_dec_ref_known(v_s_u2081_1022_, 1);
                                v___x_1031_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_1031_, 0, v_x_1027_);
                                lean_ctor_set(v___x_1031_, 1, v_s_u2082_1023_);
                                return v___x_1031_;
                            }
                        } else {
                            v_x_1032_ = lean_ctor_get(v_s_u2081_1022_, 0);
                            lean_inc(v_x_1032_);
                            lean_dec_ref_known(v_s_u2081_1022_, 1);
                            v___x_1033_ = l_Lean_Grind_AC_Seq_insert(v_x_1032_, v_s_u2082_1023_);
                            return v___x_1033_;
                        }
                    } else {
                        if lean_obj_tag(v_s_u2082_1023_) == 0 {
                            v_x_1034_ = lean_ctor_get(v_s_u2082_1023_, 0);
                            lean_inc(v_x_1034_);
                            lean_dec_ref_known(v_s_u2082_1023_, 1);
                            v___x_1035_ = l_Lean_Grind_AC_Seq_insert(v_x_1034_, v_s_u2081_1022_);
                            return v___x_1035_;
                        } else {
                            v_x_1036_ = lean_ctor_get(v_s_u2081_1022_, 0);
                            v_s_1037_ = lean_ctor_get(v_s_u2081_1022_, 1);
                            v_x_1038_ = lean_ctor_get(v_s_u2082_1023_, 0);
                            v_s_1039_ = lean_ctor_get(v_s_u2082_1023_, 1);
                            v_one_1040_ = lean_unsigned_to_nat(1);
                            v_n_1041_ = lean_nat_sub(v_fuel_1021_, v_one_1040_);
                            v___x_1042_ = l_Nat_blt(v_x_1036_, v_x_1038_);
                            if v___x_1042_ == 0 {
                                lean_inc_ref(v_s_1039_);
                                lean_inc(v_x_1038_);
                                v_isSharedCheck_1050_ = (!lean_is_exclusive(v_s_u2082_1023_)) as u8;
                                if v_isSharedCheck_1050_ == 0 {
                                    v_unused_1051_ = lean_ctor_get(v_s_u2082_1023_, 1);
                                    lean_dec(v_unused_1051_);
                                    v_unused_1052_ = lean_ctor_get(v_s_u2082_1023_, 0);
                                    lean_dec(v_unused_1052_);
                                    v___x_1044_ = v_s_u2082_1023_;
                                    v_isShared_1045_ = v_isSharedCheck_1050_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_s_u2082_1023_);
                                    v___x_1044_ = lean_box(0);
                                    v_isShared_1045_ = v_isSharedCheck_1050_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_inc_ref(v_s_1037_);
                                lean_inc(v_x_1036_);
                                v_isSharedCheck_1060_ = (!lean_is_exclusive(v_s_u2081_1022_)) as u8;
                                if v_isSharedCheck_1060_ == 0 {
                                    v_unused_1061_ = lean_ctor_get(v_s_u2081_1022_, 1);
                                    lean_dec(v_unused_1061_);
                                    v_unused_1062_ = lean_ctor_get(v_s_u2081_1022_, 0);
                                    lean_dec(v_unused_1062_);
                                    v___x_1054_ = v_s_u2081_1022_;
                                    v_isShared_1055_ = v_isSharedCheck_1060_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_s_u2081_1022_);
                                    v___x_1054_ = lean_box(0);
                                    v_isShared_1055_ = v_isSharedCheck_1060_;
                                    state = 3;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1046_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_1041_, v_s_u2081_1022_, v_s_1039_);
                lean_dec(v_n_1041_);
                if v_isShared_1045_ == 0 {
                    lean_ctor_set(v___x_1044_, 1, v___x_1046_);
                    v___x_1048_ = v___x_1044_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 0, v_x_1038_);
                    lean_ctor_set(v_reuseFailAlloc_1049_, 1, v___x_1046_);
                    v___x_1048_ = v_reuseFailAlloc_1049_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1048_;
            }
            3 => {
                v___x_1056_ = l_Lean_Grind_AC_Seq_unionFuel(v_n_1041_, v_s_1037_, v_s_u2082_1023_);
                lean_dec(v_n_1041_);
                if v_isShared_1055_ == 0 {
                    lean_ctor_set(v___x_1054_, 1, v___x_1056_);
                    v___x_1058_ = v___x_1054_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v_x_1036_);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 1, v___x_1056_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1058_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Grind_AC_Seq_unionFuel___boxed(
    mut v_fuel_1063_: *mut LeanObject,
    mut v_s_u2081_1064_: *mut LeanObject,
    mut v_s_u2082_1065_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1066_: *mut LeanObject = core::ptr::null_mut();
    v_res_1066_ = l_Lean_Grind_AC_Seq_unionFuel(v_fuel_1063_, v_s_u2081_1064_, v_s_u2082_1065_);
    lean_dec(v_fuel_1063_);
    return v_res_1066_;
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(
    mut v_fuel_1067_: *mut LeanObject,
    mut v_h__1_1068_: *mut LeanObject,
    mut v_h__2_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1071_: u8 = 0;
    v_zero_1070_ = lean_unsigned_to_nat(0);
    v_isZero_1071_ = lean_nat_dec_eq(v_fuel_1067_, v_zero_1070_);
    if v_isZero_1071_ == 1 {
        let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1069_);
        v___x_1072_ = lean_box(0);
        v___x_1073_ = lean_apply_1(v_h__1_1068_, v___x_1072_);
        return v___x_1073_;
    } else {
        let mut v_one_1074_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1075_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1068_);
        v_one_1074_ = lean_unsigned_to_nat(1);
        v_n_1075_ = lean_nat_sub(v_fuel_1067_, v_one_1074_);
        v___x_1076_ = lean_apply_1(v_h__2_1069_, v_n_1075_);
        return v___x_1076_;
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg___boxed(
    mut v_fuel_1077_: *mut LeanObject,
    mut v_h__1_1078_: *mut LeanObject,
    mut v_h__2_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1080_: *mut LeanObject = core::ptr::null_mut();
    v_res_1080_ =
        l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___redArg(
            v_fuel_1077_,
            v_h__1_1078_,
            v_h__2_1079_,
        );
    lean_dec(v_fuel_1077_);
    return v_res_1080_;
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(
    mut v_motive_1081_: *mut LeanObject,
    mut v_fuel_1082_: *mut LeanObject,
    mut v_h__1_1083_: *mut LeanObject,
    mut v_h__2_1084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_1085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_1086_: u8 = 0;
    v_zero_1085_ = lean_unsigned_to_nat(0);
    v_isZero_1086_ = lean_nat_dec_eq(v_fuel_1082_, v_zero_1085_);
    if v_isZero_1086_ == 1 {
        let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1088_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1084_);
        v___x_1087_ = lean_box(0);
        v___x_1088_ = lean_apply_1(v_h__1_1083_, v___x_1087_);
        return v___x_1088_;
    } else {
        let mut v_one_1089_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_1090_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1091_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1083_);
        v_one_1089_ = lean_unsigned_to_nat(1);
        v_n_1090_ = lean_nat_sub(v_fuel_1082_, v_one_1089_);
        v___x_1091_ = lean_apply_1(v_h__2_1084_, v_n_1090_);
        return v___x_1091_;
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter___boxed(
    mut v_motive_1092_: *mut LeanObject,
    mut v_fuel_1093_: *mut LeanObject,
    mut v_h__1_1094_: *mut LeanObject,
    mut v_h__2_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
    v_res_1096_ = l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__3_splitter(
        v_motive_1092_,
        v_fuel_1093_,
        v_h__1_1094_,
        v_h__2_1095_,
    );
    lean_dec(v_fuel_1093_);
    return v_res_1096_;
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter___redArg(
    mut v_s_u2081_1097_: *mut LeanObject,
    mut v_s_u2082_1098_: *mut LeanObject,
    mut v_h__1_1099_: *mut LeanObject,
    mut v_h__2_1100_: *mut LeanObject,
    mut v_h__3_1101_: *mut LeanObject,
    mut v_h__4_1102_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_u2081_1097_) == 0 {
        lean_dec(v_h__4_1102_);
        lean_dec(v_h__3_1101_);
        if lean_obj_tag(v_s_u2082_1098_) == 0 {
            let mut v_x_1103_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1104_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1105_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1100_);
            v_x_1103_ = lean_ctor_get(v_s_u2081_1097_, 0);
            lean_inc(v_x_1103_);
            lean_dec_ref_known(v_s_u2081_1097_, 1);
            v_x_1104_ = lean_ctor_get(v_s_u2082_1098_, 0);
            lean_inc(v_x_1104_);
            lean_dec_ref_known(v_s_u2082_1098_, 1);
            v___x_1105_ = lean_apply_2(v_h__1_1099_, v_x_1103_, v_x_1104_);
            return v___x_1105_;
        } else {
            let mut v_x_1106_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1107_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1108_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1099_);
            v_x_1106_ = lean_ctor_get(v_s_u2081_1097_, 0);
            lean_inc(v_x_1106_);
            lean_dec_ref_known(v_s_u2081_1097_, 1);
            v_x_1107_ = lean_ctor_get(v_s_u2082_1098_, 0);
            lean_inc(v_x_1107_);
            v_s_1108_ = lean_ctor_get(v_s_u2082_1098_, 1);
            lean_inc_ref(v_s_1108_);
            lean_dec_ref_known(v_s_u2082_1098_, 2);
            v___x_1109_ = lean_apply_3(v_h__2_1100_, v_x_1106_, v_x_1107_, v_s_1108_);
            return v___x_1109_;
        }
    } else {
        lean_dec(v_h__2_1100_);
        lean_dec(v_h__1_1099_);
        if lean_obj_tag(v_s_u2082_1098_) == 0 {
            let mut v_x_1110_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1111_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1112_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1102_);
            v_x_1110_ = lean_ctor_get(v_s_u2081_1097_, 0);
            lean_inc(v_x_1110_);
            v_s_1111_ = lean_ctor_get(v_s_u2081_1097_, 1);
            lean_inc_ref(v_s_1111_);
            lean_dec_ref_known(v_s_u2081_1097_, 2);
            v_x_1112_ = lean_ctor_get(v_s_u2082_1098_, 0);
            lean_inc(v_x_1112_);
            lean_dec_ref_known(v_s_u2082_1098_, 1);
            v___x_1113_ = lean_apply_3(v_h__3_1101_, v_x_1110_, v_s_1111_, v_x_1112_);
            return v___x_1113_;
        } else {
            let mut v_x_1114_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1115_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1116_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1117_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1101_);
            v_x_1114_ = lean_ctor_get(v_s_u2081_1097_, 0);
            lean_inc(v_x_1114_);
            v_s_1115_ = lean_ctor_get(v_s_u2081_1097_, 1);
            lean_inc_ref(v_s_1115_);
            lean_dec_ref_known(v_s_u2081_1097_, 2);
            v_x_1116_ = lean_ctor_get(v_s_u2082_1098_, 0);
            lean_inc(v_x_1116_);
            v_s_1117_ = lean_ctor_get(v_s_u2082_1098_, 1);
            lean_inc_ref(v_s_1117_);
            lean_dec_ref_known(v_s_u2082_1098_, 2);
            v___x_1118_ = lean_apply_4(v_h__4_1102_, v_x_1114_, v_s_1115_, v_x_1116_, v_s_1117_);
            return v___x_1118_;
        }
    }
}
pub unsafe fn l___private_Init_Grind_AC_0__Lean_Grind_AC_Seq_unionFuel_match__1_splitter(
    mut v_motive_1119_: *mut LeanObject,
    mut v_s_u2081_1120_: *mut LeanObject,
    mut v_s_u2082_1121_: *mut LeanObject,
    mut v_h__1_1122_: *mut LeanObject,
    mut v_h__2_1123_: *mut LeanObject,
    mut v_h__3_1124_: *mut LeanObject,
    mut v_h__4_1125_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_s_u2081_1120_) == 0 {
        lean_dec(v_h__4_1125_);
        lean_dec(v_h__3_1124_);
        if lean_obj_tag(v_s_u2082_1121_) == 0 {
            let mut v_x_1126_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1127_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1123_);
            v_x_1126_ = lean_ctor_get(v_s_u2081_1120_, 0);
            lean_inc(v_x_1126_);
            lean_dec_ref_known(v_s_u2081_1120_, 1);
            v_x_1127_ = lean_ctor_get(v_s_u2082_1121_, 0);
            lean_inc(v_x_1127_);
            lean_dec_ref_known(v_s_u2082_1121_, 1);
            v___x_1128_ = lean_apply_2(v_h__1_1122_, v_x_1126_, v_x_1127_);
            return v___x_1128_;
        } else {
            let mut v_x_1129_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1130_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1131_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1122_);
            v_x_1129_ = lean_ctor_get(v_s_u2081_1120_, 0);
            lean_inc(v_x_1129_);
            lean_dec_ref_known(v_s_u2081_1120_, 1);
            v_x_1130_ = lean_ctor_get(v_s_u2082_1121_, 0);
            lean_inc(v_x_1130_);
            v_s_1131_ = lean_ctor_get(v_s_u2082_1121_, 1);
            lean_inc_ref(v_s_1131_);
            lean_dec_ref_known(v_s_u2082_1121_, 2);
            v___x_1132_ = lean_apply_3(v_h__2_1123_, v_x_1129_, v_x_1130_, v_s_1131_);
            return v___x_1132_;
        }
    } else {
        lean_dec(v_h__2_1123_);
        lean_dec(v_h__1_1122_);
        if lean_obj_tag(v_s_u2082_1121_) == 0 {
            let mut v_x_1133_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1134_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1135_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1125_);
            v_x_1133_ = lean_ctor_get(v_s_u2081_1120_, 0);
            lean_inc(v_x_1133_);
            v_s_1134_ = lean_ctor_get(v_s_u2081_1120_, 1);
            lean_inc_ref(v_s_1134_);
            lean_dec_ref_known(v_s_u2081_1120_, 2);
            v_x_1135_ = lean_ctor_get(v_s_u2082_1121_, 0);
            lean_inc(v_x_1135_);
            lean_dec_ref_known(v_s_u2082_1121_, 1);
            v___x_1136_ = lean_apply_3(v_h__3_1124_, v_x_1133_, v_s_1134_, v_x_1135_);
            return v___x_1136_;
        } else {
            let mut v_x_1137_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1138_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1139_: *mut LeanObject = core::ptr::null_mut();
            let mut v_s_1140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1124_);
            v_x_1137_ = lean_ctor_get(v_s_u2081_1120_, 0);
            lean_inc(v_x_1137_);
            v_s_1138_ = lean_ctor_get(v_s_u2081_1120_, 1);
            lean_inc_ref(v_s_1138_);
            lean_dec_ref_known(v_s_u2081_1120_, 2);
            v_x_1139_ = lean_ctor_get(v_s_u2082_1121_, 0);
            lean_inc(v_x_1139_);
            v_s_1140_ = lean_ctor_get(v_s_u2082_1121_, 1);
            lean_inc_ref(v_s_1140_);
            lean_dec_ref_known(v_s_u2082_1121_, 2);
            v___x_1141_ = lean_apply_4(v_h__4_1125_, v_x_1137_, v_s_1138_, v_x_1139_, v_s_1140_);
            return v___x_1141_;
        }
    }
}
pub unsafe fn _init_l_Lean_Grind_AC_hugeFuel() -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ = lean_unsigned_to_nat(1000000);
    return v___x_1142_;
}
pub unsafe fn l_Lean_Grind_AC_Seq_union(
    mut v_s_u2081_1143_: *mut LeanObject,
    mut v_s_u2082_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1145_ = lean_unsigned_to_nat(1000000);
    v___x_1146_ = l_Lean_Grind_AC_Seq_unionFuel(v___x_1145_, v_s_u2081_1143_, v_s_u2082_1144_);
    return v___x_1146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Grind_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Grind_AC_hugeFuel = _init_l_Lean_Grind_AC_hugeFuel();
    lean_mark_persistent(l_Lean_Grind_AC_hugeFuel);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Grind_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Grind_AC(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Classical(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Grind_AC(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Grind_AC(builtin);
}

// Lean compiler output
// Module: Init.Data.Nat.Linear
// Imports: Init.Data.RArray Init.LawfulBEqTactics Init.ByCases Init.Data.Prod
use crate::ffi::{lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_mul, lean_nat_sub};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::List::Basic::{l_List_appendTR___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Nat::Basic::l_Nat_blt;
use crate::r#gen::Init::Data::Prod::{
    initialize_Init_Data_Prod, runtime_initialize_Init_Data_Prod,
};
use crate::r#gen::Init::Data::RArray::{
    initialize_Init_Data_RArray, runtime_initialize_Init_Data_RArray,
};
use crate::r#gen::Init::LawfulBEqTactics::{
    initialize_Init_LawfulBEqTactics, runtime_initialize_Init_LawfulBEqTactics,
};
pub static mut l_Nat_Linear_fixedVar: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Nat_Linear_instInhabitedExpr_default___closed__0_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
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
static mut l_Nat_Linear_instInhabitedExpr_default___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Nat_Linear_instInhabitedExpr_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Nat_Linear_instInhabitedExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instInhabitedExpr_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_Linear_instBEqExpr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_Linear_instBEqExpr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_Linear_instBEqExpr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Nat_Linear_instBEqExpr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instBEqExpr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Nat_Linear_hugeFuel: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Nat_Linear_Poly_isNum_x3f___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Nat_Linear_Poly_isNum_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_Poly_isNum_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Nat_Linear_Expr_inc___closed__0_value: crate::leanh::LeanCtorObject<1> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [(((1 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Nat_Linear_Expr_inc___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_Expr_inc___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Nat_Linear_instBEqPolyCnstr___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Nat_Linear_instBEqPolyCnstr_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Nat_Linear_instBEqPolyCnstr___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instBEqPolyCnstr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Nat_Linear_instBEqPolyCnstr: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Nat_Linear_instBEqPolyCnstr___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Nat_Linear_fixedVar() -> *mut crate::leanh::LeanObject {
    let mut v___x_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_684_ = crate::leanh::lean_unsigned_to_nat(100000000);
    return v___x_684_;
}
pub unsafe fn l_Nat_Linear_Expr_ctorIdx(
    mut v_x_685_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_685_) {
        0 => {
            let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_686_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_686_;
        }
        1 => {
            let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_687_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_687_;
        }
        2 => {
            let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_688_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_688_;
        }
        3 => {
            let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_689_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_689_;
        }
        _ => {
            let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_690_ = crate::leanh::lean_unsigned_to_nat(4);
            return v___x_690_;
        }
    }
}
pub unsafe fn l_Nat_Linear_Expr_ctorIdx___boxed(
    mut v_x_691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_692_ = l_Nat_Linear_Expr_ctorIdx(v_x_691_);
    crate::leanh::lean_dec_ref(v_x_691_);
    return v_res_692_;
}
pub unsafe fn l_Nat_Linear_Expr_ctorElim___redArg(
    mut v_t_693_: *mut crate::leanh::LeanObject,
    mut v_k_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_693_) {
        2 => {
            let mut v_a_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_695_ = crate::leanh::lean_ctor_get(v_t_693_, 0);
            crate::leanh::lean_inc_ref(v_a_695_);
            v_b_696_ = crate::leanh::lean_ctor_get(v_t_693_, 1);
            crate::leanh::lean_inc_ref(v_b_696_);
            crate::leanh::lean_dec_ref_known(v_t_693_, 2);
            v___x_697_ = crate::leanh::lean_apply_2(v_k_694_, v_a_695_, v_b_696_);
            return v___x_697_;
        }
        3 => {
            let mut v_k_698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_k_698_ = crate::leanh::lean_ctor_get(v_t_693_, 0);
            crate::leanh::lean_inc(v_k_698_);
            v_a_699_ = crate::leanh::lean_ctor_get(v_t_693_, 1);
            crate::leanh::lean_inc_ref(v_a_699_);
            crate::leanh::lean_dec_ref_known(v_t_693_, 2);
            v___x_700_ = crate::leanh::lean_apply_2(v_k_694_, v_k_698_, v_a_699_);
            return v___x_700_;
        }
        4 => {
            let mut v_a_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_701_ = crate::leanh::lean_ctor_get(v_t_693_, 0);
            crate::leanh::lean_inc_ref(v_a_701_);
            v_k_702_ = crate::leanh::lean_ctor_get(v_t_693_, 1);
            crate::leanh::lean_inc(v_k_702_);
            crate::leanh::lean_dec_ref_known(v_t_693_, 2);
            v___x_703_ = crate::leanh::lean_apply_2(v_k_694_, v_a_701_, v_k_702_);
            return v___x_703_;
        }
        _ => {
            let mut v_v_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_v_704_ = crate::leanh::lean_ctor_get(v_t_693_, 0);
            crate::leanh::lean_inc(v_v_704_);
            crate::leanh::lean_dec_ref(v_t_693_);
            v___x_705_ = crate::leanh::lean_apply_1(v_k_694_, v_v_704_);
            return v___x_705_;
        }
    }
}
pub unsafe fn l_Nat_Linear_Expr_ctorElim(
    mut v_motive_706_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_707_: *mut crate::leanh::LeanObject,
    mut v_t_708_: *mut crate::leanh::LeanObject,
    mut v_h_709_: *mut crate::leanh::LeanObject,
    mut v_k_710_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_711_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_708_, v_k_710_);
    return v___x_711_;
}
pub unsafe fn l_Nat_Linear_Expr_ctorElim___boxed(
    mut v_motive_712_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_713_: *mut crate::leanh::LeanObject,
    mut v_t_714_: *mut crate::leanh::LeanObject,
    mut v_h_715_: *mut crate::leanh::LeanObject,
    mut v_k_716_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_717_ =
        l_Nat_Linear_Expr_ctorElim(v_motive_712_, v_ctorIdx_713_, v_t_714_, v_h_715_, v_k_716_);
    crate::leanh::lean_dec(v_ctorIdx_713_);
    return v_res_717_;
}
pub unsafe fn l_Nat_Linear_Expr_num_elim___redArg(
    mut v_t_718_: *mut crate::leanh::LeanObject,
    mut v_num_719_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_720_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_718_, v_num_719_);
    return v___x_720_;
}
pub unsafe fn l_Nat_Linear_Expr_num_elim(
    mut v_motive_721_: *mut crate::leanh::LeanObject,
    mut v_t_722_: *mut crate::leanh::LeanObject,
    mut v_h_723_: *mut crate::leanh::LeanObject,
    mut v_num_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_722_, v_num_724_);
    return v___x_725_;
}
pub unsafe fn l_Nat_Linear_Expr_var_elim___redArg(
    mut v_t_726_: *mut crate::leanh::LeanObject,
    mut v_var_727_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_728_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_726_, v_var_727_);
    return v___x_728_;
}
pub unsafe fn l_Nat_Linear_Expr_var_elim(
    mut v_motive_729_: *mut crate::leanh::LeanObject,
    mut v_t_730_: *mut crate::leanh::LeanObject,
    mut v_h_731_: *mut crate::leanh::LeanObject,
    mut v_var_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_733_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_730_, v_var_732_);
    return v___x_733_;
}
pub unsafe fn l_Nat_Linear_Expr_add_elim___redArg(
    mut v_t_734_: *mut crate::leanh::LeanObject,
    mut v_add_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_736_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_734_, v_add_735_);
    return v___x_736_;
}
pub unsafe fn l_Nat_Linear_Expr_add_elim(
    mut v_motive_737_: *mut crate::leanh::LeanObject,
    mut v_t_738_: *mut crate::leanh::LeanObject,
    mut v_h_739_: *mut crate::leanh::LeanObject,
    mut v_add_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_738_, v_add_740_);
    return v___x_741_;
}
pub unsafe fn l_Nat_Linear_Expr_mulL_elim___redArg(
    mut v_t_742_: *mut crate::leanh::LeanObject,
    mut v_mulL_743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_744_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_742_, v_mulL_743_);
    return v___x_744_;
}
pub unsafe fn l_Nat_Linear_Expr_mulL_elim(
    mut v_motive_745_: *mut crate::leanh::LeanObject,
    mut v_t_746_: *mut crate::leanh::LeanObject,
    mut v_h_747_: *mut crate::leanh::LeanObject,
    mut v_mulL_748_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_749_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_746_, v_mulL_748_);
    return v___x_749_;
}
pub unsafe fn l_Nat_Linear_Expr_mulR_elim___redArg(
    mut v_t_750_: *mut crate::leanh::LeanObject,
    mut v_mulR_751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_752_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_750_, v_mulR_751_);
    return v___x_752_;
}
pub unsafe fn l_Nat_Linear_Expr_mulR_elim(
    mut v_motive_753_: *mut crate::leanh::LeanObject,
    mut v_t_754_: *mut crate::leanh::LeanObject,
    mut v_h_755_: *mut crate::leanh::LeanObject,
    mut v_mulR_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_757_ = l_Nat_Linear_Expr_ctorElim___redArg(v_t_754_, v_mulR_756_);
    return v___x_757_;
}
pub unsafe fn l_Nat_Linear_instBEqExpr_beq(
    mut v_x_762_: *mut crate::leanh::LeanObject,
    mut v_x_763_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_v_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: u8 = 0;
    let mut v___x_767_: u8 = 0;
    let mut v_i_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_770_: u8 = 0;
    let mut v___x_771_: u8 = 0;
    let mut v_a_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: u8 = 0;
    let mut v___x_778_: u8 = 0;
    let mut v_k_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: u8 = 0;
    let mut v___x_785_: u8 = 0;
    let mut v_a_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: u8 = 0;
    let mut v___x_791_: u8 = 0;
    let mut v___x_792_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_762_) {
                0 => {
                    if crate::leanh::lean_obj_tag(v_x_763_) == 0 {
                        v_v_764_ = crate::leanh::lean_ctor_get(v_x_762_, 0);
                        v_v_765_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                        v___x_766_ = lean_nat_dec_eq(v_v_764_, v_v_765_);
                        return v___x_766_;
                    } else {
                        v___x_767_ = 0;
                        return v___x_767_;
                    }
                }
                1 => {
                    if crate::leanh::lean_obj_tag(v_x_763_) == 1 {
                        v_i_768_ = crate::leanh::lean_ctor_get(v_x_762_, 0);
                        v_i_769_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                        v___x_770_ = lean_nat_dec_eq(v_i_768_, v_i_769_);
                        return v___x_770_;
                    } else {
                        v___x_771_ = 0;
                        return v___x_771_;
                    }
                }
                2 => {
                    if crate::leanh::lean_obj_tag(v_x_763_) == 2 {
                        v_a_772_ = crate::leanh::lean_ctor_get(v_x_762_, 0);
                        v_b_773_ = crate::leanh::lean_ctor_get(v_x_762_, 1);
                        v_a_774_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                        v_b_775_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
                        v___x_776_ = l_Nat_Linear_instBEqExpr_beq(v_a_772_, v_a_774_);
                        if v___x_776_ == 0 {
                            return v___x_776_;
                        } else {
                            v_x_762_ = v_b_773_;
                            v_x_763_ = v_b_775_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_778_ = 0;
                        return v___x_778_;
                    }
                }
                3 => {
                    if crate::leanh::lean_obj_tag(v_x_763_) == 3 {
                        v_k_779_ = crate::leanh::lean_ctor_get(v_x_762_, 0);
                        v_a_780_ = crate::leanh::lean_ctor_get(v_x_762_, 1);
                        v_k_781_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                        v_a_782_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
                        v___x_783_ = lean_nat_dec_eq(v_k_779_, v_k_781_);
                        if v___x_783_ == 0 {
                            return v___x_783_;
                        } else {
                            v_x_762_ = v_a_780_;
                            v_x_763_ = v_a_782_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v___x_785_ = 0;
                        return v___x_785_;
                    }
                }
                _ => {
                    if crate::leanh::lean_obj_tag(v_x_763_) == 4 {
                        v_a_786_ = crate::leanh::lean_ctor_get(v_x_762_, 0);
                        v_k_787_ = crate::leanh::lean_ctor_get(v_x_762_, 1);
                        v_a_788_ = crate::leanh::lean_ctor_get(v_x_763_, 0);
                        v_k_789_ = crate::leanh::lean_ctor_get(v_x_763_, 1);
                        v___x_790_ = l_Nat_Linear_instBEqExpr_beq(v_a_786_, v_a_788_);
                        if v___x_790_ == 0 {
                            return v___x_790_;
                        } else {
                            v___x_791_ = lean_nat_dec_eq(v_k_787_, v_k_789_);
                            return v___x_791_;
                        }
                    } else {
                        v___x_792_ = 0;
                        return v___x_792_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_instBEqExpr_beq___boxed(
    mut v_x_793_: *mut crate::leanh::LeanObject,
    mut v_x_794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_795_: u8 = 0;
    let mut v_r_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_795_ = l_Nat_Linear_instBEqExpr_beq(v_x_793_, v_x_794_);
    crate::leanh::lean_dec_ref(v_x_794_);
    crate::leanh::lean_dec_ref(v_x_793_);
    v_r_796_ = crate::leanh::lean_box((v_res_795_) as usize);
    return v_r_796_;
}
pub unsafe fn l_Nat_Linear_Poly_insert(
    mut v_k_799_: *mut crate::leanh::LeanObject,
    mut v_v_800_: *mut crate::leanh::LeanObject,
    mut v_p_801_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: u8 = 0;
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_811_: u8 = 0;
    let mut v___x_812_: u8 = 0;
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_819_: u8 = 0;
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_827_: u8 = 0;
    let mut v_unused_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_830_: u8 = 0;
    let mut v_unused_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_840_: u8 = 0;
    let mut v_unused_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_801_) == 0 {
                    v___x_802_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_802_, 0, v_k_799_);
                    crate::leanh::lean_ctor_set(v___x_802_, 1, v_v_800_);
                    v___x_803_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_803_, 0, v___x_802_);
                    crate::leanh::lean_ctor_set(v___x_803_, 1, v_p_801_);
                    return v___x_803_;
                } else {
                    v_head_804_ = crate::leanh::lean_ctor_get(v_p_801_, 0);
                    crate::leanh::lean_inc(v_head_804_);
                    v_tail_805_ = crate::leanh::lean_ctor_get(v_p_801_, 1);
                    v_fst_806_ = crate::leanh::lean_ctor_get(v_head_804_, 0);
                    v_snd_807_ = crate::leanh::lean_ctor_get(v_head_804_, 1);
                    v___x_808_ = l_Nat_blt(v_v_800_, v_snd_807_);
                    if v___x_808_ == 0 {
                        crate::leanh::lean_inc(v_tail_805_);
                        v_isSharedCheck_830_ = (!crate::leanh::lean_is_exclusive(v_p_801_)) as u8;
                        if v_isSharedCheck_830_ == 0 {
                            v_unused_831_ = crate::leanh::lean_ctor_get(v_p_801_, 1);
                            crate::leanh::lean_dec(v_unused_831_);
                            v_unused_832_ = crate::leanh::lean_ctor_get(v_p_801_, 0);
                            crate::leanh::lean_dec(v_unused_832_);
                            v___x_810_ = v_p_801_;
                            v_isShared_811_ = v_isSharedCheck_830_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_p_801_);
                            v___x_810_ = crate::leanh::lean_box(0);
                            v_isShared_811_ = v_isSharedCheck_830_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_isSharedCheck_840_ =
                            (!crate::leanh::lean_is_exclusive(v_head_804_)) as u8;
                        if v_isSharedCheck_840_ == 0 {
                            v_unused_841_ = crate::leanh::lean_ctor_get(v_head_804_, 1);
                            crate::leanh::lean_dec(v_unused_841_);
                            v_unused_842_ = crate::leanh::lean_ctor_get(v_head_804_, 0);
                            crate::leanh::lean_dec(v_unused_842_);
                            v___x_834_ = v_head_804_;
                            v_isShared_835_ = v_isSharedCheck_840_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_head_804_);
                            v___x_834_ = crate::leanh::lean_box(0);
                            v_isShared_835_ = v_isSharedCheck_840_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_812_ = lean_nat_dec_eq(v_v_800_, v_snd_807_);
                if v___x_812_ == 0 {
                    v___x_813_ = l_Nat_Linear_Poly_insert(v_k_799_, v_v_800_, v_tail_805_);
                    if v_isShared_811_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_810_, 1, v___x_813_);
                        v___x_815_ = v___x_810_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_816_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_816_, 0, v_head_804_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_816_, 1, v___x_813_);
                        v___x_815_ = v_reuseFailAlloc_816_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_snd_807_);
                    crate::leanh::lean_inc(v_fst_806_);
                    crate::leanh::lean_dec(v_v_800_);
                    v_isSharedCheck_827_ = (!crate::leanh::lean_is_exclusive(v_head_804_)) as u8;
                    if v_isSharedCheck_827_ == 0 {
                        v_unused_828_ = crate::leanh::lean_ctor_get(v_head_804_, 1);
                        crate::leanh::lean_dec(v_unused_828_);
                        v_unused_829_ = crate::leanh::lean_ctor_get(v_head_804_, 0);
                        crate::leanh::lean_dec(v_unused_829_);
                        v___x_818_ = v_head_804_;
                        v_isShared_819_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_head_804_);
                        v___x_818_ = crate::leanh::lean_box(0);
                        v_isShared_819_ = v_isSharedCheck_827_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_815_;
            }
            3 => {
                v___x_820_ = lean_nat_add(v_k_799_, v_fst_806_);
                crate::leanh::lean_dec(v_fst_806_);
                crate::leanh::lean_dec(v_k_799_);
                if v_isShared_819_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_818_, 0, v___x_820_);
                    v___x_822_ = v___x_818_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_826_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 0, v___x_820_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_826_, 1, v_snd_807_);
                    v___x_822_ = v_reuseFailAlloc_826_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_810_, 0, v___x_822_);
                    v___x_824_ = v___x_810_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_825_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_825_, 0, v___x_822_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_825_, 1, v_tail_805_);
                    v___x_824_ = v_reuseFailAlloc_825_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_824_;
            }
            6 => {
                if v_isShared_835_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_834_, 1, v_v_800_);
                    crate::leanh::lean_ctor_set(v___x_834_, 0, v_k_799_);
                    v___x_837_ = v___x_834_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_839_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_839_, 0, v_k_799_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_839_, 1, v_v_800_);
                    v___x_837_ = v_reuseFailAlloc_839_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_838_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_838_, 0, v___x_837_);
                crate::leanh::lean_ctor_set(v___x_838_, 1, v_p_801_);
                return v___x_838_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_Poly_norm_go(
    mut v_p_843_: *mut crate::leanh::LeanObject,
    mut v_r_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_843_) == 0 {
                    return v_r_844_;
                } else {
                    v_head_845_ = crate::leanh::lean_ctor_get(v_p_843_, 0);
                    crate::leanh::lean_inc(v_head_845_);
                    v_tail_846_ = crate::leanh::lean_ctor_get(v_p_843_, 1);
                    crate::leanh::lean_inc(v_tail_846_);
                    crate::leanh::lean_dec_ref_known(v_p_843_, 2);
                    v_fst_847_ = crate::leanh::lean_ctor_get(v_head_845_, 0);
                    crate::leanh::lean_inc(v_fst_847_);
                    v_snd_848_ = crate::leanh::lean_ctor_get(v_head_845_, 1);
                    crate::leanh::lean_inc(v_snd_848_);
                    crate::leanh::lean_dec(v_head_845_);
                    v___x_849_ = l_Nat_Linear_Poly_insert(v_fst_847_, v_snd_848_, v_r_844_);
                    v_p_843_ = v_tail_846_;
                    v_r_844_ = v___x_849_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_Poly_norm(
    mut v_p_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_852_ = crate::leanh::lean_box(0);
    v___x_853_ = l_Nat_Linear_Poly_norm_go(v_p_851_, v___x_852_);
    return v___x_853_;
}
pub unsafe fn l_Nat_Linear_Poly_cancelAux(
    mut v_fuel_854_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_855_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_856_: *mut crate::leanh::LeanObject,
    mut v_r_u2081_857_: *mut crate::leanh::LeanObject,
    mut v_r_u2082_858_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_860_: u8 = 0;
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: u8 = 0;
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_887_: u8 = 0;
    let mut v___x_888_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_891_: u8 = 0;
    let mut v___x_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_894_: u8 = 0;
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: u8 = 0;
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v_unused_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_917_: u8 = 0;
    let mut v_unused_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_924_: u8 = 0;
    let mut v_unused_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_934_: u8 = 0;
    let mut v_unused_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_859_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_860_ = lean_nat_dec_eq(v_fuel_854_, v_zero_859_);
                if v_isZero_860_ == 1 {
                    crate::leanh::lean_dec(v_fuel_854_);
                    v___x_861_ = l_List_reverse___redArg(v_r_u2081_857_);
                    v___x_862_ = l_List_appendTR___redArg(v___x_861_, v_m_u2081_855_);
                    v___x_863_ = l_List_reverse___redArg(v_r_u2082_858_);
                    v___x_864_ = l_List_appendTR___redArg(v___x_863_, v_m_u2082_856_);
                    v___x_865_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_865_, 0, v___x_862_);
                    crate::leanh::lean_ctor_set(v___x_865_, 1, v___x_864_);
                    return v___x_865_;
                } else {
                    if crate::leanh::lean_obj_tag(v_m_u2082_856_) == 0 {
                        crate::leanh::lean_dec(v_fuel_854_);
                        v___x_866_ = l_List_reverse___redArg(v_r_u2081_857_);
                        v___x_867_ = l_List_appendTR___redArg(v___x_866_, v_m_u2081_855_);
                        v___x_868_ = l_List_reverse___redArg(v_r_u2082_858_);
                        v___x_869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_867_);
                        crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_868_);
                        return v___x_869_;
                    } else {
                        if crate::leanh::lean_obj_tag(v_m_u2081_855_) == 0 {
                            crate::leanh::lean_dec(v_fuel_854_);
                            v___x_870_ = l_List_reverse___redArg(v_r_u2081_857_);
                            v___x_871_ = l_List_reverse___redArg(v_r_u2082_858_);
                            v___x_872_ = l_List_appendTR___redArg(v___x_871_, v_m_u2082_856_);
                            v___x_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_870_);
                            crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
                            return v___x_873_;
                        } else {
                            v_head_874_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 0);
                            v_head_875_ = crate::leanh::lean_ctor_get(v_m_u2082_856_, 0);
                            crate::leanh::lean_inc(v_head_875_);
                            v_tail_876_ = crate::leanh::lean_ctor_get(v_m_u2082_856_, 1);
                            v_tail_877_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 1);
                            v_fst_878_ = crate::leanh::lean_ctor_get(v_head_874_, 0);
                            v_snd_879_ = crate::leanh::lean_ctor_get(v_head_874_, 1);
                            v_fst_880_ = crate::leanh::lean_ctor_get(v_head_875_, 0);
                            v_snd_881_ = crate::leanh::lean_ctor_get(v_head_875_, 1);
                            v_one_882_ = crate::leanh::lean_unsigned_to_nat(1);
                            v_n_883_ = lean_nat_sub(v_fuel_854_, v_one_882_);
                            crate::leanh::lean_dec(v_fuel_854_);
                            v___x_884_ = l_Nat_blt(v_snd_879_, v_snd_881_);
                            if v___x_884_ == 0 {
                                crate::leanh::lean_inc(v_tail_876_);
                                v_isSharedCheck_924_ =
                                    (!crate::leanh::lean_is_exclusive(v_m_u2082_856_)) as u8;
                                if v_isSharedCheck_924_ == 0 {
                                    v_unused_925_ = crate::leanh::lean_ctor_get(v_m_u2082_856_, 1);
                                    crate::leanh::lean_dec(v_unused_925_);
                                    v_unused_926_ = crate::leanh::lean_ctor_get(v_m_u2082_856_, 0);
                                    crate::leanh::lean_dec(v_unused_926_);
                                    v___x_886_ = v_m_u2082_856_;
                                    v_isShared_887_ = v_isSharedCheck_924_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_m_u2082_856_);
                                    v___x_886_ = crate::leanh::lean_box(0);
                                    v_isShared_887_ = v_isSharedCheck_924_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_inc(v_tail_877_);
                                crate::leanh::lean_inc(v_head_874_);
                                crate::leanh::lean_dec(v_head_875_);
                                v_isSharedCheck_934_ =
                                    (!crate::leanh::lean_is_exclusive(v_m_u2081_855_)) as u8;
                                if v_isSharedCheck_934_ == 0 {
                                    v_unused_935_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 1);
                                    crate::leanh::lean_dec(v_unused_935_);
                                    v_unused_936_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 0);
                                    crate::leanh::lean_dec(v_unused_936_);
                                    v___x_928_ = v_m_u2081_855_;
                                    v_isShared_929_ = v_isSharedCheck_934_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_m_u2081_855_);
                                    v___x_928_ = crate::leanh::lean_box(0);
                                    v_isShared_929_ = v_isSharedCheck_934_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_888_ = l_Nat_blt(v_snd_881_, v_snd_879_);
                if v___x_888_ == 0 {
                    crate::leanh::lean_inc(v_fst_880_);
                    crate::leanh::lean_inc(v_snd_879_);
                    crate::leanh::lean_inc(v_fst_878_);
                    crate::leanh::lean_inc(v_tail_877_);
                    crate::leanh::lean_del_object(v___x_886_);
                    v_isSharedCheck_917_ = (!crate::leanh::lean_is_exclusive(v_m_u2081_855_)) as u8;
                    if v_isSharedCheck_917_ == 0 {
                        v_unused_918_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 1);
                        crate::leanh::lean_dec(v_unused_918_);
                        v_unused_919_ = crate::leanh::lean_ctor_get(v_m_u2081_855_, 0);
                        crate::leanh::lean_dec(v_unused_919_);
                        v___x_890_ = v_m_u2081_855_;
                        v_isShared_891_ = v_isSharedCheck_917_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_u2081_855_);
                        v___x_890_ = crate::leanh::lean_box(0);
                        v_isShared_891_ = v_isSharedCheck_917_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_887_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_886_, 1, v_r_u2082_858_);
                        v___x_921_ = v___x_886_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_923_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_923_, 0, v_head_875_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_923_, 1, v_r_u2082_858_);
                        v___x_921_ = v_reuseFailAlloc_923_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_isSharedCheck_914_ = (!crate::leanh::lean_is_exclusive(v_head_875_)) as u8;
                if v_isSharedCheck_914_ == 0 {
                    v_unused_915_ = crate::leanh::lean_ctor_get(v_head_875_, 1);
                    crate::leanh::lean_dec(v_unused_915_);
                    v_unused_916_ = crate::leanh::lean_ctor_get(v_head_875_, 0);
                    crate::leanh::lean_dec(v_unused_916_);
                    v___x_893_ = v_head_875_;
                    v_isShared_894_ = v_isSharedCheck_914_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_head_875_);
                    v___x_893_ = crate::leanh::lean_box(0);
                    v_isShared_894_ = v_isSharedCheck_914_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_895_ = l_Nat_blt(v_fst_878_, v_fst_880_);
                if v___x_895_ == 0 {
                    v___x_896_ = l_Nat_blt(v_fst_880_, v_fst_878_);
                    if v___x_896_ == 0 {
                        crate::leanh::lean_del_object(v___x_893_);
                        crate::leanh::lean_del_object(v___x_890_);
                        crate::leanh::lean_dec(v_fst_880_);
                        crate::leanh::lean_dec(v_snd_879_);
                        crate::leanh::lean_dec(v_fst_878_);
                        v_fuel_854_ = v_n_883_;
                        v_m_u2081_855_ = v_tail_877_;
                        v_m_u2082_856_ = v_tail_876_;
                        state = 0;
                        continue;
                    } else {
                        v___x_898_ = lean_nat_sub(v_fst_878_, v_fst_880_);
                        crate::leanh::lean_dec(v_fst_880_);
                        crate::leanh::lean_dec(v_fst_878_);
                        if v_isShared_894_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_893_, 1, v_snd_879_);
                            crate::leanh::lean_ctor_set(v___x_893_, 0, v___x_898_);
                            v___x_900_ = v___x_893_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_905_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 0, v___x_898_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_905_, 1, v_snd_879_);
                            v___x_900_ = v_reuseFailAlloc_905_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v___x_906_ = lean_nat_sub(v_fst_880_, v_fst_878_);
                    crate::leanh::lean_dec(v_fst_878_);
                    crate::leanh::lean_dec(v_fst_880_);
                    if v_isShared_894_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_893_, 1, v_snd_879_);
                        crate::leanh::lean_ctor_set(v___x_893_, 0, v___x_906_);
                        v___x_908_ = v___x_893_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_913_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_906_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_913_, 1, v_snd_879_);
                        v___x_908_ = v_reuseFailAlloc_913_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_890_, 1, v_r_u2081_857_);
                    crate::leanh::lean_ctor_set(v___x_890_, 0, v___x_900_);
                    v___x_902_ = v___x_890_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_904_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_904_, 0, v___x_900_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_904_, 1, v_r_u2081_857_);
                    v___x_902_ = v_reuseFailAlloc_904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_fuel_854_ = v_n_883_;
                v_m_u2081_855_ = v_tail_877_;
                v_m_u2082_856_ = v_tail_876_;
                v_r_u2081_857_ = v___x_902_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_891_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_890_, 1, v_r_u2082_858_);
                    crate::leanh::lean_ctor_set(v___x_890_, 0, v___x_908_);
                    v___x_910_ = v___x_890_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_912_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_912_, 1, v_r_u2082_858_);
                    v___x_910_ = v_reuseFailAlloc_912_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v_fuel_854_ = v_n_883_;
                v_m_u2081_855_ = v_tail_877_;
                v_m_u2082_856_ = v_tail_876_;
                v_r_u2082_858_ = v___x_910_;
                state = 0;
                continue;
            }
            8 => {
                v_fuel_854_ = v_n_883_;
                v_m_u2082_856_ = v_tail_876_;
                v_r_u2082_858_ = v___x_921_;
                state = 0;
                continue;
            }
            9 => {
                if v_isShared_929_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_928_, 1, v_r_u2081_857_);
                    v___x_931_ = v___x_928_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_933_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 0, v_head_874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_933_, 1, v_r_u2081_857_);
                    v___x_931_ = v_reuseFailAlloc_933_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_fuel_854_ = v_n_883_;
                v_m_u2081_855_ = v_tail_877_;
                v_r_u2081_857_ = v___x_931_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Nat_Linear_hugeFuel() -> *mut crate::leanh::LeanObject {
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_937_ = crate::leanh::lean_unsigned_to_nat(1000000);
    return v___x_937_;
}
pub unsafe fn l_Nat_Linear_Poly_cancel(
    mut v_p_u2081_938_: *mut crate::leanh::LeanObject,
    mut v_p_u2082_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = crate::leanh::lean_unsigned_to_nat(1000000);
    v___x_941_ = crate::leanh::lean_box(0);
    v___x_942_ = l_Nat_Linear_Poly_cancelAux(
        v___x_940_,
        v_p_u2081_938_,
        v_p_u2082_939_,
        v___x_941_,
        v___x_941_,
    );
    return v___x_942_;
}
pub unsafe fn l_Nat_Linear_Poly_isNum_x3f(
    mut v_p_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_945_) == 0 {
        let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_946_ = l_Nat_Linear_Poly_isNum_x3f___closed__0;
        return v___x_946_;
    } else {
        let mut v_tail_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_tail_947_ = crate::leanh::lean_ctor_get(v_p_945_, 1);
        if crate::leanh::lean_obj_tag(v_tail_947_) == 0 {
            let mut v_head_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_952_: u8 = 0;
            v_head_948_ = crate::leanh::lean_ctor_get(v_p_945_, 0);
            v_fst_949_ = crate::leanh::lean_ctor_get(v_head_948_, 0);
            v_snd_950_ = crate::leanh::lean_ctor_get(v_head_948_, 1);
            v___x_951_ = crate::leanh::lean_unsigned_to_nat(100000000);
            v___x_952_ = lean_nat_dec_eq(v_snd_950_, v___x_951_);
            if v___x_952_ == 0 {
                let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_953_ = crate::leanh::lean_box(0);
                return v___x_953_;
            } else {
                let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_inc(v_fst_949_);
                v___x_954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_954_, 0, v_fst_949_);
                return v___x_954_;
            }
        } else {
            let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_955_ = crate::leanh::lean_box(0);
            return v___x_955_;
        }
    }
}
pub unsafe fn l_Nat_Linear_Poly_isNum_x3f___boxed(
    mut v_p_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_Nat_Linear_Poly_isNum_x3f(v_p_956_);
    crate::leanh::lean_dec(v_p_956_);
    return v_res_957_;
}
pub unsafe fn l_Nat_Linear_Poly_isZero(mut v_p_958_: *mut crate::leanh::LeanObject) -> u8 {
    if crate::leanh::lean_obj_tag(v_p_958_) == 0 {
        let mut v___x_959_: u8 = 0;
        v___x_959_ = 1;
        return v___x_959_;
    } else {
        let mut v___x_960_: u8 = 0;
        v___x_960_ = 0;
        return v___x_960_;
    }
}
pub unsafe fn l_Nat_Linear_Poly_isZero___boxed(
    mut v_p_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: u8 = 0;
    let mut v_r_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ = l_Nat_Linear_Poly_isZero(v_p_961_);
    crate::leanh::lean_dec(v_p_961_);
    v_r_963_ = crate::leanh::lean_box((v_res_962_) as usize);
    return v_r_963_;
}
pub unsafe fn l_Nat_Linear_Poly_isNonZero(mut v_p_964_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_965_: u8 = 0;
    let mut v_head_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: u8 = 0;
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_964_) == 0 {
                    v___x_965_ = 0;
                    return v___x_965_;
                } else {
                    v_head_966_ = crate::leanh::lean_ctor_get(v_p_964_, 0);
                    v_tail_967_ = crate::leanh::lean_ctor_get(v_p_964_, 1);
                    v_fst_968_ = crate::leanh::lean_ctor_get(v_head_966_, 0);
                    v_snd_969_ = crate::leanh::lean_ctor_get(v_head_966_, 1);
                    v___x_970_ = crate::leanh::lean_unsigned_to_nat(100000000);
                    v___x_971_ = lean_nat_dec_eq(v_snd_969_, v___x_970_);
                    if v___x_971_ == 0 {
                        v_p_964_ = v_tail_967_;
                        state = 0;
                        continue;
                    } else {
                        v___x_973_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_974_ = lean_nat_dec_lt(v___x_973_, v_fst_968_);
                        return v___x_974_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_Poly_isNonZero___boxed(
    mut v_p_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_976_: u8 = 0;
    let mut v_r_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_976_ = l_Nat_Linear_Poly_isNonZero(v_p_975_);
    crate::leanh::lean_dec(v_p_975_);
    v_r_977_ = crate::leanh::lean_box((v_res_976_) as usize);
    return v_r_977_;
}
pub unsafe fn l_Nat_Linear_Expr_toPoly_go(
    mut v_coeff_978_: *mut crate::leanh::LeanObject,
    mut v_a_979_: *mut crate::leanh::LeanObject,
    mut v_a_980_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: u8 = 0;
    let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: u8 = 0;
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u8 = 0;
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_a_979_) {
                0 => {
                    v_v_981_ = crate::leanh::lean_ctor_get(v_a_979_, 0);
                    v___x_982_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_983_ = lean_nat_dec_eq(v_v_981_, v___x_982_);
                    if v___x_983_ == 0 {
                        v___x_984_ = lean_nat_mul(v_coeff_978_, v_v_981_);
                        crate::leanh::lean_dec(v_coeff_978_);
                        v___x_985_ = crate::leanh::lean_unsigned_to_nat(100000000);
                        v___x_986_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_986_, 0, v___x_984_);
                        crate::leanh::lean_ctor_set(v___x_986_, 1, v___x_985_);
                        v___x_987_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_987_, 0, v___x_986_);
                        crate::leanh::lean_ctor_set(v___x_987_, 1, v_a_980_);
                        return v___x_987_;
                    } else {
                        crate::leanh::lean_dec(v_coeff_978_);
                        return v_a_980_;
                    }
                }
                1 => {
                    v_i_988_ = crate::leanh::lean_ctor_get(v_a_979_, 0);
                    crate::leanh::lean_inc(v_i_988_);
                    v___x_989_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_989_, 0, v_coeff_978_);
                    crate::leanh::lean_ctor_set(v___x_989_, 1, v_i_988_);
                    v___x_990_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_990_, 0, v___x_989_);
                    crate::leanh::lean_ctor_set(v___x_990_, 1, v_a_980_);
                    return v___x_990_;
                }
                2 => {
                    v_a_991_ = crate::leanh::lean_ctor_get(v_a_979_, 0);
                    v_b_992_ = crate::leanh::lean_ctor_get(v_a_979_, 1);
                    crate::leanh::lean_inc(v_coeff_978_);
                    v___x_993_ = l_Nat_Linear_Expr_toPoly_go(v_coeff_978_, v_b_992_, v_a_980_);
                    v_a_979_ = v_a_991_;
                    v_a_980_ = v___x_993_;
                    state = 0;
                    continue;
                }
                3 => {
                    v_k_995_ = crate::leanh::lean_ctor_get(v_a_979_, 0);
                    v_a_996_ = crate::leanh::lean_ctor_get(v_a_979_, 1);
                    v___x_997_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_998_ = lean_nat_dec_eq(v_k_995_, v___x_997_);
                    if v___x_998_ == 0 {
                        v___x_999_ = lean_nat_mul(v_coeff_978_, v_k_995_);
                        crate::leanh::lean_dec(v_coeff_978_);
                        v_coeff_978_ = v___x_999_;
                        v_a_979_ = v_a_996_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_coeff_978_);
                        return v_a_980_;
                    }
                }
                _ => {
                    v_a_1001_ = crate::leanh::lean_ctor_get(v_a_979_, 0);
                    v_k_1002_ = crate::leanh::lean_ctor_get(v_a_979_, 1);
                    v___x_1003_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1004_ = lean_nat_dec_eq(v_k_1002_, v___x_1003_);
                    if v___x_1004_ == 0 {
                        v___x_1005_ = lean_nat_mul(v_coeff_978_, v_k_1002_);
                        crate::leanh::lean_dec(v_coeff_978_);
                        v_coeff_978_ = v___x_1005_;
                        v_a_979_ = v_a_1001_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_coeff_978_);
                        return v_a_980_;
                    }
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_Expr_toPoly_go___boxed(
    mut v_coeff_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1010_ = l_Nat_Linear_Expr_toPoly_go(v_coeff_1007_, v_a_1008_, v_a_1009_);
    crate::leanh::lean_dec_ref(v_a_1008_);
    return v_res_1010_;
}
pub unsafe fn l_Nat_Linear_Expr_toPoly(
    mut v_e_1011_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1012_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_1013_ = crate::leanh::lean_box(0);
    v___x_1014_ = l_Nat_Linear_Expr_toPoly_go(v___x_1012_, v_e_1011_, v___x_1013_);
    return v___x_1014_;
}
pub unsafe fn l_Nat_Linear_Expr_toPoly___boxed(
    mut v_e_1015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1016_ = l_Nat_Linear_Expr_toPoly(v_e_1015_);
    crate::leanh::lean_dec_ref(v_e_1015_);
    return v_res_1016_;
}
pub unsafe fn l_Nat_Linear_Expr_toNormPoly(
    mut v_e_1017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1018_ = l_Nat_Linear_Expr_toPoly(v_e_1017_);
    v___x_1019_ = l_Nat_Linear_Poly_norm(v___x_1018_);
    return v___x_1019_;
}
pub unsafe fn l_Nat_Linear_Expr_toNormPoly___boxed(
    mut v_e_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l_Nat_Linear_Expr_toNormPoly(v_e_1020_);
    crate::leanh::lean_dec_ref(v_e_1020_);
    return v_res_1021_;
}
pub unsafe fn l_Nat_Linear_Expr_inc(
    mut v_e_1024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1025_ = l_Nat_Linear_Expr_inc___closed__0;
    v___x_1026_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1026_, 0, v_e_1024_);
    crate::leanh::lean_ctor_set(v___x_1026_, 1, v___x_1025_);
    return v___x_1026_;
}
pub unsafe fn l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(
    mut v_x_1027_: *mut crate::leanh::LeanObject,
    mut v_x_1028_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1029_: u8 = 0;
    let mut v___x_1030_: u8 = 0;
    let mut v___x_1031_: u8 = 0;
    let mut v_head_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1037_: u8 = 0;
    let mut v_fst_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: u8 = 0;
    let mut v___x_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1027_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_1028_) == 0 {
                        v___x_1029_ = 1;
                        return v___x_1029_;
                    } else {
                        v___x_1030_ = 0;
                        return v___x_1030_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_x_1028_) == 0 {
                        v___x_1031_ = 0;
                        return v___x_1031_;
                    } else {
                        v_head_1032_ = crate::leanh::lean_ctor_get(v_x_1027_, 0);
                        v_tail_1033_ = crate::leanh::lean_ctor_get(v_x_1027_, 1);
                        v_head_1034_ = crate::leanh::lean_ctor_get(v_x_1028_, 0);
                        v_tail_1035_ = crate::leanh::lean_ctor_get(v_x_1028_, 1);
                        v_fst_1039_ = crate::leanh::lean_ctor_get(v_head_1032_, 0);
                        v_snd_1040_ = crate::leanh::lean_ctor_get(v_head_1032_, 1);
                        v_fst_1041_ = crate::leanh::lean_ctor_get(v_head_1034_, 0);
                        v_snd_1042_ = crate::leanh::lean_ctor_get(v_head_1034_, 1);
                        v___x_1043_ = lean_nat_dec_eq(v_fst_1039_, v_fst_1041_);
                        if v___x_1043_ == 0 {
                            v___y_1037_ = v___x_1043_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1044_ = lean_nat_dec_eq(v_snd_1040_, v_snd_1042_);
                            v___y_1037_ = v___x_1044_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v___y_1037_ == 0 {
                    return v___y_1037_;
                } else {
                    v_x_1027_ = v_tail_1033_;
                    v_x_1028_ = v_tail_1035_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0___boxed(
    mut v_x_1045_: *mut crate::leanh::LeanObject,
    mut v_x_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1047_: u8 = 0;
    let mut v_r_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1047_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(v_x_1045_, v_x_1046_);
    crate::leanh::lean_dec(v_x_1046_);
    crate::leanh::lean_dec(v_x_1045_);
    v_r_1048_ = crate::leanh::lean_box((v_res_1047_) as usize);
    return v_r_1048_;
}
pub unsafe fn l_Nat_Linear_instBEqPolyCnstr_beq(
    mut v_x_1049_: *mut crate::leanh::LeanObject,
    mut v_x_1050_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_eq_1051_: u8 = 0;
    let mut v_lhs_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_1054_: u8 = 0;
    let mut v_lhs_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1051_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1049_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1052_ = crate::leanh::lean_ctor_get(v_x_1049_, 0);
                v_rhs_1053_ = crate::leanh::lean_ctor_get(v_x_1049_, 1);
                v_eq_1054_ = crate::leanh::lean_ctor_get_uint8(
                    v_x_1050_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1055_ = crate::leanh::lean_ctor_get(v_x_1050_, 0);
                v_rhs_1056_ = crate::leanh::lean_ctor_get(v_x_1050_, 1);
                if v_eq_1051_ == 0 {
                    if v_eq_1054_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v_eq_1051_;
                    }
                } else {
                    if v_eq_1054_ == 0 {
                        return v_eq_1054_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1058_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(
                    v_lhs_1052_,
                    v_lhs_1055_,
                );
                if v___x_1058_ == 0 {
                    return v___x_1058_;
                } else {
                    v___x_1059_ = l_List_beq___at___00Nat_Linear_instBEqPolyCnstr_beq_spec__0(
                        v_rhs_1053_,
                        v_rhs_1056_,
                    );
                    return v___x_1059_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_instBEqPolyCnstr_beq___boxed(
    mut v_x_1060_: *mut crate::leanh::LeanObject,
    mut v_x_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1062_: u8 = 0;
    let mut v_r_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Nat_Linear_instBEqPolyCnstr_beq(v_x_1060_, v_x_1061_);
    crate::leanh::lean_dec_ref(v_x_1061_);
    crate::leanh::lean_dec_ref(v_x_1060_);
    v_r_1063_ = crate::leanh::lean_box((v_res_1062_) as usize);
    return v_r_1063_;
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___redArg(
    mut v_x_1066_: *mut crate::leanh::LeanObject,
    mut v_x_1067_: *mut crate::leanh::LeanObject,
    mut v_h__1_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1069_: u8 = 0;
    let mut v_lhs_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_1072_: u8 = 0;
    let mut v_lhs_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_eq_1069_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1066_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_1070_ = crate::leanh::lean_ctor_get(v_x_1066_, 0);
    crate::leanh::lean_inc(v_lhs_1070_);
    v_rhs_1071_ = crate::leanh::lean_ctor_get(v_x_1066_, 1);
    crate::leanh::lean_inc(v_rhs_1071_);
    crate::leanh::lean_dec_ref(v_x_1066_);
    v_eq_1072_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1067_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_1073_ = crate::leanh::lean_ctor_get(v_x_1067_, 0);
    crate::leanh::lean_inc(v_lhs_1073_);
    v_rhs_1074_ = crate::leanh::lean_ctor_get(v_x_1067_, 1);
    crate::leanh::lean_inc(v_rhs_1074_);
    crate::leanh::lean_dec_ref(v_x_1067_);
    v___x_1075_ = crate::leanh::lean_box((v_eq_1069_) as usize);
    v___x_1076_ = crate::leanh::lean_box((v_eq_1072_) as usize);
    v___x_1077_ = crate::leanh::lean_apply_6(
        v_h__1_1068_,
        v___x_1075_,
        v_lhs_1070_,
        v_rhs_1071_,
        v___x_1076_,
        v_lhs_1073_,
        v_rhs_1074_,
    );
    return v___x_1077_;
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(
    mut v_motive_1078_: *mut crate::leanh::LeanObject,
    mut v_x_1079_: *mut crate::leanh::LeanObject,
    mut v_x_1080_: *mut crate::leanh::LeanObject,
    mut v_h__1_1081_: *mut crate::leanh::LeanObject,
    mut v_h__2_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1083_: u8 = 0;
    let mut v_lhs_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eq_1086_: u8 = 0;
    let mut v_lhs_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_eq_1083_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1079_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_1084_ = crate::leanh::lean_ctor_get(v_x_1079_, 0);
    crate::leanh::lean_inc(v_lhs_1084_);
    v_rhs_1085_ = crate::leanh::lean_ctor_get(v_x_1079_, 1);
    crate::leanh::lean_inc(v_rhs_1085_);
    crate::leanh::lean_dec_ref(v_x_1079_);
    v_eq_1086_ = crate::leanh::lean_ctor_get_uint8(
        v_x_1080_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    v_lhs_1087_ = crate::leanh::lean_ctor_get(v_x_1080_, 0);
    crate::leanh::lean_inc(v_lhs_1087_);
    v_rhs_1088_ = crate::leanh::lean_ctor_get(v_x_1080_, 1);
    crate::leanh::lean_inc(v_rhs_1088_);
    crate::leanh::lean_dec_ref(v_x_1080_);
    v___x_1089_ = crate::leanh::lean_box((v_eq_1083_) as usize);
    v___x_1090_ = crate::leanh::lean_box((v_eq_1086_) as usize);
    v___x_1091_ = crate::leanh::lean_apply_6(
        v_h__1_1081_,
        v___x_1089_,
        v_lhs_1084_,
        v_rhs_1085_,
        v___x_1090_,
        v_lhs_1087_,
        v_rhs_1088_,
    );
    return v___x_1091_;
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter___boxed(
    mut v_motive_1092_: *mut crate::leanh::LeanObject,
    mut v_x_1093_: *mut crate::leanh::LeanObject,
    mut v_x_1094_: *mut crate::leanh::LeanObject,
    mut v_h__1_1095_: *mut crate::leanh::LeanObject,
    mut v_h__2_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1097_ =
        l___private_Init_Data_Nat_Linear_0__Nat_Linear_instBEqPolyCnstr_beq_match__1_splitter(
            v_motive_1092_,
            v_x_1093_,
            v_x_1094_,
            v_h__1_1095_,
            v_h__2_1096_,
        );
    crate::leanh::lean_dec(v_h__2_1096_);
    return v_res_1097_;
}
pub unsafe fn l_Nat_Linear_PolyCnstr_norm(
    mut v_c_1098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1099_: u8 = 0;
    let mut v_lhs_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1104_: u8 = 0;
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1113_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1099_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1098_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1100_ = crate::leanh::lean_ctor_get(v_c_1098_, 0);
                v_rhs_1101_ = crate::leanh::lean_ctor_get(v_c_1098_, 1);
                v_isSharedCheck_1113_ = (!crate::leanh::lean_is_exclusive(v_c_1098_)) as u8;
                if v_isSharedCheck_1113_ == 0 {
                    v___x_1103_ = v_c_1098_;
                    v_isShared_1104_ = v_isSharedCheck_1113_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1101_);
                    crate::leanh::lean_inc(v_lhs_1100_);
                    crate::leanh::lean_dec(v_c_1098_);
                    v___x_1103_ = crate::leanh::lean_box(0);
                    v_isShared_1104_ = v_isSharedCheck_1113_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1105_ = l_Nat_Linear_Poly_norm(v_lhs_1100_);
                v___x_1106_ = l_Nat_Linear_Poly_norm(v_rhs_1101_);
                v___x_1107_ = l_Nat_Linear_Poly_cancel(v___x_1105_, v___x_1106_);
                v_fst_1108_ = crate::leanh::lean_ctor_get(v___x_1107_, 0);
                crate::leanh::lean_inc(v_fst_1108_);
                v_snd_1109_ = crate::leanh::lean_ctor_get(v___x_1107_, 1);
                crate::leanh::lean_inc(v_snd_1109_);
                crate::leanh::lean_dec_ref(v___x_1107_);
                if v_isShared_1104_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1103_, 1, v_snd_1109_);
                    crate::leanh::lean_ctor_set(v___x_1103_, 0, v_fst_1108_);
                    v___x_1111_ = v___x_1103_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1112_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 0, v_fst_1108_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1112_, 1, v_snd_1109_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1112_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_eq_1099_,
                    );
                    v___x_1111_ = v_reuseFailAlloc_1112_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1111_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_PolyCnstr_isUnsat(mut v_c_1114_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_eq_1115_: u8 = 0;
    let mut v_lhs_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1119_: u8 = 0;
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: u8 = 0;
    let mut v___x_1122_: u8 = 0;
    let mut v___x_1123_: u8 = 0;
    let mut v___x_1124_: u8 = 0;
    let mut v___x_1125_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1115_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1114_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1116_ = crate::leanh::lean_ctor_get(v_c_1114_, 0);
                v_rhs_1117_ = crate::leanh::lean_ctor_get(v_c_1114_, 1);
                if v_eq_1115_ == 0 {
                    v___x_1122_ = l_Nat_Linear_Poly_isNonZero(v_lhs_1116_);
                    if v___x_1122_ == 0 {
                        return v___x_1122_;
                    } else {
                        v___x_1123_ = l_Nat_Linear_Poly_isZero(v_rhs_1117_);
                        return v___x_1123_;
                    }
                } else {
                    v___x_1124_ = l_Nat_Linear_Poly_isZero(v_lhs_1116_);
                    if v___x_1124_ == 0 {
                        v___y_1119_ = v___x_1124_;
                        state = 1;
                        continue;
                    } else {
                        v___x_1125_ = l_Nat_Linear_Poly_isNonZero(v_rhs_1117_);
                        v___y_1119_ = v___x_1125_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_1119_ == 0 {
                    v___x_1120_ = l_Nat_Linear_Poly_isNonZero(v_lhs_1116_);
                    if v___x_1120_ == 0 {
                        return v___x_1120_;
                    } else {
                        v___x_1121_ = l_Nat_Linear_Poly_isZero(v_rhs_1117_);
                        return v___x_1121_;
                    }
                } else {
                    return v___y_1119_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_PolyCnstr_isUnsat___boxed(
    mut v_c_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1127_: u8 = 0;
    let mut v_r_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_Nat_Linear_PolyCnstr_isUnsat(v_c_1126_);
    crate::leanh::lean_dec_ref(v_c_1126_);
    v_r_1128_ = crate::leanh::lean_box((v_res_1127_) as usize);
    return v_r_1128_;
}
pub unsafe fn l_Nat_Linear_PolyCnstr_isValid(mut v_c_1129_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v_eq_1130_: u8 = 0;
    v_eq_1130_ = crate::leanh::lean_ctor_get_uint8(
        v_c_1129_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
    );
    if v_eq_1130_ == 0 {
        let mut v_lhs_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1132_: u8 = 0;
        v_lhs_1131_ = crate::leanh::lean_ctor_get(v_c_1129_, 0);
        v___x_1132_ = l_Nat_Linear_Poly_isZero(v_lhs_1131_);
        return v___x_1132_;
    } else {
        let mut v_lhs_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_rhs_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1135_: u8 = 0;
        v_lhs_1133_ = crate::leanh::lean_ctor_get(v_c_1129_, 0);
        v_rhs_1134_ = crate::leanh::lean_ctor_get(v_c_1129_, 1);
        v___x_1135_ = l_Nat_Linear_Poly_isZero(v_lhs_1133_);
        if v___x_1135_ == 0 {
            return v___x_1135_;
        } else {
            let mut v___x_1136_: u8 = 0;
            v___x_1136_ = l_Nat_Linear_Poly_isZero(v_rhs_1134_);
            return v___x_1136_;
        }
    }
}
pub unsafe fn l_Nat_Linear_PolyCnstr_isValid___boxed(
    mut v_c_1137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1138_: u8 = 0;
    let mut v_r_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Nat_Linear_PolyCnstr_isValid(v_c_1137_);
    crate::leanh::lean_dec_ref(v_c_1137_);
    v_r_1139_ = crate::leanh::lean_box((v_res_1138_) as usize);
    return v_r_1139_;
}
pub unsafe fn l_Nat_Linear_ExprCnstr_toPoly(
    mut v_c_1140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1141_: u8 = 0;
    let mut v_lhs_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1146_: u8 = 0;
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1141_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1140_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1142_ = crate::leanh::lean_ctor_get(v_c_1140_, 0);
                v_rhs_1143_ = crate::leanh::lean_ctor_get(v_c_1140_, 1);
                v_isSharedCheck_1152_ = (!crate::leanh::lean_is_exclusive(v_c_1140_)) as u8;
                if v_isSharedCheck_1152_ == 0 {
                    v___x_1145_ = v_c_1140_;
                    v_isShared_1146_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1143_);
                    crate::leanh::lean_inc(v_lhs_1142_);
                    crate::leanh::lean_dec(v_c_1140_);
                    v___x_1145_ = crate::leanh::lean_box(0);
                    v_isShared_1146_ = v_isSharedCheck_1152_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1147_ = l_Nat_Linear_Expr_toPoly(v_lhs_1142_);
                crate::leanh::lean_dec_ref(v_lhs_1142_);
                v___x_1148_ = l_Nat_Linear_Expr_toPoly(v_rhs_1143_);
                crate::leanh::lean_dec_ref(v_rhs_1143_);
                if v_isShared_1146_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1145_, 1, v___x_1148_);
                    crate::leanh::lean_ctor_set(v___x_1145_, 0, v___x_1147_);
                    v___x_1150_ = v___x_1145_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1151_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 0, v___x_1147_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1151_, 1, v___x_1148_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1151_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_eq_1141_,
                    );
                    v___x_1150_ = v_reuseFailAlloc_1151_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_ExprCnstr_toNormPoly(
    mut v_c_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1154_: u8 = 0;
    let mut v_lhs_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1168_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1154_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1153_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1155_ = crate::leanh::lean_ctor_get(v_c_1153_, 0);
                v_rhs_1156_ = crate::leanh::lean_ctor_get(v_c_1153_, 1);
                v_isSharedCheck_1168_ = (!crate::leanh::lean_is_exclusive(v_c_1153_)) as u8;
                if v_isSharedCheck_1168_ == 0 {
                    v___x_1158_ = v_c_1153_;
                    v_isShared_1159_ = v_isSharedCheck_1168_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1156_);
                    crate::leanh::lean_inc(v_lhs_1155_);
                    crate::leanh::lean_dec(v_c_1153_);
                    v___x_1158_ = crate::leanh::lean_box(0);
                    v_isShared_1159_ = v_isSharedCheck_1168_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1160_ = l_Nat_Linear_Expr_toNormPoly(v_lhs_1155_);
                crate::leanh::lean_dec_ref(v_lhs_1155_);
                v___x_1161_ = l_Nat_Linear_Expr_toNormPoly(v_rhs_1156_);
                crate::leanh::lean_dec_ref(v_rhs_1156_);
                v___x_1162_ = l_Nat_Linear_Poly_cancel(v___x_1160_, v___x_1161_);
                v_fst_1163_ = crate::leanh::lean_ctor_get(v___x_1162_, 0);
                crate::leanh::lean_inc(v_fst_1163_);
                v_snd_1164_ = crate::leanh::lean_ctor_get(v___x_1162_, 1);
                crate::leanh::lean_inc(v_snd_1164_);
                crate::leanh::lean_dec_ref(v___x_1162_);
                if v_isShared_1159_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1158_, 1, v_snd_1164_);
                    crate::leanh::lean_ctor_set(v___x_1158_, 0, v_fst_1163_);
                    v___x_1166_ = v___x_1158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1167_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_fst_1163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_snd_1164_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1167_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_eq_1154_,
                    );
                    v___x_1166_ = v_reuseFailAlloc_1167_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1166_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_monomialToExpr(
    mut v_k_1169_: *mut crate::leanh::LeanObject,
    mut v_v_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1172_: u8 = 0;
    v___x_1171_ = crate::leanh::lean_unsigned_to_nat(100000000);
    v___x_1172_ = lean_nat_dec_eq(v_v_1170_, v___x_1171_);
    if v___x_1172_ == 0 {
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: u8 = 0;
        v___x_1173_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1174_ = lean_nat_dec_eq(v_k_1169_, v___x_1173_);
        if v___x_1174_ == 0 {
            let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1175_, 0, v_v_1170_);
            v___x_1176_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1176_, 0, v_k_1169_);
            crate::leanh::lean_ctor_set(v___x_1176_, 1, v___x_1175_);
            return v___x_1176_;
        } else {
            let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_k_1169_);
            v___x_1177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1177_, 0, v_v_1170_);
            return v___x_1177_;
        }
    } else {
        let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_v_1170_);
        v___x_1178_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1178_, 0, v_k_1169_);
        return v___x_1178_;
    }
}
pub unsafe fn l_Nat_Linear_Poly_toExpr_go(
    mut v_e_1179_: *mut crate::leanh::LeanObject,
    mut v_p_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_head_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1187_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1193_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_1180_) == 0 {
                    return v_e_1179_;
                } else {
                    v_head_1181_ = crate::leanh::lean_ctor_get(v_p_1180_, 0);
                    crate::leanh::lean_inc(v_head_1181_);
                    v_tail_1182_ = crate::leanh::lean_ctor_get(v_p_1180_, 1);
                    crate::leanh::lean_inc(v_tail_1182_);
                    crate::leanh::lean_dec_ref_known(v_p_1180_, 2);
                    v_fst_1183_ = crate::leanh::lean_ctor_get(v_head_1181_, 0);
                    v_snd_1184_ = crate::leanh::lean_ctor_get(v_head_1181_, 1);
                    v_isSharedCheck_1193_ = (!crate::leanh::lean_is_exclusive(v_head_1181_)) as u8;
                    if v_isSharedCheck_1193_ == 0 {
                        v___x_1186_ = v_head_1181_;
                        v_isShared_1187_ = v_isSharedCheck_1193_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1184_);
                        crate::leanh::lean_inc(v_fst_1183_);
                        crate::leanh::lean_dec(v_head_1181_);
                        v___x_1186_ = crate::leanh::lean_box(0);
                        v_isShared_1187_ = v_isSharedCheck_1193_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1188_ = l_Nat_Linear_monomialToExpr(v_fst_1183_, v_snd_1184_);
                if v_isShared_1187_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1186_, 2);
                    crate::leanh::lean_ctor_set(v___x_1186_, 1, v___x_1188_);
                    crate::leanh::lean_ctor_set(v___x_1186_, 0, v_e_1179_);
                    v___x_1190_ = v___x_1186_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1192_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 0, v_e_1179_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1192_, 1, v___x_1188_);
                    v___x_1190_ = v_reuseFailAlloc_1192_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_e_1179_ = v___x_1190_;
                v_p_1180_ = v_tail_1182_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Nat_Linear_Poly_toExpr(
    mut v_p_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1194_) == 0 {
        let mut v___x_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1195_ = l_Nat_Linear_instInhabitedExpr_default___closed__0;
        return v___x_1195_;
    } else {
        let mut v_head_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1196_ = crate::leanh::lean_ctor_get(v_p_1194_, 0);
        crate::leanh::lean_inc(v_head_1196_);
        v_tail_1197_ = crate::leanh::lean_ctor_get(v_p_1194_, 1);
        crate::leanh::lean_inc(v_tail_1197_);
        crate::leanh::lean_dec_ref_known(v_p_1194_, 2);
        v_fst_1198_ = crate::leanh::lean_ctor_get(v_head_1196_, 0);
        crate::leanh::lean_inc(v_fst_1198_);
        v_snd_1199_ = crate::leanh::lean_ctor_get(v_head_1196_, 1);
        crate::leanh::lean_inc(v_snd_1199_);
        crate::leanh::lean_dec(v_head_1196_);
        v___x_1200_ = l_Nat_Linear_monomialToExpr(v_fst_1198_, v_snd_1199_);
        v___x_1201_ = l_Nat_Linear_Poly_toExpr_go(v___x_1200_, v_tail_1197_);
        return v___x_1201_;
    }
}
pub unsafe fn l_Nat_Linear_PolyCnstr_toExpr(
    mut v_c_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_eq_1203_: u8 = 0;
    let mut v_lhs_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rhs_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1208_: u8 = 0;
    let mut v___x_1209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_eq_1203_ = crate::leanh::lean_ctor_get_uint8(
                    v_c_1202_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                );
                v_lhs_1204_ = crate::leanh::lean_ctor_get(v_c_1202_, 0);
                v_rhs_1205_ = crate::leanh::lean_ctor_get(v_c_1202_, 1);
                v_isSharedCheck_1214_ = (!crate::leanh::lean_is_exclusive(v_c_1202_)) as u8;
                if v_isSharedCheck_1214_ == 0 {
                    v___x_1207_ = v_c_1202_;
                    v_isShared_1208_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_rhs_1205_);
                    crate::leanh::lean_inc(v_lhs_1204_);
                    crate::leanh::lean_dec(v_c_1202_);
                    v___x_1207_ = crate::leanh::lean_box(0);
                    v_isShared_1208_ = v_isSharedCheck_1214_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1209_ = l_Nat_Linear_Poly_toExpr(v_lhs_1204_);
                v___x_1210_ = l_Nat_Linear_Poly_toExpr(v_rhs_1205_);
                if v_isShared_1208_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1207_, 1, v___x_1210_);
                    crate::leanh::lean_ctor_set(v___x_1207_, 0, v___x_1209_);
                    v___x_1212_ = v___x_1207_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1213_ = crate::leanh::lean_alloc_ctor(0, 2, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 0, v___x_1209_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1213_, 1, v___x_1210_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1213_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        v_eq_1203_,
                    );
                    v___x_1212_ = v_reuseFailAlloc_1213_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter___redArg(
    mut v_p_1215_: *mut crate::leanh::LeanObject,
    mut v_h__1_1216_: *mut crate::leanh::LeanObject,
    mut v_h__2_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1215_) == 0 {
        let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1217_);
        v___x_1218_ = crate::leanh::lean_box(0);
        v___x_1219_ = crate::leanh::lean_apply_1(v_h__1_1216_, v___x_1218_);
        return v___x_1219_;
    } else {
        let mut v_head_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1216_);
        v_head_1220_ = crate::leanh::lean_ctor_get(v_p_1215_, 0);
        crate::leanh::lean_inc(v_head_1220_);
        v_tail_1221_ = crate::leanh::lean_ctor_get(v_p_1215_, 1);
        crate::leanh::lean_inc(v_tail_1221_);
        crate::leanh::lean_dec_ref_known(v_p_1215_, 2);
        v_fst_1222_ = crate::leanh::lean_ctor_get(v_head_1220_, 0);
        crate::leanh::lean_inc(v_fst_1222_);
        v_snd_1223_ = crate::leanh::lean_ctor_get(v_head_1220_, 1);
        crate::leanh::lean_inc(v_snd_1223_);
        crate::leanh::lean_dec(v_head_1220_);
        v___x_1224_ =
            crate::leanh::lean_apply_3(v_h__2_1217_, v_fst_1222_, v_snd_1223_, v_tail_1221_);
        return v___x_1224_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_denote_match__1_splitter(
    mut v_motive_1225_: *mut crate::leanh::LeanObject,
    mut v_p_1226_: *mut crate::leanh::LeanObject,
    mut v_h__1_1227_: *mut crate::leanh::LeanObject,
    mut v_h__2_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1226_) == 0 {
        let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1228_);
        v___x_1229_ = crate::leanh::lean_box(0);
        v___x_1230_ = crate::leanh::lean_apply_1(v_h__1_1227_, v___x_1229_);
        return v___x_1230_;
    } else {
        let mut v_head_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fst_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_snd_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1227_);
        v_head_1231_ = crate::leanh::lean_ctor_get(v_p_1226_, 0);
        crate::leanh::lean_inc(v_head_1231_);
        v_tail_1232_ = crate::leanh::lean_ctor_get(v_p_1226_, 1);
        crate::leanh::lean_inc(v_tail_1232_);
        crate::leanh::lean_dec_ref_known(v_p_1226_, 2);
        v_fst_1233_ = crate::leanh::lean_ctor_get(v_head_1231_, 0);
        crate::leanh::lean_inc(v_fst_1233_);
        v_snd_1234_ = crate::leanh::lean_ctor_get(v_head_1231_, 1);
        crate::leanh::lean_inc(v_snd_1234_);
        crate::leanh::lean_dec(v_head_1231_);
        v___x_1235_ =
            crate::leanh::lean_apply_3(v_h__2_1228_, v_fst_1233_, v_snd_1234_, v_tail_1232_);
        return v___x_1235_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(
    mut v_fuel_1236_: *mut crate::leanh::LeanObject,
    mut v_h__1_1237_: *mut crate::leanh::LeanObject,
    mut v_h__2_1238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1240_: u8 = 0;
    v_zero_1239_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1240_ = lean_nat_dec_eq(v_fuel_1236_, v_zero_1239_);
    if v_isZero_1240_ == 1 {
        let mut v___x_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1238_);
        v___x_1241_ = crate::leanh::lean_box(0);
        v___x_1242_ = crate::leanh::lean_apply_1(v_h__1_1237_, v___x_1241_);
        return v___x_1242_;
    } else {
        let mut v_one_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1237_);
        v_one_1243_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1244_ = lean_nat_sub(v_fuel_1236_, v_one_1243_);
        v___x_1245_ = crate::leanh::lean_apply_1(v_h__2_1238_, v_n_1244_);
        return v___x_1245_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg___boxed(
    mut v_fuel_1246_: *mut crate::leanh::LeanObject,
    mut v_h__1_1247_: *mut crate::leanh::LeanObject,
    mut v_h__2_1248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1249_ =
        l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___redArg(
            v_fuel_1246_,
            v_h__1_1247_,
            v_h__2_1248_,
        );
    crate::leanh::lean_dec(v_fuel_1246_);
    return v_res_1249_;
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(
    mut v_motive_1250_: *mut crate::leanh::LeanObject,
    mut v_fuel_1251_: *mut crate::leanh::LeanObject,
    mut v_h__1_1252_: *mut crate::leanh::LeanObject,
    mut v_h__2_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_1254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1255_: u8 = 0;
    v_zero_1254_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_1255_ = lean_nat_dec_eq(v_fuel_1251_, v_zero_1254_);
    if v_isZero_1255_ == 1 {
        let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1253_);
        v___x_1256_ = crate::leanh::lean_box(0);
        v___x_1257_ = crate::leanh::lean_apply_1(v_h__1_1252_, v___x_1256_);
        return v___x_1257_;
    } else {
        let mut v_one_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1252_);
        v_one_1258_ = crate::leanh::lean_unsigned_to_nat(1);
        v_n_1259_ = lean_nat_sub(v_fuel_1251_, v_one_1258_);
        v___x_1260_ = crate::leanh::lean_apply_1(v_h__2_1253_, v_n_1259_);
        return v___x_1260_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter___boxed(
    mut v_motive_1261_: *mut crate::leanh::LeanObject,
    mut v_fuel_1262_: *mut crate::leanh::LeanObject,
    mut v_h__1_1263_: *mut crate::leanh::LeanObject,
    mut v_h__2_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__3_splitter(
        v_motive_1261_,
        v_fuel_1262_,
        v_h__1_1263_,
        v_h__2_1264_,
    );
    crate::leanh::lean_dec(v_fuel_1262_);
    return v_res_1265_;
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter___redArg(
    mut v_m_u2081_1266_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1267_: *mut crate::leanh::LeanObject,
    mut v_h__1_1268_: *mut crate::leanh::LeanObject,
    mut v_h__2_1269_: *mut crate::leanh::LeanObject,
    mut v_h__3_1270_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2082_1267_) == 0 {
        let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1270_);
        crate::leanh::lean_dec(v_h__2_1269_);
        v___x_1271_ = crate::leanh::lean_apply_1(v_h__1_1268_, v_m_u2081_1266_);
        return v___x_1271_;
    } else {
        crate::leanh::lean_dec(v_h__1_1268_);
        if crate::leanh::lean_obj_tag(v_m_u2081_1266_) == 0 {
            let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1270_);
            v___x_1272_ = crate::leanh::lean_apply_2(
                v_h__2_1269_,
                v_m_u2082_1267_,
                crate::leanh::lean_box(0),
            );
            return v___x_1272_;
        } else {
            let mut v_head_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1269_);
            v_head_1273_ = crate::leanh::lean_ctor_get(v_m_u2081_1266_, 0);
            crate::leanh::lean_inc(v_head_1273_);
            v_head_1274_ = crate::leanh::lean_ctor_get(v_m_u2082_1267_, 0);
            crate::leanh::lean_inc(v_head_1274_);
            v_tail_1275_ = crate::leanh::lean_ctor_get(v_m_u2082_1267_, 1);
            crate::leanh::lean_inc(v_tail_1275_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_1267_, 2);
            v_tail_1276_ = crate::leanh::lean_ctor_get(v_m_u2081_1266_, 1);
            crate::leanh::lean_inc(v_tail_1276_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_1266_, 2);
            v_fst_1277_ = crate::leanh::lean_ctor_get(v_head_1273_, 0);
            crate::leanh::lean_inc(v_fst_1277_);
            v_snd_1278_ = crate::leanh::lean_ctor_get(v_head_1273_, 1);
            crate::leanh::lean_inc(v_snd_1278_);
            crate::leanh::lean_dec(v_head_1273_);
            v_fst_1279_ = crate::leanh::lean_ctor_get(v_head_1274_, 0);
            crate::leanh::lean_inc(v_fst_1279_);
            v_snd_1280_ = crate::leanh::lean_ctor_get(v_head_1274_, 1);
            crate::leanh::lean_inc(v_snd_1280_);
            crate::leanh::lean_dec(v_head_1274_);
            v___x_1281_ = crate::leanh::lean_apply_6(
                v_h__3_1270_,
                v_fst_1277_,
                v_snd_1278_,
                v_tail_1276_,
                v_fst_1279_,
                v_snd_1280_,
                v_tail_1275_,
            );
            return v___x_1281_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_cancelAux_match__1_splitter(
    mut v_motive_1282_: *mut crate::leanh::LeanObject,
    mut v_m_u2081_1283_: *mut crate::leanh::LeanObject,
    mut v_m_u2082_1284_: *mut crate::leanh::LeanObject,
    mut v_h__1_1285_: *mut crate::leanh::LeanObject,
    mut v_h__2_1286_: *mut crate::leanh::LeanObject,
    mut v_h__3_1287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_m_u2082_1284_) == 0 {
        let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1287_);
        crate::leanh::lean_dec(v_h__2_1286_);
        v___x_1288_ = crate::leanh::lean_apply_1(v_h__1_1285_, v_m_u2081_1283_);
        return v___x_1288_;
    } else {
        crate::leanh::lean_dec(v_h__1_1285_);
        if crate::leanh::lean_obj_tag(v_m_u2081_1283_) == 0 {
            let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1287_);
            v___x_1289_ = crate::leanh::lean_apply_2(
                v_h__2_1286_,
                v_m_u2082_1284_,
                crate::leanh::lean_box(0),
            );
            return v___x_1289_;
        } else {
            let mut v_head_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_head_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_tail_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_fst_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_snd_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1286_);
            v_head_1290_ = crate::leanh::lean_ctor_get(v_m_u2081_1283_, 0);
            crate::leanh::lean_inc(v_head_1290_);
            v_head_1291_ = crate::leanh::lean_ctor_get(v_m_u2082_1284_, 0);
            crate::leanh::lean_inc(v_head_1291_);
            v_tail_1292_ = crate::leanh::lean_ctor_get(v_m_u2082_1284_, 1);
            crate::leanh::lean_inc(v_tail_1292_);
            crate::leanh::lean_dec_ref_known(v_m_u2082_1284_, 2);
            v_tail_1293_ = crate::leanh::lean_ctor_get(v_m_u2081_1283_, 1);
            crate::leanh::lean_inc(v_tail_1293_);
            crate::leanh::lean_dec_ref_known(v_m_u2081_1283_, 2);
            v_fst_1294_ = crate::leanh::lean_ctor_get(v_head_1290_, 0);
            crate::leanh::lean_inc(v_fst_1294_);
            v_snd_1295_ = crate::leanh::lean_ctor_get(v_head_1290_, 1);
            crate::leanh::lean_inc(v_snd_1295_);
            crate::leanh::lean_dec(v_head_1290_);
            v_fst_1296_ = crate::leanh::lean_ctor_get(v_head_1291_, 0);
            crate::leanh::lean_inc(v_fst_1296_);
            v_snd_1297_ = crate::leanh::lean_ctor_get(v_head_1291_, 1);
            crate::leanh::lean_inc(v_snd_1297_);
            crate::leanh::lean_dec(v_head_1291_);
            v___x_1298_ = crate::leanh::lean_apply_6(
                v_h__3_1287_,
                v_fst_1294_,
                v_snd_1295_,
                v_tail_1293_,
                v_fst_1296_,
                v_snd_1297_,
                v_tail_1292_,
            );
            return v___x_1298_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter___redArg(
    mut v_x_1299_: *mut crate::leanh::LeanObject,
    mut v_h__1_1300_: *mut crate::leanh::LeanObject,
    mut v_h__2_1301_: *mut crate::leanh::LeanObject,
    mut v_h__3_1302_: *mut crate::leanh::LeanObject,
    mut v_h__4_1303_: *mut crate::leanh::LeanObject,
    mut v_h__5_1304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1299_) {
        0 => {
            let mut v_v_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1304_);
            crate::leanh::lean_dec(v_h__4_1303_);
            crate::leanh::lean_dec(v_h__3_1302_);
            crate::leanh::lean_dec(v_h__2_1301_);
            v_v_1305_ = crate::leanh::lean_ctor_get(v_x_1299_, 0);
            crate::leanh::lean_inc(v_v_1305_);
            crate::leanh::lean_dec_ref_known(v_x_1299_, 1);
            v___x_1306_ = crate::leanh::lean_apply_1(v_h__1_1300_, v_v_1305_);
            return v___x_1306_;
        }
        1 => {
            let mut v_i_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1304_);
            crate::leanh::lean_dec(v_h__4_1303_);
            crate::leanh::lean_dec(v_h__3_1302_);
            crate::leanh::lean_dec(v_h__1_1300_);
            v_i_1307_ = crate::leanh::lean_ctor_get(v_x_1299_, 0);
            crate::leanh::lean_inc(v_i_1307_);
            crate::leanh::lean_dec_ref_known(v_x_1299_, 1);
            v___x_1308_ = crate::leanh::lean_apply_1(v_h__2_1301_, v_i_1307_);
            return v___x_1308_;
        }
        2 => {
            let mut v_a_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1304_);
            crate::leanh::lean_dec(v_h__4_1303_);
            crate::leanh::lean_dec(v_h__2_1301_);
            crate::leanh::lean_dec(v_h__1_1300_);
            v_a_1309_ = crate::leanh::lean_ctor_get(v_x_1299_, 0);
            crate::leanh::lean_inc_ref(v_a_1309_);
            v_b_1310_ = crate::leanh::lean_ctor_get(v_x_1299_, 1);
            crate::leanh::lean_inc_ref(v_b_1310_);
            crate::leanh::lean_dec_ref_known(v_x_1299_, 2);
            v___x_1311_ = crate::leanh::lean_apply_2(v_h__3_1302_, v_a_1309_, v_b_1310_);
            return v___x_1311_;
        }
        3 => {
            let mut v_k_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1304_);
            crate::leanh::lean_dec(v_h__3_1302_);
            crate::leanh::lean_dec(v_h__2_1301_);
            crate::leanh::lean_dec(v_h__1_1300_);
            v_k_1312_ = crate::leanh::lean_ctor_get(v_x_1299_, 0);
            crate::leanh::lean_inc(v_k_1312_);
            v_a_1313_ = crate::leanh::lean_ctor_get(v_x_1299_, 1);
            crate::leanh::lean_inc_ref(v_a_1313_);
            crate::leanh::lean_dec_ref_known(v_x_1299_, 2);
            v___x_1314_ = crate::leanh::lean_apply_2(v_h__4_1303_, v_k_1312_, v_a_1313_);
            return v___x_1314_;
        }
        _ => {
            let mut v_a_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1303_);
            crate::leanh::lean_dec(v_h__3_1302_);
            crate::leanh::lean_dec(v_h__2_1301_);
            crate::leanh::lean_dec(v_h__1_1300_);
            v_a_1315_ = crate::leanh::lean_ctor_get(v_x_1299_, 0);
            crate::leanh::lean_inc_ref(v_a_1315_);
            v_k_1316_ = crate::leanh::lean_ctor_get(v_x_1299_, 1);
            crate::leanh::lean_inc(v_k_1316_);
            crate::leanh::lean_dec_ref_known(v_x_1299_, 2);
            v___x_1317_ = crate::leanh::lean_apply_2(v_h__5_1304_, v_a_1315_, v_k_1316_);
            return v___x_1317_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Expr_toPoly_go_match__1_splitter(
    mut v_motive_1318_: *mut crate::leanh::LeanObject,
    mut v_x_1319_: *mut crate::leanh::LeanObject,
    mut v_h__1_1320_: *mut crate::leanh::LeanObject,
    mut v_h__2_1321_: *mut crate::leanh::LeanObject,
    mut v_h__3_1322_: *mut crate::leanh::LeanObject,
    mut v_h__4_1323_: *mut crate::leanh::LeanObject,
    mut v_h__5_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1319_) {
        0 => {
            let mut v_v_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1324_);
            crate::leanh::lean_dec(v_h__4_1323_);
            crate::leanh::lean_dec(v_h__3_1322_);
            crate::leanh::lean_dec(v_h__2_1321_);
            v_v_1325_ = crate::leanh::lean_ctor_get(v_x_1319_, 0);
            crate::leanh::lean_inc(v_v_1325_);
            crate::leanh::lean_dec_ref_known(v_x_1319_, 1);
            v___x_1326_ = crate::leanh::lean_apply_1(v_h__1_1320_, v_v_1325_);
            return v___x_1326_;
        }
        1 => {
            let mut v_i_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1324_);
            crate::leanh::lean_dec(v_h__4_1323_);
            crate::leanh::lean_dec(v_h__3_1322_);
            crate::leanh::lean_dec(v_h__1_1320_);
            v_i_1327_ = crate::leanh::lean_ctor_get(v_x_1319_, 0);
            crate::leanh::lean_inc(v_i_1327_);
            crate::leanh::lean_dec_ref_known(v_x_1319_, 1);
            v___x_1328_ = crate::leanh::lean_apply_1(v_h__2_1321_, v_i_1327_);
            return v___x_1328_;
        }
        2 => {
            let mut v_a_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_b_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1324_);
            crate::leanh::lean_dec(v_h__4_1323_);
            crate::leanh::lean_dec(v_h__2_1321_);
            crate::leanh::lean_dec(v_h__1_1320_);
            v_a_1329_ = crate::leanh::lean_ctor_get(v_x_1319_, 0);
            crate::leanh::lean_inc_ref(v_a_1329_);
            v_b_1330_ = crate::leanh::lean_ctor_get(v_x_1319_, 1);
            crate::leanh::lean_inc_ref(v_b_1330_);
            crate::leanh::lean_dec_ref_known(v_x_1319_, 2);
            v___x_1331_ = crate::leanh::lean_apply_2(v_h__3_1322_, v_a_1329_, v_b_1330_);
            return v___x_1331_;
        }
        3 => {
            let mut v_k_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__5_1324_);
            crate::leanh::lean_dec(v_h__3_1322_);
            crate::leanh::lean_dec(v_h__2_1321_);
            crate::leanh::lean_dec(v_h__1_1320_);
            v_k_1332_ = crate::leanh::lean_ctor_get(v_x_1319_, 0);
            crate::leanh::lean_inc(v_k_1332_);
            v_a_1333_ = crate::leanh::lean_ctor_get(v_x_1319_, 1);
            crate::leanh::lean_inc_ref(v_a_1333_);
            crate::leanh::lean_dec_ref_known(v_x_1319_, 2);
            v___x_1334_ = crate::leanh::lean_apply_2(v_h__4_1323_, v_k_1332_, v_a_1333_);
            return v___x_1334_;
        }
        _ => {
            let mut v_a_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1323_);
            crate::leanh::lean_dec(v_h__3_1322_);
            crate::leanh::lean_dec(v_h__2_1321_);
            crate::leanh::lean_dec(v_h__1_1320_);
            v_a_1335_ = crate::leanh::lean_ctor_get(v_x_1319_, 0);
            crate::leanh::lean_inc_ref(v_a_1335_);
            v_k_1336_ = crate::leanh::lean_ctor_get(v_x_1319_, 1);
            crate::leanh::lean_inc(v_k_1336_);
            crate::leanh::lean_dec_ref_known(v_x_1319_, 2);
            v___x_1337_ = crate::leanh::lean_apply_2(v_h__5_1324_, v_a_1335_, v_k_1336_);
            return v___x_1337_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter___redArg(
    mut v_p_1338_: *mut crate::leanh::LeanObject,
    mut v_h__1_1339_: *mut crate::leanh::LeanObject,
    mut v_h__2_1340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1338_) == 0 {
        let mut v___x_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1340_);
        v___x_1341_ = crate::leanh::lean_box(0);
        v___x_1342_ = crate::leanh::lean_apply_1(v_h__1_1339_, v___x_1341_);
        return v___x_1342_;
    } else {
        let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1339_);
        v___x_1343_ =
            crate::leanh::lean_apply_2(v_h__2_1340_, v_p_1338_, crate::leanh::lean_box(0));
        return v___x_1343_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_Linear_0__Nat_Linear_Poly_isZero_match__1_splitter(
    mut v_motive_1344_: *mut crate::leanh::LeanObject,
    mut v_p_1345_: *mut crate::leanh::LeanObject,
    mut v_h__1_1346_: *mut crate::leanh::LeanObject,
    mut v_h__2_1347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_1345_) == 0 {
        let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1347_);
        v___x_1348_ = crate::leanh::lean_box(0);
        v___x_1349_ = crate::leanh::lean_apply_1(v_h__1_1346_, v___x_1348_);
        return v___x_1349_;
    } else {
        let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1346_);
        v___x_1350_ =
            crate::leanh::lean_apply_2(v_h__2_1347_, v_p_1345_, crate::leanh::lean_box(0));
        return v___x_1350_;
    }
}
pub unsafe fn l_Nat_elimOffset___redArg(
    mut v_h_u2082_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1352_ = crate::leanh::lean_apply_1(v_h_u2082_1351_, crate::leanh::lean_box(0));
    return v___x_1352_;
}
pub unsafe fn l_Nat_elimOffset(
    mut v_00_u03b1_1353_: *mut crate::leanh::LeanObject,
    mut v_a_1354_: *mut crate::leanh::LeanObject,
    mut v_b_1355_: *mut crate::leanh::LeanObject,
    mut v_k_1356_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_1357_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_1358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1359_ = crate::leanh::lean_apply_1(v_h_u2082_1358_, crate::leanh::lean_box(0));
    return v___x_1359_;
}
pub unsafe fn l_Nat_elimOffset___boxed(
    mut v_00_u03b1_1360_: *mut crate::leanh::LeanObject,
    mut v_a_1361_: *mut crate::leanh::LeanObject,
    mut v_b_1362_: *mut crate::leanh::LeanObject,
    mut v_k_1363_: *mut crate::leanh::LeanObject,
    mut v_h_u2081_1364_: *mut crate::leanh::LeanObject,
    mut v_h_u2082_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1366_ = l_Nat_elimOffset(
        v_00_u03b1_1360_,
        v_a_1361_,
        v_b_1362_,
        v_k_1363_,
        v_h_u2081_1364_,
        v_h_u2082_1365_,
    );
    crate::leanh::lean_dec(v_k_1363_);
    crate::leanh::lean_dec(v_b_1362_);
    crate::leanh::lean_dec(v_a_1361_);
    return v_res_1366_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_Linear(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Nat_Linear_fixedVar = _init_l_Nat_Linear_fixedVar();
    crate::leanh::lean_mark_persistent(l_Nat_Linear_fixedVar);
    l_Nat_Linear_hugeFuel = _init_l_Nat_Linear_hugeFuel();
    crate::leanh::lean_mark_persistent(l_Nat_Linear_hugeFuel);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_Linear(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_Linear(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_LawfulBEqTactics(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Prod(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Nat_Linear(builtin);
}

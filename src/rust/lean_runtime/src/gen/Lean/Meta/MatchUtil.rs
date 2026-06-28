// Lean compiler output
// Module: Lean.Meta.MatchUtil
// Imports: Lean.Util.Recognizers Lean.Meta.CtorRecognizer
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isAppOfArity, l_Lean_Expr_isFalse,
};
use crate::r#gen::Lean::Meta::Basic::l_Lean_Meta_isExprDefEq;
use crate::r#gen::Lean::Meta::CtorRecognizer::{
    initialize_Lean_Meta_CtorRecognizer, l_Lean_Meta_isConstructorApp_x3f,
    runtime_initialize_Lean_Meta_CtorRecognizer,
};
use crate::r#gen::Lean::Util::Recognizers::{
    initialize_Lean_Util_Recognizers, runtime_initialize_Lean_Util_Recognizers,
};
use crate::lean_imports_rs::Lean::Meta::Basic::lean_whnf;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_6, lean_box, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [69, 113, 0],
    };
static mut l_Lean_Meta_matchEq_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_matchEq_x3f___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_matchEq_x3f___lam__0___closed__0_value) as *mut LeanObject,
        16122875713692181903 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_matchEq_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchEq_x3f___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [72, 69, 113, 0],
    };
static mut l_Lean_Meta_matchHEq_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_matchHEq_x3f___lam__0___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_matchHEq_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            13589827700912665667 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_matchHEq_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchHEq_x3f___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 4,
        m_capacity: 4,
        m_length: 3,
        m_data: [78, 111, 116, 0],
    };
static mut l_Lean_Meta_matchNot_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_matchNot_x3f___lam__0___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_matchNot_x3f___lam__0___closed__0_value)
                as *mut LeanObject,
            16612019923665488825 as *mut LeanObject,
        ],
    };
static mut l_Lean_Meta_matchNot_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchNot_x3f___lam__0___closed__1_value) as *mut LeanObject;
pub static l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 3,
        m_capacity: 3,
        m_length: 2,
        m_data: [78, 101, 0],
    };
static mut l_Lean_Meta_matchNe_x3f___lam__0___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_matchNe_x3f___lam__0___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_matchNe_x3f___lam__0___closed__0_value) as *mut LeanObject,
        6695605208187598753 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_matchNe_x3f___lam__0___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_matchNe_x3f___lam__0___closed__1_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_testHelper(
    mut v_e_596_: *mut LeanObject,
    mut v_p_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
    mut v_a_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_605_: u8 = 0;
    let mut v___x_606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_612_: u8 = 0;
    let mut v___x_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_616_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_597_);
                lean_inc(v_a_601_);
                lean_inc_ref(v_a_600_);
                lean_inc(v_a_599_);
                lean_inc_ref(v_a_598_);
                lean_inc_ref(v_e_596_);
                v___x_603_ = lean_apply_6(
                    v_p_597_,
                    v_e_596_,
                    v_a_598_,
                    v_a_599_,
                    v_a_600_,
                    v_a_601_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_603_) == 0 {
                    v_a_604_ = lean_ctor_get(v___x_603_, 0);
                    lean_inc(v_a_604_);
                    v___x_605_ = (lean_unbox(v_a_604_) as u8);
                    lean_dec(v_a_604_);
                    if v___x_605_ == 0 {
                        lean_dec_ref_known(v___x_603_, 1);
                        lean_inc(v_a_601_);
                        lean_inc_ref(v_a_600_);
                        lean_inc(v_a_599_);
                        lean_inc_ref(v_a_598_);
                        v___x_606_ = lean_whnf(v_e_596_, v_a_598_, v_a_599_, v_a_600_, v_a_601_);
                        if lean_obj_tag(v___x_606_) == 0 {
                            v_a_607_ = lean_ctor_get(v___x_606_, 0);
                            lean_inc(v_a_607_);
                            lean_dec_ref_known(v___x_606_, 1);
                            lean_inc(v_a_601_);
                            lean_inc_ref(v_a_600_);
                            lean_inc(v_a_599_);
                            lean_inc_ref(v_a_598_);
                            v___x_608_ = lean_apply_6(
                                v_p_597_,
                                v_a_607_,
                                v_a_598_,
                                v_a_599_,
                                v_a_600_,
                                v_a_601_,
                                lean_box(0),
                            );
                            return v___x_608_;
                        } else {
                            lean_dec_ref(v_p_597_);
                            v_a_609_ = lean_ctor_get(v___x_606_, 0);
                            v_isSharedCheck_616_ = (!lean_is_exclusive(v___x_606_)) as u8;
                            if v_isSharedCheck_616_ == 0 {
                                v___x_611_ = v___x_606_;
                                v_isShared_612_ = v_isSharedCheck_616_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_609_);
                                lean_dec(v___x_606_);
                                v___x_611_ = lean_box(0);
                                v_isShared_612_ = v_isSharedCheck_616_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_p_597_);
                        lean_dec_ref(v_e_596_);
                        return v___x_603_;
                    }
                } else {
                    lean_dec_ref(v_p_597_);
                    lean_dec_ref(v_e_596_);
                    return v___x_603_;
                }
            }
            1 => {
                if v_isShared_612_ == 0 {
                    v___x_614_ = v___x_611_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_615_, 0, v_a_609_);
                    v___x_614_ = v_reuseFailAlloc_615_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_614_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_testHelper___boxed(
    mut v_e_617_: *mut LeanObject,
    mut v_p_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
    mut v_a_622_: *mut LeanObject,
    mut v_a_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_624_: *mut LeanObject = core::ptr::null_mut();
    v_res_624_ = l_Lean_Meta_testHelper(v_e_617_, v_p_618_, v_a_619_, v_a_620_, v_a_621_, v_a_622_);
    lean_dec(v_a_622_);
    lean_dec_ref(v_a_621_);
    lean_dec(v_a_620_);
    lean_dec_ref(v_a_619_);
    return v_res_624_;
}
pub unsafe fn l_Lean_Meta_matchHelper_x3f___redArg(
    mut v_e_625_: *mut LeanObject,
    mut v_p_x3f_626_: *mut LeanObject,
    mut v_a_627_: *mut LeanObject,
    mut v_a_628_: *mut LeanObject,
    mut v_a_629_: *mut LeanObject,
    mut v_a_630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_640_: u8 = 0;
    let mut v___x_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_x3f_626_);
                lean_inc(v_a_630_);
                lean_inc_ref(v_a_629_);
                lean_inc(v_a_628_);
                lean_inc_ref(v_a_627_);
                lean_inc_ref(v_e_625_);
                v___x_632_ = lean_apply_6(
                    v_p_x3f_626_,
                    v_e_625_,
                    v_a_627_,
                    v_a_628_,
                    v_a_629_,
                    v_a_630_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_632_) == 0 {
                    v_a_633_ = lean_ctor_get(v___x_632_, 0);
                    lean_inc(v_a_633_);
                    if lean_obj_tag(v_a_633_) == 0 {
                        lean_dec_ref_known(v___x_632_, 1);
                        lean_inc(v_a_630_);
                        lean_inc_ref(v_a_629_);
                        lean_inc(v_a_628_);
                        lean_inc_ref(v_a_627_);
                        v___x_634_ = lean_whnf(v_e_625_, v_a_627_, v_a_628_, v_a_629_, v_a_630_);
                        if lean_obj_tag(v___x_634_) == 0 {
                            v_a_635_ = lean_ctor_get(v___x_634_, 0);
                            lean_inc(v_a_635_);
                            lean_dec_ref_known(v___x_634_, 1);
                            lean_inc(v_a_630_);
                            lean_inc_ref(v_a_629_);
                            lean_inc(v_a_628_);
                            lean_inc_ref(v_a_627_);
                            v___x_636_ = lean_apply_6(
                                v_p_x3f_626_,
                                v_a_635_,
                                v_a_627_,
                                v_a_628_,
                                v_a_629_,
                                v_a_630_,
                                lean_box(0),
                            );
                            return v___x_636_;
                        } else {
                            lean_dec_ref(v_p_x3f_626_);
                            v_a_637_ = lean_ctor_get(v___x_634_, 0);
                            v_isSharedCheck_644_ = (!lean_is_exclusive(v___x_634_)) as u8;
                            if v_isSharedCheck_644_ == 0 {
                                v___x_639_ = v___x_634_;
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_637_);
                                lean_dec(v___x_634_);
                                v___x_639_ = lean_box(0);
                                v_isShared_640_ = v_isSharedCheck_644_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_633_);
                        lean_dec_ref(v_p_x3f_626_);
                        lean_dec_ref(v_e_625_);
                        return v___x_632_;
                    }
                } else {
                    lean_dec_ref(v_p_x3f_626_);
                    lean_dec_ref(v_e_625_);
                    return v___x_632_;
                }
            }
            1 => {
                if v_isShared_640_ == 0 {
                    v___x_642_ = v___x_639_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_643_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_643_, 0, v_a_637_);
                    v___x_642_ = v_reuseFailAlloc_643_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchHelper_x3f___redArg___boxed(
    mut v_e_645_: *mut LeanObject,
    mut v_p_x3f_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_652_: *mut LeanObject = core::ptr::null_mut();
    v_res_652_ = l_Lean_Meta_matchHelper_x3f___redArg(
        v_e_645_,
        v_p_x3f_646_,
        v_a_647_,
        v_a_648_,
        v_a_649_,
        v_a_650_,
    );
    lean_dec(v_a_650_);
    lean_dec_ref(v_a_649_);
    lean_dec(v_a_648_);
    lean_dec_ref(v_a_647_);
    return v_res_652_;
}
pub unsafe fn l_Lean_Meta_matchHelper_x3f(
    mut v_00_u03b1_653_: *mut LeanObject,
    mut v_e_654_: *mut LeanObject,
    mut v_p_x3f_655_: *mut LeanObject,
    mut v_a_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_669_: u8 = 0;
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_p_x3f_655_);
                lean_inc(v_a_659_);
                lean_inc_ref(v_a_658_);
                lean_inc(v_a_657_);
                lean_inc_ref(v_a_656_);
                lean_inc_ref(v_e_654_);
                v___x_661_ = lean_apply_6(
                    v_p_x3f_655_,
                    v_e_654_,
                    v_a_656_,
                    v_a_657_,
                    v_a_658_,
                    v_a_659_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_661_) == 0 {
                    v_a_662_ = lean_ctor_get(v___x_661_, 0);
                    lean_inc(v_a_662_);
                    if lean_obj_tag(v_a_662_) == 0 {
                        lean_dec_ref_known(v___x_661_, 1);
                        lean_inc(v_a_659_);
                        lean_inc_ref(v_a_658_);
                        lean_inc(v_a_657_);
                        lean_inc_ref(v_a_656_);
                        v___x_663_ = lean_whnf(v_e_654_, v_a_656_, v_a_657_, v_a_658_, v_a_659_);
                        if lean_obj_tag(v___x_663_) == 0 {
                            v_a_664_ = lean_ctor_get(v___x_663_, 0);
                            lean_inc(v_a_664_);
                            lean_dec_ref_known(v___x_663_, 1);
                            lean_inc(v_a_659_);
                            lean_inc_ref(v_a_658_);
                            lean_inc(v_a_657_);
                            lean_inc_ref(v_a_656_);
                            v___x_665_ = lean_apply_6(
                                v_p_x3f_655_,
                                v_a_664_,
                                v_a_656_,
                                v_a_657_,
                                v_a_658_,
                                v_a_659_,
                                lean_box(0),
                            );
                            return v___x_665_;
                        } else {
                            lean_dec_ref(v_p_x3f_655_);
                            v_a_666_ = lean_ctor_get(v___x_663_, 0);
                            v_isSharedCheck_673_ = (!lean_is_exclusive(v___x_663_)) as u8;
                            if v_isSharedCheck_673_ == 0 {
                                v___x_668_ = v___x_663_;
                                v_isShared_669_ = v_isSharedCheck_673_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_666_);
                                lean_dec(v___x_663_);
                                v___x_668_ = lean_box(0);
                                v_isShared_669_ = v_isSharedCheck_673_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_662_);
                        lean_dec_ref(v_p_x3f_655_);
                        lean_dec_ref(v_e_654_);
                        return v___x_661_;
                    }
                } else {
                    lean_dec_ref(v_p_x3f_655_);
                    lean_dec_ref(v_e_654_);
                    return v___x_661_;
                }
            }
            1 => {
                if v_isShared_669_ == 0 {
                    v___x_671_ = v___x_668_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_672_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_672_, 0, v_a_666_);
                    v___x_671_ = v_reuseFailAlloc_672_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_671_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchHelper_x3f___boxed(
    mut v_00_u03b1_674_: *mut LeanObject,
    mut v_e_675_: *mut LeanObject,
    mut v_p_x3f_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
    mut v_a_680_: *mut LeanObject,
    mut v_a_681_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_682_: *mut LeanObject = core::ptr::null_mut();
    v_res_682_ = l_Lean_Meta_matchHelper_x3f(
        v_00_u03b1_674_,
        v_e_675_,
        v_p_x3f_676_,
        v_a_677_,
        v_a_678_,
        v_a_679_,
        v_a_680_,
    );
    lean_dec(v_a_680_);
    lean_dec_ref(v_a_679_);
    lean_dec(v_a_678_);
    lean_dec_ref(v_a_677_);
    return v_res_682_;
}
pub unsafe fn l_Lean_Meta_matchEq_x3f___lam__0(
    mut v_e_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
    mut v___y_690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_694_: u8 = 0;
    v___x_692_ = l_Lean_Meta_matchEq_x3f___lam__0___closed__1;
    v___x_693_ = lean_unsigned_to_nat(3);
    v___x_694_ = l_Lean_Expr_isAppOfArity(v_e_686_, v___x_692_, v___x_693_);
    if v___x_694_ == 0 {
        let mut v___x_695_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
        v___x_695_ = lean_box(0);
        v___x_696_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_696_, 0, v___x_695_);
        return v___x_696_;
    } else {
        let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
        v___x_697_ = l_Lean_Expr_appFn_x21(v_e_686_);
        v___x_698_ = l_Lean_Expr_appFn_x21(v___x_697_);
        v___x_699_ = l_Lean_Expr_appArg_x21(v___x_698_);
        lean_dec_ref(v___x_698_);
        v___x_700_ = l_Lean_Expr_appArg_x21(v___x_697_);
        lean_dec_ref(v___x_697_);
        v___x_701_ = l_Lean_Expr_appArg_x21(v_e_686_);
        v___x_702_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_702_, 0, v___x_700_);
        lean_ctor_set(v___x_702_, 1, v___x_701_);
        v___x_703_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_703_, 0, v___x_699_);
        lean_ctor_set(v___x_703_, 1, v___x_702_);
        v___x_704_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_704_, 0, v___x_703_);
        v___x_705_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_705_, 0, v___x_704_);
        return v___x_705_;
    }
}
pub unsafe fn l_Lean_Meta_matchEq_x3f___lam__0___boxed(
    mut v_e_706_: *mut LeanObject,
    mut v___y_707_: *mut LeanObject,
    mut v___y_708_: *mut LeanObject,
    mut v___y_709_: *mut LeanObject,
    mut v___y_710_: *mut LeanObject,
    mut v___y_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_712_ =
        l_Lean_Meta_matchEq_x3f___lam__0(v_e_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_);
    lean_dec(v___y_710_);
    lean_dec_ref(v___y_709_);
    lean_dec(v___y_708_);
    lean_dec_ref(v___y_707_);
    lean_dec_ref(v_e_706_);
    return v_res_712_;
}
pub unsafe fn l_Lean_Meta_matchEq_x3f(
    mut v_e_713_: *mut LeanObject,
    mut v_a_714_: *mut LeanObject,
    mut v_a_715_: *mut LeanObject,
    mut v_a_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_727_: u8 = 0;
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_731_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_719_ = l_Lean_Meta_matchEq_x3f___lam__0(
                    v_e_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_,
                );
                v_a_720_ = lean_ctor_get(v___x_719_, 0);
                lean_inc(v_a_720_);
                if lean_obj_tag(v_a_720_) == 0 {
                    lean_dec_ref(v___x_719_);
                    lean_inc(v_a_717_);
                    lean_inc_ref(v_a_716_);
                    lean_inc(v_a_715_);
                    lean_inc_ref(v_a_714_);
                    v___x_721_ = lean_whnf(v_e_713_, v_a_714_, v_a_715_, v_a_716_, v_a_717_);
                    if lean_obj_tag(v___x_721_) == 0 {
                        v_a_722_ = lean_ctor_get(v___x_721_, 0);
                        lean_inc(v_a_722_);
                        lean_dec_ref_known(v___x_721_, 1);
                        v___x_723_ = l_Lean_Meta_matchEq_x3f___lam__0(
                            v_a_722_, v_a_714_, v_a_715_, v_a_716_, v_a_717_,
                        );
                        lean_dec(v_a_722_);
                        return v___x_723_;
                    } else {
                        v_a_724_ = lean_ctor_get(v___x_721_, 0);
                        v_isSharedCheck_731_ = (!lean_is_exclusive(v___x_721_)) as u8;
                        if v_isSharedCheck_731_ == 0 {
                            v___x_726_ = v___x_721_;
                            v_isShared_727_ = v_isSharedCheck_731_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_724_);
                            lean_dec(v___x_721_);
                            v___x_726_ = lean_box(0);
                            v_isShared_727_ = v_isSharedCheck_731_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_720_);
                    lean_dec_ref(v_e_713_);
                    return v___x_719_;
                }
            }
            1 => {
                if v_isShared_727_ == 0 {
                    v___x_729_ = v___x_726_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_730_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_730_, 0, v_a_724_);
                    v___x_729_ = v_reuseFailAlloc_730_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_729_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchEq_x3f___boxed(
    mut v_e_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
    mut v_a_734_: *mut LeanObject,
    mut v_a_735_: *mut LeanObject,
    mut v_a_736_: *mut LeanObject,
    mut v_a_737_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_738_: *mut LeanObject = core::ptr::null_mut();
    v_res_738_ = l_Lean_Meta_matchEq_x3f(v_e_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
    lean_dec(v_a_736_);
    lean_dec_ref(v_a_735_);
    lean_dec(v_a_734_);
    lean_dec_ref(v_a_733_);
    return v_res_738_;
}
pub unsafe fn l_Lean_Meta_matchHEq_x3f___lam__0(
    mut v_e_742_: *mut LeanObject,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: u8 = 0;
    v___x_748_ = l_Lean_Meta_matchHEq_x3f___lam__0___closed__1;
    v___x_749_ = lean_unsigned_to_nat(4);
    v___x_750_ = l_Lean_Expr_isAppOfArity(v_e_742_, v___x_748_, v___x_749_);
    if v___x_750_ == 0 {
        let mut v___x_751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
        v___x_751_ = lean_box(0);
        v___x_752_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_752_, 0, v___x_751_);
        return v___x_752_;
    } else {
        let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_760_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
        v___x_753_ = l_Lean_Expr_appFn_x21(v_e_742_);
        v___x_754_ = l_Lean_Expr_appFn_x21(v___x_753_);
        v___x_755_ = l_Lean_Expr_appFn_x21(v___x_754_);
        v___x_756_ = l_Lean_Expr_appArg_x21(v___x_755_);
        lean_dec_ref(v___x_755_);
        v___x_757_ = l_Lean_Expr_appArg_x21(v___x_754_);
        lean_dec_ref(v___x_754_);
        v___x_758_ = l_Lean_Expr_appArg_x21(v___x_753_);
        lean_dec_ref(v___x_753_);
        v___x_759_ = l_Lean_Expr_appArg_x21(v_e_742_);
        v___x_760_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_760_, 0, v___x_758_);
        lean_ctor_set(v___x_760_, 1, v___x_759_);
        v___x_761_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_761_, 0, v___x_757_);
        lean_ctor_set(v___x_761_, 1, v___x_760_);
        v___x_762_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_762_, 0, v___x_756_);
        lean_ctor_set(v___x_762_, 1, v___x_761_);
        v___x_763_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_763_, 0, v___x_762_);
        v___x_764_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_764_, 0, v___x_763_);
        return v___x_764_;
    }
}
pub unsafe fn l_Lean_Meta_matchHEq_x3f___lam__0___boxed(
    mut v_e_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_771_: *mut LeanObject = core::ptr::null_mut();
    v_res_771_ =
        l_Lean_Meta_matchHEq_x3f___lam__0(v_e_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_);
    lean_dec(v___y_769_);
    lean_dec_ref(v___y_768_);
    lean_dec(v___y_767_);
    lean_dec_ref(v___y_766_);
    lean_dec_ref(v_e_765_);
    return v_res_771_;
}
pub unsafe fn l_Lean_Meta_matchHEq_x3f(
    mut v_e_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_786_: u8 = 0;
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_778_ = l_Lean_Meta_matchHEq_x3f___lam__0(
                    v_e_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_,
                );
                v_a_779_ = lean_ctor_get(v___x_778_, 0);
                lean_inc(v_a_779_);
                if lean_obj_tag(v_a_779_) == 0 {
                    lean_dec_ref(v___x_778_);
                    lean_inc(v_a_776_);
                    lean_inc_ref(v_a_775_);
                    lean_inc(v_a_774_);
                    lean_inc_ref(v_a_773_);
                    v___x_780_ = lean_whnf(v_e_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_);
                    if lean_obj_tag(v___x_780_) == 0 {
                        v_a_781_ = lean_ctor_get(v___x_780_, 0);
                        lean_inc(v_a_781_);
                        lean_dec_ref_known(v___x_780_, 1);
                        v___x_782_ = l_Lean_Meta_matchHEq_x3f___lam__0(
                            v_a_781_, v_a_773_, v_a_774_, v_a_775_, v_a_776_,
                        );
                        lean_dec(v_a_781_);
                        return v___x_782_;
                    } else {
                        v_a_783_ = lean_ctor_get(v___x_780_, 0);
                        v_isSharedCheck_790_ = (!lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_790_ == 0 {
                            v___x_785_ = v___x_780_;
                            v_isShared_786_ = v_isSharedCheck_790_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_783_);
                            lean_dec(v___x_780_);
                            v___x_785_ = lean_box(0);
                            v_isShared_786_ = v_isSharedCheck_790_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_779_);
                    lean_dec_ref(v_e_772_);
                    return v___x_778_;
                }
            }
            1 => {
                if v_isShared_786_ == 0 {
                    v___x_788_ = v___x_785_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_789_, 0, v_a_783_);
                    v___x_788_ = v_reuseFailAlloc_789_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_788_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchHEq_x3f___boxed(
    mut v_e_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
    mut v_a_793_: *mut LeanObject,
    mut v_a_794_: *mut LeanObject,
    mut v_a_795_: *mut LeanObject,
    mut v_a_796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_797_: *mut LeanObject = core::ptr::null_mut();
    v_res_797_ = l_Lean_Meta_matchHEq_x3f(v_e_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_);
    lean_dec(v_a_795_);
    lean_dec_ref(v_a_794_);
    lean_dec(v_a_793_);
    lean_dec_ref(v_a_792_);
    return v_res_797_;
}
pub unsafe fn l_Lean_Meta_matchEqHEq_x3f(
    mut v_e_798_: *mut LeanObject,
    mut v_a_799_: *mut LeanObject,
    mut v_a_800_: *mut LeanObject,
    mut v_a_801_: *mut LeanObject,
    mut v_a_802_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v_val_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_814_: u8 = 0;
    let mut v_snd_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v_fst_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_832_: u8 = 0;
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_849_: u8 = 0;
    let mut v_a_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_853_: u8 = 0;
    let mut v___x_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_857_: u8 = 0;
    let mut v_isSharedCheck_858_: u8 = 0;
    let mut v_isSharedCheck_859_: u8 = 0;
    let mut v_unused_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_866_: u8 = 0;
    let mut v_a_867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_870_: u8 = 0;
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_798_);
                v___x_804_ =
                    l_Lean_Meta_matchEq_x3f(v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_);
                if lean_obj_tag(v___x_804_) == 0 {
                    v_a_805_ = lean_ctor_get(v___x_804_, 0);
                    lean_inc(v_a_805_);
                    if lean_obj_tag(v_a_805_) == 1 {
                        lean_dec_ref_known(v_a_805_, 1);
                        lean_dec_ref(v_e_798_);
                        return v___x_804_;
                    } else {
                        lean_dec(v_a_805_);
                        lean_dec_ref_known(v___x_804_, 1);
                        v___x_806_ = l_Lean_Meta_matchHEq_x3f(
                            v_e_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_,
                        );
                        if lean_obj_tag(v___x_806_) == 0 {
                            v_a_807_ = lean_ctor_get(v___x_806_, 0);
                            v_isSharedCheck_866_ = (!lean_is_exclusive(v___x_806_)) as u8;
                            if v_isSharedCheck_866_ == 0 {
                                v___x_809_ = v___x_806_;
                                v_isShared_810_ = v_isSharedCheck_866_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_807_);
                                lean_dec(v___x_806_);
                                v___x_809_ = lean_box(0);
                                v_isShared_810_ = v_isSharedCheck_866_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_867_ = lean_ctor_get(v___x_806_, 0);
                            v_isSharedCheck_874_ = (!lean_is_exclusive(v___x_806_)) as u8;
                            if v_isSharedCheck_874_ == 0 {
                                v___x_869_ = v___x_806_;
                                v_isShared_870_ = v_isSharedCheck_874_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_867_);
                                lean_dec(v___x_806_);
                                v___x_869_ = lean_box(0);
                                v_isShared_870_ = v_isSharedCheck_874_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_798_);
                    return v___x_804_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_807_) == 1 {
                    lean_del_object(v___x_809_);
                    v_val_811_ = lean_ctor_get(v_a_807_, 0);
                    v_isSharedCheck_861_ = (!lean_is_exclusive(v_a_807_)) as u8;
                    if v_isSharedCheck_861_ == 0 {
                        v___x_813_ = v_a_807_;
                        v_isShared_814_ = v_isSharedCheck_861_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_811_);
                        lean_dec(v_a_807_);
                        v___x_813_ = lean_box(0);
                        v_isShared_814_ = v_isSharedCheck_861_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_807_);
                    v___x_862_ = lean_box(0);
                    if v_isShared_810_ == 0 {
                        lean_ctor_set(v___x_809_, 0, v___x_862_);
                        v___x_864_ = v___x_809_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_865_, 0, v___x_862_);
                        v___x_864_ = v_reuseFailAlloc_865_;
                        state = 13;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_815_ = lean_ctor_get(v_val_811_, 1);
                lean_inc(v_snd_815_);
                v_snd_816_ = lean_ctor_get(v_snd_815_, 1);
                lean_inc(v_snd_816_);
                v_fst_817_ = lean_ctor_get(v_val_811_, 0);
                lean_inc(v_fst_817_);
                lean_dec(v_val_811_);
                v_fst_818_ = lean_ctor_get(v_snd_815_, 0);
                v_isSharedCheck_859_ = (!lean_is_exclusive(v_snd_815_)) as u8;
                if v_isSharedCheck_859_ == 0 {
                    v_unused_860_ = lean_ctor_get(v_snd_815_, 1);
                    lean_dec(v_unused_860_);
                    v___x_820_ = v_snd_815_;
                    v_isShared_821_ = v_isSharedCheck_859_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_818_);
                    lean_dec(v_snd_815_);
                    v___x_820_ = lean_box(0);
                    v_isShared_821_ = v_isSharedCheck_859_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_822_ = lean_ctor_get(v_snd_816_, 0);
                v_snd_823_ = lean_ctor_get(v_snd_816_, 1);
                v_isSharedCheck_858_ = (!lean_is_exclusive(v_snd_816_)) as u8;
                if v_isSharedCheck_858_ == 0 {
                    v___x_825_ = v_snd_816_;
                    v_isShared_826_ = v_isSharedCheck_858_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_823_);
                    lean_inc(v_fst_822_);
                    lean_dec(v_snd_816_);
                    v___x_825_ = lean_box(0);
                    v_isShared_826_ = v_isSharedCheck_858_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_fst_817_);
                v___x_827_ = l_Lean_Meta_isExprDefEq(
                    v_fst_817_, v_fst_822_, v_a_799_, v_a_800_, v_a_801_, v_a_802_,
                );
                if lean_obj_tag(v___x_827_) == 0 {
                    v_a_828_ = lean_ctor_get(v___x_827_, 0);
                    v_isSharedCheck_849_ = (!lean_is_exclusive(v___x_827_)) as u8;
                    if v_isSharedCheck_849_ == 0 {
                        v___x_830_ = v___x_827_;
                        v_isShared_831_ = v_isSharedCheck_849_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_828_);
                        lean_dec(v___x_827_);
                        v___x_830_ = lean_box(0);
                        v_isShared_831_ = v_isSharedCheck_849_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_825_);
                    lean_dec(v_snd_823_);
                    lean_del_object(v___x_820_);
                    lean_dec(v_fst_818_);
                    lean_dec(v_fst_817_);
                    lean_del_object(v___x_813_);
                    v_a_850_ = lean_ctor_get(v___x_827_, 0);
                    v_isSharedCheck_857_ = (!lean_is_exclusive(v___x_827_)) as u8;
                    if v_isSharedCheck_857_ == 0 {
                        v___x_852_ = v___x_827_;
                        v_isShared_853_ = v_isSharedCheck_857_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_850_);
                        lean_dec(v___x_827_);
                        v___x_852_ = lean_box(0);
                        v_isShared_853_ = v_isSharedCheck_857_;
                        state = 11;
                        continue;
                    }
                }
            }
            5 => {
                v___x_832_ = (lean_unbox(v_a_828_) as u8);
                lean_dec(v_a_828_);
                if v___x_832_ == 0 {
                    lean_del_object(v___x_825_);
                    lean_dec(v_snd_823_);
                    lean_del_object(v___x_820_);
                    lean_dec(v_fst_818_);
                    lean_dec(v_fst_817_);
                    lean_del_object(v___x_813_);
                    v___x_833_ = lean_box(0);
                    if v_isShared_831_ == 0 {
                        lean_ctor_set(v___x_830_, 0, v___x_833_);
                        v___x_835_ = v___x_830_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_836_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_836_, 0, v___x_833_);
                        v___x_835_ = v_reuseFailAlloc_836_;
                        state = 6;
                        continue;
                    }
                } else {
                    if v_isShared_826_ == 0 {
                        lean_ctor_set(v___x_825_, 0, v_fst_818_);
                        v___x_838_ = v___x_825_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_848_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_848_, 0, v_fst_818_);
                        lean_ctor_set(v_reuseFailAlloc_848_, 1, v_snd_823_);
                        v___x_838_ = v_reuseFailAlloc_848_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_835_;
            }
            7 => {
                if v_isShared_821_ == 0 {
                    lean_ctor_set(v___x_820_, 1, v___x_838_);
                    lean_ctor_set(v___x_820_, 0, v_fst_817_);
                    v___x_840_ = v___x_820_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_847_, 0, v_fst_817_);
                    lean_ctor_set(v_reuseFailAlloc_847_, 1, v___x_838_);
                    v___x_840_ = v_reuseFailAlloc_847_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_814_ == 0 {
                    lean_ctor_set(v___x_813_, 0, v___x_840_);
                    v___x_842_ = v___x_813_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_840_);
                    v___x_842_ = v_reuseFailAlloc_846_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_831_ == 0 {
                    lean_ctor_set(v___x_830_, 0, v___x_842_);
                    v___x_844_ = v___x_830_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
                    v___x_844_ = v_reuseFailAlloc_845_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_844_;
            }
            11 => {
                if v_isShared_853_ == 0 {
                    v___x_855_ = v___x_852_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_856_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_856_, 0, v_a_850_);
                    v___x_855_ = v_reuseFailAlloc_856_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_855_;
            }
            13 => {
                return v___x_864_;
            }
            14 => {
                if v_isShared_870_ == 0 {
                    v___x_872_ = v___x_869_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_867_);
                    v___x_872_ = v_reuseFailAlloc_873_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchEqHEq_x3f___boxed(
    mut v_e_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_881_: *mut LeanObject = core::ptr::null_mut();
    v_res_881_ = l_Lean_Meta_matchEqHEq_x3f(v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_);
    lean_dec(v_a_879_);
    lean_dec_ref(v_a_878_);
    lean_dec(v_a_877_);
    lean_dec_ref(v_a_876_);
    return v_res_881_;
}
pub unsafe fn l_Lean_Meta_matchEqHEqLHS_x3f(
    mut v_e_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
    mut v_a_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_892_: u8 = 0;
    let mut v_val_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v_snd_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_902_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut v_unused_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_919_: u8 = 0;
    let mut v_val_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_923_: u8 = 0;
    let mut v_snd_924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_929_: u8 = 0;
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_939_: u8 = 0;
    let mut v_unused_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_946_: u8 = 0;
    let mut v_a_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_950_: u8 = 0;
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_954_: u8 = 0;
    let mut v_isSharedCheck_955_: u8 = 0;
    let mut v_a_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_959_: u8 = 0;
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_963_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_882_);
                v___x_888_ =
                    l_Lean_Meta_matchEq_x3f(v_e_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
                if lean_obj_tag(v___x_888_) == 0 {
                    v_a_889_ = lean_ctor_get(v___x_888_, 0);
                    v_isSharedCheck_955_ = (!lean_is_exclusive(v___x_888_)) as u8;
                    if v_isSharedCheck_955_ == 0 {
                        v___x_891_ = v___x_888_;
                        v_isShared_892_ = v_isSharedCheck_955_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_889_);
                        lean_dec(v___x_888_);
                        v___x_891_ = lean_box(0);
                        v_isShared_892_ = v_isSharedCheck_955_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_882_);
                    v_a_956_ = lean_ctor_get(v___x_888_, 0);
                    v_isSharedCheck_963_ = (!lean_is_exclusive(v___x_888_)) as u8;
                    if v_isSharedCheck_963_ == 0 {
                        v___x_958_ = v___x_888_;
                        v_isShared_959_ = v_isSharedCheck_963_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_956_);
                        lean_dec(v___x_888_);
                        v___x_958_ = lean_box(0);
                        v_isShared_959_ = v_isSharedCheck_963_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_889_) == 1 {
                    lean_dec_ref(v_e_882_);
                    v_val_893_ = lean_ctor_get(v_a_889_, 0);
                    v_isSharedCheck_914_ = (!lean_is_exclusive(v_a_889_)) as u8;
                    if v_isSharedCheck_914_ == 0 {
                        v___x_895_ = v_a_889_;
                        v_isShared_896_ = v_isSharedCheck_914_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_893_);
                        lean_dec(v_a_889_);
                        v___x_895_ = lean_box(0);
                        v_isShared_896_ = v_isSharedCheck_914_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_891_);
                    lean_dec(v_a_889_);
                    v___x_915_ =
                        l_Lean_Meta_matchHEq_x3f(v_e_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_);
                    if lean_obj_tag(v___x_915_) == 0 {
                        v_a_916_ = lean_ctor_get(v___x_915_, 0);
                        v_isSharedCheck_946_ = (!lean_is_exclusive(v___x_915_)) as u8;
                        if v_isSharedCheck_946_ == 0 {
                            v___x_918_ = v___x_915_;
                            v_isShared_919_ = v_isSharedCheck_946_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_916_);
                            lean_dec(v___x_915_);
                            v___x_918_ = lean_box(0);
                            v_isShared_919_ = v_isSharedCheck_946_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_947_ = lean_ctor_get(v___x_915_, 0);
                        v_isSharedCheck_954_ = (!lean_is_exclusive(v___x_915_)) as u8;
                        if v_isSharedCheck_954_ == 0 {
                            v___x_949_ = v___x_915_;
                            v_isShared_950_ = v_isSharedCheck_954_;
                            state = 14;
                            continue;
                        } else {
                            lean_inc(v_a_947_);
                            lean_dec(v___x_915_);
                            v___x_949_ = lean_box(0);
                            v_isShared_950_ = v_isSharedCheck_954_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v_snd_897_ = lean_ctor_get(v_val_893_, 1);
                lean_inc(v_snd_897_);
                v_fst_898_ = lean_ctor_get(v_val_893_, 0);
                lean_inc(v_fst_898_);
                lean_dec(v_val_893_);
                v_fst_899_ = lean_ctor_get(v_snd_897_, 0);
                v_isSharedCheck_912_ = (!lean_is_exclusive(v_snd_897_)) as u8;
                if v_isSharedCheck_912_ == 0 {
                    v_unused_913_ = lean_ctor_get(v_snd_897_, 1);
                    lean_dec(v_unused_913_);
                    v___x_901_ = v_snd_897_;
                    v_isShared_902_ = v_isSharedCheck_912_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_fst_899_);
                    lean_dec(v_snd_897_);
                    v___x_901_ = lean_box(0);
                    v_isShared_902_ = v_isSharedCheck_912_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_902_ == 0 {
                    lean_ctor_set(v___x_901_, 1, v_fst_899_);
                    lean_ctor_set(v___x_901_, 0, v_fst_898_);
                    v___x_904_ = v___x_901_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_911_, 0, v_fst_898_);
                    lean_ctor_set(v_reuseFailAlloc_911_, 1, v_fst_899_);
                    v___x_904_ = v_reuseFailAlloc_911_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_896_ == 0 {
                    lean_ctor_set(v___x_895_, 0, v___x_904_);
                    v___x_906_ = v___x_895_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_910_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_904_);
                    v___x_906_ = v_reuseFailAlloc_910_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_892_ == 0 {
                    lean_ctor_set(v___x_891_, 0, v___x_906_);
                    v___x_908_ = v___x_891_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_909_, 0, v___x_906_);
                    v___x_908_ = v_reuseFailAlloc_909_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_908_;
            }
            7 => {
                if lean_obj_tag(v_a_916_) == 1 {
                    v_val_920_ = lean_ctor_get(v_a_916_, 0);
                    v_isSharedCheck_941_ = (!lean_is_exclusive(v_a_916_)) as u8;
                    if v_isSharedCheck_941_ == 0 {
                        v___x_922_ = v_a_916_;
                        v_isShared_923_ = v_isSharedCheck_941_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_val_920_);
                        lean_dec(v_a_916_);
                        v___x_922_ = lean_box(0);
                        v_isShared_923_ = v_isSharedCheck_941_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec(v_a_916_);
                    v___x_942_ = lean_box(0);
                    if v_isShared_919_ == 0 {
                        lean_ctor_set(v___x_918_, 0, v___x_942_);
                        v___x_944_ = v___x_918_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
                        v___x_944_ = v_reuseFailAlloc_945_;
                        state = 13;
                        continue;
                    }
                }
            }
            8 => {
                v_snd_924_ = lean_ctor_get(v_val_920_, 1);
                lean_inc(v_snd_924_);
                v_fst_925_ = lean_ctor_get(v_val_920_, 0);
                lean_inc(v_fst_925_);
                lean_dec(v_val_920_);
                v_fst_926_ = lean_ctor_get(v_snd_924_, 0);
                v_isSharedCheck_939_ = (!lean_is_exclusive(v_snd_924_)) as u8;
                if v_isSharedCheck_939_ == 0 {
                    v_unused_940_ = lean_ctor_get(v_snd_924_, 1);
                    lean_dec(v_unused_940_);
                    v___x_928_ = v_snd_924_;
                    v_isShared_929_ = v_isSharedCheck_939_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_fst_926_);
                    lean_dec(v_snd_924_);
                    v___x_928_ = lean_box(0);
                    v_isShared_929_ = v_isSharedCheck_939_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_929_ == 0 {
                    lean_ctor_set(v___x_928_, 1, v_fst_926_);
                    lean_ctor_set(v___x_928_, 0, v_fst_925_);
                    v___x_931_ = v___x_928_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_938_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_938_, 0, v_fst_925_);
                    lean_ctor_set(v_reuseFailAlloc_938_, 1, v_fst_926_);
                    v___x_931_ = v_reuseFailAlloc_938_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_923_ == 0 {
                    lean_ctor_set(v___x_922_, 0, v___x_931_);
                    v___x_933_ = v___x_922_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_937_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_931_);
                    v___x_933_ = v_reuseFailAlloc_937_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_919_ == 0 {
                    lean_ctor_set(v___x_918_, 0, v___x_933_);
                    v___x_935_ = v___x_918_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_936_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_936_, 0, v___x_933_);
                    v___x_935_ = v_reuseFailAlloc_936_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_935_;
            }
            13 => {
                return v___x_944_;
            }
            14 => {
                if v_isShared_950_ == 0 {
                    v___x_952_ = v___x_949_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_953_, 0, v_a_947_);
                    v___x_952_ = v_reuseFailAlloc_953_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_952_;
            }
            16 => {
                if v_isShared_959_ == 0 {
                    v___x_961_ = v___x_958_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_962_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_962_, 0, v_a_956_);
                    v___x_961_ = v_reuseFailAlloc_962_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchEqHEqLHS_x3f___boxed(
    mut v_e_964_: *mut LeanObject,
    mut v_a_965_: *mut LeanObject,
    mut v_a_966_: *mut LeanObject,
    mut v_a_967_: *mut LeanObject,
    mut v_a_968_: *mut LeanObject,
    mut v_a_969_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_970_: *mut LeanObject = core::ptr::null_mut();
    v_res_970_ = l_Lean_Meta_matchEqHEqLHS_x3f(v_e_964_, v_a_965_, v_a_966_, v_a_967_, v_a_968_);
    lean_dec(v_a_968_);
    lean_dec_ref(v_a_967_);
    lean_dec(v_a_966_);
    lean_dec_ref(v_a_965_);
    return v_res_970_;
}
pub unsafe fn l_Lean_Meta_matchFalse___lam__0(
    mut v_e_971_: *mut LeanObject,
    mut v___y_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v___y_974_: *mut LeanObject,
    mut v___y_975_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_977_: u8 = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    v___x_977_ = l_Lean_Expr_isFalse(v_e_971_);
    v___x_978_ = lean_box((v___x_977_) as usize);
    v___x_979_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_979_, 0, v___x_978_);
    return v___x_979_;
}
pub unsafe fn l_Lean_Meta_matchFalse___lam__0___boxed(
    mut v_e_980_: *mut LeanObject,
    mut v___y_981_: *mut LeanObject,
    mut v___y_982_: *mut LeanObject,
    mut v___y_983_: *mut LeanObject,
    mut v___y_984_: *mut LeanObject,
    mut v___y_985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_986_: *mut LeanObject = core::ptr::null_mut();
    v_res_986_ =
        l_Lean_Meta_matchFalse___lam__0(v_e_980_, v___y_981_, v___y_982_, v___y_983_, v___y_984_);
    lean_dec(v___y_984_);
    lean_dec_ref(v___y_983_);
    lean_dec(v___y_982_);
    lean_dec_ref(v___y_981_);
    return v_res_986_;
}
pub unsafe fn l_Lean_Meta_matchFalse(
    mut v_e_987_: *mut LeanObject,
    mut v_a_988_: *mut LeanObject,
    mut v_a_989_: *mut LeanObject,
    mut v_a_990_: *mut LeanObject,
    mut v_a_991_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1006_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_987_);
                v___x_993_ = l_Lean_Meta_matchFalse___lam__0(
                    v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_,
                );
                v_a_994_ = lean_ctor_get(v___x_993_, 0);
                lean_inc(v_a_994_);
                v___x_995_ = (lean_unbox(v_a_994_) as u8);
                lean_dec(v_a_994_);
                if v___x_995_ == 0 {
                    lean_dec_ref(v___x_993_);
                    lean_inc(v_a_991_);
                    lean_inc_ref(v_a_990_);
                    lean_inc(v_a_989_);
                    lean_inc_ref(v_a_988_);
                    v___x_996_ = lean_whnf(v_e_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_);
                    if lean_obj_tag(v___x_996_) == 0 {
                        v_a_997_ = lean_ctor_get(v___x_996_, 0);
                        lean_inc(v_a_997_);
                        lean_dec_ref_known(v___x_996_, 1);
                        v___x_998_ = l_Lean_Meta_matchFalse___lam__0(
                            v_a_997_, v_a_988_, v_a_989_, v_a_990_, v_a_991_,
                        );
                        return v___x_998_;
                    } else {
                        v_a_999_ = lean_ctor_get(v___x_996_, 0);
                        v_isSharedCheck_1006_ = (!lean_is_exclusive(v___x_996_)) as u8;
                        if v_isSharedCheck_1006_ == 0 {
                            v___x_1001_ = v___x_996_;
                            v_isShared_1002_ = v_isSharedCheck_1006_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_999_);
                            lean_dec(v___x_996_);
                            v___x_1001_ = lean_box(0);
                            v_isShared_1002_ = v_isSharedCheck_1006_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_987_);
                    return v___x_993_;
                }
            }
            1 => {
                if v_isShared_1002_ == 0 {
                    v___x_1004_ = v___x_1001_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
                    v___x_1004_ = v_reuseFailAlloc_1005_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1004_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchFalse___boxed(
    mut v_e_1007_: *mut LeanObject,
    mut v_a_1008_: *mut LeanObject,
    mut v_a_1009_: *mut LeanObject,
    mut v_a_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_Lean_Meta_matchFalse(v_e_1007_, v_a_1008_, v_a_1009_, v_a_1010_, v_a_1011_);
    lean_dec(v_a_1011_);
    lean_dec_ref(v_a_1010_);
    lean_dec(v_a_1009_);
    lean_dec_ref(v_a_1008_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_Meta_matchNot_x3f___lam__0(
    mut v_e_1017_: *mut LeanObject,
    mut v___y_1018_: *mut LeanObject,
    mut v___y_1019_: *mut LeanObject,
    mut v___y_1020_: *mut LeanObject,
    mut v___y_1021_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v_binderType_1029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: u8 = 0;
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1046_: u8 = 0;
    let mut v_a_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1050_: u8 = 0;
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1054_: u8 = 0;
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1026_ = l_Lean_Meta_matchNot_x3f___lam__0___closed__1;
                v___x_1027_ = lean_unsigned_to_nat(1);
                v___x_1028_ = l_Lean_Expr_isAppOfArity(v_e_1017_, v___x_1026_, v___x_1027_);
                if v___x_1028_ == 0 {
                    if lean_obj_tag(v_e_1017_) == 7 {
                        v_binderType_1029_ = lean_ctor_get(v_e_1017_, 1);
                        lean_inc_ref(v_binderType_1029_);
                        v_body_1030_ = lean_ctor_get(v_e_1017_, 2);
                        lean_inc_ref(v_body_1030_);
                        lean_dec_ref_known(v_e_1017_, 3);
                        v___x_1031_ = l_Lean_Expr_hasLooseBVars(v_body_1030_);
                        if v___x_1031_ == 0 {
                            v___x_1032_ = l_Lean_Meta_matchFalse(
                                v_body_1030_,
                                v___y_1018_,
                                v___y_1019_,
                                v___y_1020_,
                                v___y_1021_,
                            );
                            if lean_obj_tag(v___x_1032_) == 0 {
                                v_a_1033_ = lean_ctor_get(v___x_1032_, 0);
                                v_isSharedCheck_1046_ = (!lean_is_exclusive(v___x_1032_)) as u8;
                                if v_isSharedCheck_1046_ == 0 {
                                    v___x_1035_ = v___x_1032_;
                                    v_isShared_1036_ = v_isSharedCheck_1046_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_1033_);
                                    lean_dec(v___x_1032_);
                                    v___x_1035_ = lean_box(0);
                                    v_isShared_1036_ = v_isSharedCheck_1046_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_binderType_1029_);
                                v_a_1047_ = lean_ctor_get(v___x_1032_, 0);
                                v_isSharedCheck_1054_ = (!lean_is_exclusive(v___x_1032_)) as u8;
                                if v_isSharedCheck_1054_ == 0 {
                                    v___x_1049_ = v___x_1032_;
                                    v_isShared_1050_ = v_isSharedCheck_1054_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_inc(v_a_1047_);
                                    lean_dec(v___x_1032_);
                                    v___x_1049_ = lean_box(0);
                                    v_isShared_1050_ = v_isSharedCheck_1054_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_body_1030_);
                            lean_dec_ref(v_binderType_1029_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_1017_);
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_1055_ = l_Lean_Expr_appArg_x21(v_e_1017_);
                    lean_dec_ref(v_e_1017_);
                    v___x_1056_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1056_, 0, v___x_1055_);
                    v___x_1057_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1057_, 0, v___x_1056_);
                    return v___x_1057_;
                }
            }
            1 => {
                v___x_1024_ = lean_box(0);
                v___x_1025_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1025_, 0, v___x_1024_);
                return v___x_1025_;
            }
            2 => {
                v___x_1037_ = (lean_unbox(v_a_1033_) as u8);
                lean_dec(v_a_1033_);
                if v___x_1037_ == 0 {
                    lean_dec_ref(v_binderType_1029_);
                    v___x_1038_ = lean_box(0);
                    if v_isShared_1036_ == 0 {
                        lean_ctor_set(v___x_1035_, 0, v___x_1038_);
                        v___x_1040_ = v___x_1035_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1041_, 0, v___x_1038_);
                        v___x_1040_ = v_reuseFailAlloc_1041_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1042_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1042_, 0, v_binderType_1029_);
                    if v_isShared_1036_ == 0 {
                        lean_ctor_set(v___x_1035_, 0, v___x_1042_);
                        v___x_1044_ = v___x_1035_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1045_, 0, v___x_1042_);
                        v___x_1044_ = v_reuseFailAlloc_1045_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1040_;
            }
            4 => {
                return v___x_1044_;
            }
            5 => {
                if v_isShared_1050_ == 0 {
                    v___x_1052_ = v___x_1049_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1053_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1053_, 0, v_a_1047_);
                    v___x_1052_ = v_reuseFailAlloc_1053_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1052_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchNot_x3f___lam__0___boxed(
    mut v_e_1058_: *mut LeanObject,
    mut v___y_1059_: *mut LeanObject,
    mut v___y_1060_: *mut LeanObject,
    mut v___y_1061_: *mut LeanObject,
    mut v___y_1062_: *mut LeanObject,
    mut v___y_1063_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1064_: *mut LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Lean_Meta_matchNot_x3f___lam__0(
        v_e_1058_,
        v___y_1059_,
        v___y_1060_,
        v___y_1061_,
        v___y_1062_,
    );
    lean_dec(v___y_1062_);
    lean_dec_ref(v___y_1061_);
    lean_dec(v___y_1060_);
    lean_dec_ref(v___y_1059_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_Meta_matchNot_x3f(
    mut v_e_1065_: *mut LeanObject,
    mut v_a_1066_: *mut LeanObject,
    mut v_a_1067_: *mut LeanObject,
    mut v_a_1068_: *mut LeanObject,
    mut v_a_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1065_);
                v___x_1071_ = l_Lean_Meta_matchNot_x3f___lam__0(
                    v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_,
                );
                if lean_obj_tag(v___x_1071_) == 0 {
                    v_a_1072_ = lean_ctor_get(v___x_1071_, 0);
                    lean_inc(v_a_1072_);
                    if lean_obj_tag(v_a_1072_) == 0 {
                        lean_dec_ref_known(v___x_1071_, 1);
                        lean_inc(v_a_1069_);
                        lean_inc_ref(v_a_1068_);
                        lean_inc(v_a_1067_);
                        lean_inc_ref(v_a_1066_);
                        v___x_1073_ =
                            lean_whnf(v_e_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
                        if lean_obj_tag(v___x_1073_) == 0 {
                            v_a_1074_ = lean_ctor_get(v___x_1073_, 0);
                            lean_inc(v_a_1074_);
                            lean_dec_ref_known(v___x_1073_, 1);
                            v___x_1075_ = l_Lean_Meta_matchNot_x3f___lam__0(
                                v_a_1074_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_,
                            );
                            return v___x_1075_;
                        } else {
                            v_a_1076_ = lean_ctor_get(v___x_1073_, 0);
                            v_isSharedCheck_1083_ = (!lean_is_exclusive(v___x_1073_)) as u8;
                            if v_isSharedCheck_1083_ == 0 {
                                v___x_1078_ = v___x_1073_;
                                v_isShared_1079_ = v_isSharedCheck_1083_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1076_);
                                lean_dec(v___x_1073_);
                                v___x_1078_ = lean_box(0);
                                v_isShared_1079_ = v_isSharedCheck_1083_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1072_);
                        lean_dec_ref(v_e_1065_);
                        return v___x_1071_;
                    }
                } else {
                    lean_dec_ref(v_e_1065_);
                    return v___x_1071_;
                }
            }
            1 => {
                if v_isShared_1079_ == 0 {
                    v___x_1081_ = v___x_1078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
                    v___x_1081_ = v_reuseFailAlloc_1082_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchNot_x3f___boxed(
    mut v_e_1084_: *mut LeanObject,
    mut v_a_1085_: *mut LeanObject,
    mut v_a_1086_: *mut LeanObject,
    mut v_a_1087_: *mut LeanObject,
    mut v_a_1088_: *mut LeanObject,
    mut v_a_1089_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1090_: *mut LeanObject = core::ptr::null_mut();
    v_res_1090_ = l_Lean_Meta_matchNot_x3f(v_e_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_);
    lean_dec(v_a_1088_);
    lean_dec_ref(v_a_1087_);
    lean_dec(v_a_1086_);
    lean_dec_ref(v_a_1085_);
    return v_res_1090_;
}
pub unsafe fn l_Lean_Meta_matchNe_x3f___lam__0(
    mut v_e_1094_: *mut LeanObject,
    mut v___y_1095_: *mut LeanObject,
    mut v___y_1096_: *mut LeanObject,
    mut v___y_1097_: *mut LeanObject,
    mut v___y_1098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1107_: u8 = 0;
    let mut v_val_1108_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v_a_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1118_: u8 = 0;
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1122_: u8 = 0;
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1100_ = l_Lean_Meta_matchNe_x3f___lam__0___closed__1;
                v___x_1101_ = lean_unsigned_to_nat(3);
                v___x_1102_ = l_Lean_Expr_isAppOfArity(v_e_1094_, v___x_1100_, v___x_1101_);
                if v___x_1102_ == 0 {
                    v___x_1103_ = l_Lean_Meta_matchNot_x3f(
                        v_e_1094_,
                        v___y_1095_,
                        v___y_1096_,
                        v___y_1097_,
                        v___y_1098_,
                    );
                    if lean_obj_tag(v___x_1103_) == 0 {
                        v_a_1104_ = lean_ctor_get(v___x_1103_, 0);
                        v_isSharedCheck_1114_ = (!lean_is_exclusive(v___x_1103_)) as u8;
                        if v_isSharedCheck_1114_ == 0 {
                            v___x_1106_ = v___x_1103_;
                            v_isShared_1107_ = v_isSharedCheck_1114_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1104_);
                            lean_dec(v___x_1103_);
                            v___x_1106_ = lean_box(0);
                            v_isShared_1107_ = v_isSharedCheck_1114_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1115_ = lean_ctor_get(v___x_1103_, 0);
                        v_isSharedCheck_1122_ = (!lean_is_exclusive(v___x_1103_)) as u8;
                        if v_isSharedCheck_1122_ == 0 {
                            v___x_1117_ = v___x_1103_;
                            v_isShared_1118_ = v_isSharedCheck_1122_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1115_);
                            lean_dec(v___x_1103_);
                            v___x_1117_ = lean_box(0);
                            v_isShared_1118_ = v_isSharedCheck_1122_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_1123_ = l_Lean_Expr_appFn_x21(v_e_1094_);
                    v___x_1124_ = l_Lean_Expr_appFn_x21(v___x_1123_);
                    v___x_1125_ = l_Lean_Expr_appArg_x21(v___x_1124_);
                    lean_dec_ref(v___x_1124_);
                    v___x_1126_ = l_Lean_Expr_appArg_x21(v___x_1123_);
                    lean_dec_ref(v___x_1123_);
                    v___x_1127_ = l_Lean_Expr_appArg_x21(v_e_1094_);
                    lean_dec_ref(v_e_1094_);
                    v___x_1128_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1128_, 0, v___x_1126_);
                    lean_ctor_set(v___x_1128_, 1, v___x_1127_);
                    v___x_1129_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_1129_, 0, v___x_1125_);
                    lean_ctor_set(v___x_1129_, 1, v___x_1128_);
                    v___x_1130_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1130_, 0, v___x_1129_);
                    v___x_1131_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1131_, 0, v___x_1130_);
                    return v___x_1131_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_1104_) == 1 {
                    lean_del_object(v___x_1106_);
                    v_val_1108_ = lean_ctor_get(v_a_1104_, 0);
                    lean_inc(v_val_1108_);
                    lean_dec_ref_known(v_a_1104_, 1);
                    v___x_1109_ = l_Lean_Meta_matchEq_x3f(
                        v_val_1108_,
                        v___y_1095_,
                        v___y_1096_,
                        v___y_1097_,
                        v___y_1098_,
                    );
                    return v___x_1109_;
                } else {
                    lean_dec(v_a_1104_);
                    v___x_1110_ = lean_box(0);
                    if v_isShared_1107_ == 0 {
                        lean_ctor_set(v___x_1106_, 0, v___x_1110_);
                        v___x_1112_ = v___x_1106_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1113_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1113_, 0, v___x_1110_);
                        v___x_1112_ = v_reuseFailAlloc_1113_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1112_;
            }
            3 => {
                if v_isShared_1118_ == 0 {
                    v___x_1120_ = v___x_1117_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1121_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_a_1115_);
                    v___x_1120_ = v_reuseFailAlloc_1121_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1120_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchNe_x3f___lam__0___boxed(
    mut v_e_1132_: *mut LeanObject,
    mut v___y_1133_: *mut LeanObject,
    mut v___y_1134_: *mut LeanObject,
    mut v___y_1135_: *mut LeanObject,
    mut v___y_1136_: *mut LeanObject,
    mut v___y_1137_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1138_: *mut LeanObject = core::ptr::null_mut();
    v_res_1138_ = l_Lean_Meta_matchNe_x3f___lam__0(
        v_e_1132_,
        v___y_1133_,
        v___y_1134_,
        v___y_1135_,
        v___y_1136_,
    );
    lean_dec(v___y_1136_);
    lean_dec_ref(v___y_1135_);
    lean_dec(v___y_1134_);
    lean_dec_ref(v___y_1133_);
    return v_res_1138_;
}
pub unsafe fn l_Lean_Meta_matchNe_x3f(
    mut v_e_1139_: *mut LeanObject,
    mut v_a_1140_: *mut LeanObject,
    mut v_a_1141_: *mut LeanObject,
    mut v_a_1142_: *mut LeanObject,
    mut v_a_1143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1153_: u8 = 0;
    let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1139_);
                v___x_1145_ = l_Lean_Meta_matchNe_x3f___lam__0(
                    v_e_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_,
                );
                if lean_obj_tag(v___x_1145_) == 0 {
                    v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
                    lean_inc(v_a_1146_);
                    if lean_obj_tag(v_a_1146_) == 0 {
                        lean_dec_ref_known(v___x_1145_, 1);
                        lean_inc(v_a_1143_);
                        lean_inc_ref(v_a_1142_);
                        lean_inc(v_a_1141_);
                        lean_inc_ref(v_a_1140_);
                        v___x_1147_ =
                            lean_whnf(v_e_1139_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_);
                        if lean_obj_tag(v___x_1147_) == 0 {
                            v_a_1148_ = lean_ctor_get(v___x_1147_, 0);
                            lean_inc(v_a_1148_);
                            lean_dec_ref_known(v___x_1147_, 1);
                            v___x_1149_ = l_Lean_Meta_matchNe_x3f___lam__0(
                                v_a_1148_, v_a_1140_, v_a_1141_, v_a_1142_, v_a_1143_,
                            );
                            return v___x_1149_;
                        } else {
                            v_a_1150_ = lean_ctor_get(v___x_1147_, 0);
                            v_isSharedCheck_1157_ = (!lean_is_exclusive(v___x_1147_)) as u8;
                            if v_isSharedCheck_1157_ == 0 {
                                v___x_1152_ = v___x_1147_;
                                v_isShared_1153_ = v_isSharedCheck_1157_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1150_);
                                lean_dec(v___x_1147_);
                                v___x_1152_ = lean_box(0);
                                v_isShared_1153_ = v_isSharedCheck_1157_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1146_);
                        lean_dec_ref(v_e_1139_);
                        return v___x_1145_;
                    }
                } else {
                    lean_dec_ref(v_e_1139_);
                    return v___x_1145_;
                }
            }
            1 => {
                if v_isShared_1153_ == 0 {
                    v___x_1155_ = v___x_1152_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_a_1150_);
                    v___x_1155_ = v_reuseFailAlloc_1156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchNe_x3f___boxed(
    mut v_e_1158_: *mut LeanObject,
    mut v_a_1159_: *mut LeanObject,
    mut v_a_1160_: *mut LeanObject,
    mut v_a_1161_: *mut LeanObject,
    mut v_a_1162_: *mut LeanObject,
    mut v_a_1163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1164_: *mut LeanObject = core::ptr::null_mut();
    v_res_1164_ = l_Lean_Meta_matchNe_x3f(v_e_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
    lean_dec(v_a_1162_);
    lean_dec_ref(v_a_1161_);
    lean_dec(v_a_1160_);
    lean_dec_ref(v_a_1159_);
    return v_res_1164_;
}
pub unsafe fn l_Lean_Meta_matchConstructorApp_x3f(
    mut v_e_1165_: *mut LeanObject,
    mut v_a_1166_: *mut LeanObject,
    mut v_a_1167_: *mut LeanObject,
    mut v_a_1168_: *mut LeanObject,
    mut v_a_1169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1179_: u8 = 0;
    let mut v___x_1181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1183_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1165_);
                v___x_1171_ = l_Lean_Meta_isConstructorApp_x3f(
                    v_e_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_,
                );
                if lean_obj_tag(v___x_1171_) == 0 {
                    v_a_1172_ = lean_ctor_get(v___x_1171_, 0);
                    lean_inc(v_a_1172_);
                    if lean_obj_tag(v_a_1172_) == 0 {
                        lean_dec_ref_known(v___x_1171_, 1);
                        lean_inc(v_a_1169_);
                        lean_inc_ref(v_a_1168_);
                        lean_inc(v_a_1167_);
                        lean_inc_ref(v_a_1166_);
                        v___x_1173_ =
                            lean_whnf(v_e_1165_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_);
                        if lean_obj_tag(v___x_1173_) == 0 {
                            v_a_1174_ = lean_ctor_get(v___x_1173_, 0);
                            lean_inc(v_a_1174_);
                            lean_dec_ref_known(v___x_1173_, 1);
                            v___x_1175_ = l_Lean_Meta_isConstructorApp_x3f(
                                v_a_1174_, v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_,
                            );
                            return v___x_1175_;
                        } else {
                            v_a_1176_ = lean_ctor_get(v___x_1173_, 0);
                            v_isSharedCheck_1183_ = (!lean_is_exclusive(v___x_1173_)) as u8;
                            if v_isSharedCheck_1183_ == 0 {
                                v___x_1178_ = v___x_1173_;
                                v_isShared_1179_ = v_isSharedCheck_1183_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_1176_);
                                lean_dec(v___x_1173_);
                                v___x_1178_ = lean_box(0);
                                v_isShared_1179_ = v_isSharedCheck_1183_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_1172_);
                        lean_dec_ref(v_e_1165_);
                        return v___x_1171_;
                    }
                } else {
                    lean_dec_ref(v_e_1165_);
                    return v___x_1171_;
                }
            }
            1 => {
                if v_isShared_1179_ == 0 {
                    v___x_1181_ = v___x_1178_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1182_, 0, v_a_1176_);
                    v___x_1181_ = v_reuseFailAlloc_1182_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1181_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_matchConstructorApp_x3f___boxed(
    mut v_e_1184_: *mut LeanObject,
    mut v_a_1185_: *mut LeanObject,
    mut v_a_1186_: *mut LeanObject,
    mut v_a_1187_: *mut LeanObject,
    mut v_a_1188_: *mut LeanObject,
    mut v_a_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1190_: *mut LeanObject = core::ptr::null_mut();
    v_res_1190_ =
        l_Lean_Meta_matchConstructorApp_x3f(v_e_1184_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
    lean_dec(v_a_1188_);
    lean_dec_ref(v_a_1187_);
    lean_dec(v_a_1186_);
    lean_dec_ref(v_a_1185_);
    return v_res_1190_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_MatchUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_MatchUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_MatchUtil(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Util_Recognizers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_CtorRecognizer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_MatchUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_MatchUtil(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_MatchUtil(builtin);
}

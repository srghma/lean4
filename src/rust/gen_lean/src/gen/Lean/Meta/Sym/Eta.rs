// Lean compiler output
// Module: Lean.Meta.Sym.Eta
// Imports: Lean.Meta.Sym.ExprPtr Lean.Meta.Basic Lean.Meta.Transform
use crate::ffi::{
    lean_array_fget, lean_array_fset, lean_array_get_size, lean_array_uget_borrowed,
    lean_array_uset, lean_expr_has_loose_bvar, lean_expr_lower_loose_bvars, lean_find_expr,
    lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul, lean_nat_sub, lean_ptr_addr, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_dec_eq, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Prelude::l_Lean_maxRecDepthErrorMessage;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_forallE___override, l_Lean_Expr_hasLooseBVars,
    l_Lean_Expr_isLambda, l_Lean_Expr_lam___override, l_Lean_Expr_letE___override,
    l_Lean_Expr_mdata___override, l_Lean_Expr_proj___override, l_Lean_instBEqBinderInfo_beq,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, runtime_initialize_Lean_Meta_Basic,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    initialize_Lean_Meta_Sym_ExprPtr,
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1, runtime_initialize_Lean_Meta_Sym_ExprPtr,
};
use crate::r#gen::Lean::Meta::Transform::{
    initialize_Lean_Meta_Transform, runtime_initialize_Lean_Meta_Transform,
};
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [114, 117, 110, 116, 105, 109, 101, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [109, 97, 120, 82, 101, 99, 68, 101, 112, 116, 104, 0]};
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__0_value) as *mut crate::leanh::LeanObject,7310567555909517314 as *mut crate::leanh::LeanObject] };
pub static l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__1_value) as *mut crate::leanh::LeanObject,273128857561458264 as *mut crate::leanh::LeanObject] };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_etaReduceAll___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Sym_isEtaReducible___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Sym_etaReduceAll___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_etaReduceAll___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Sym_etaReduceAll___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_etaReduceAll___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Sym_etaReduceAll___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_etaReduceAll___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(
    mut v_e_594_: *mut crate::leanh::LeanObject,
    mut v_a_595_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_597_: u8 = 0;
    let mut v___x_598_: u8 = 0;
    let mut v_one_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_596_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_597_ = lean_nat_dec_eq(v_a_595_, v_zero_596_);
                if v_isZero_597_ == 1 {
                    crate::leanh::lean_dec(v_a_595_);
                    v___x_598_ = 0;
                    return v___x_598_;
                } else {
                    v_one_599_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_600_ = lean_nat_sub(v_a_595_, v_one_599_);
                    crate::leanh::lean_dec(v_a_595_);
                    v___x_601_ = lean_expr_has_loose_bvar(v_e_594_, v_n_600_);
                    if v___x_601_ == 0 {
                        v_a_595_ = v_n_600_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_n_600_);
                        return v___x_601_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go___boxed(
    mut v_e_603_: *mut crate::leanh::LeanObject,
    mut v_a_604_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_605_: u8 = 0;
    let mut v_r_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_605_ =
        l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(v_e_603_, v_a_604_);
    crate::leanh::lean_dec_ref(v_e_603_);
    v_r_606_ = crate::leanh::lean_box((v_res_605_) as usize);
    return v_r_606_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(
    mut v_e_607_: *mut crate::leanh::LeanObject,
    mut v_n_608_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_609_: u8 = 0;
    v___x_609_ = l_Lean_Expr_hasLooseBVars(v_e_607_);
    if v___x_609_ == 0 {
        crate::leanh::lean_dec(v_n_608_);
        return v___x_609_;
    } else {
        let mut v___x_610_: u8 = 0;
        v___x_610_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange_go(
            v_e_607_, v_n_608_,
        );
        return v___x_610_;
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange___boxed(
    mut v_e_611_: *mut crate::leanh::LeanObject,
    mut v_n_612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_613_: u8 = 0;
    let mut v_r_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_613_ =
        l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(v_e_611_, v_n_612_);
    crate::leanh::lean_dec_ref(v_e_611_);
    v_r_614_ = crate::leanh::lean_box((v_res_613_) as usize);
    return v_r_614_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(
    mut v_n_615_: *mut crate::leanh::LeanObject,
    mut v_default_616_: *mut crate::leanh::LeanObject,
    mut v_body_617_: *mut crate::leanh::LeanObject,
    mut v_m_618_: *mut crate::leanh::LeanObject,
    mut v_i_619_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_621_: u8 = 0;
    let mut v___x_622_: u8 = 0;
    let mut v___x_623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fn_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_deBruijnIndex_626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v_one_628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_620_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_621_ = lean_nat_dec_eq(v_m_618_, v_zero_620_);
                if v_isZero_621_ == 1 {
                    crate::leanh::lean_dec(v_i_619_);
                    crate::leanh::lean_dec(v_m_618_);
                    crate::leanh::lean_inc(v_n_615_);
                    v___x_622_ =
                        l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_hasLooseBVarsInRange(
                            v_body_617_,
                            v_n_615_,
                        );
                    if v___x_622_ == 0 {
                        v___x_623_ = lean_expr_lower_loose_bvars(v_body_617_, v_n_615_, v_n_615_);
                        crate::leanh::lean_dec(v_n_615_);
                        return v___x_623_;
                    } else {
                        crate::leanh::lean_dec(v_n_615_);
                        crate::leanh::lean_inc_ref(v_default_616_);
                        return v_default_616_;
                    }
                } else {
                    if crate::leanh::lean_obj_tag(v_body_617_) == 5 {
                        v_arg_624_ = crate::leanh::lean_ctor_get(v_body_617_, 1);
                        if crate::leanh::lean_obj_tag(v_arg_624_) == 0 {
                            v_fn_625_ = crate::leanh::lean_ctor_get(v_body_617_, 0);
                            v_deBruijnIndex_626_ = crate::leanh::lean_ctor_get(v_arg_624_, 0);
                            v___x_627_ = lean_nat_dec_eq(v_deBruijnIndex_626_, v_i_619_);
                            if v___x_627_ == 0 {
                                crate::leanh::lean_dec(v_i_619_);
                                crate::leanh::lean_dec(v_m_618_);
                                crate::leanh::lean_dec(v_n_615_);
                                crate::leanh::lean_inc_ref(v_default_616_);
                                return v_default_616_;
                            } else {
                                v_one_628_ = crate::leanh::lean_unsigned_to_nat(1);
                                v_n_629_ = lean_nat_sub(v_m_618_, v_one_628_);
                                crate::leanh::lean_dec(v_m_618_);
                                v___x_630_ = lean_nat_add(v_i_619_, v_one_628_);
                                crate::leanh::lean_dec(v_i_619_);
                                v_body_617_ = v_fn_625_;
                                v_m_618_ = v_n_629_;
                                v_i_619_ = v___x_630_;
                                state = 0;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_i_619_);
                            crate::leanh::lean_dec(v_m_618_);
                            crate::leanh::lean_dec(v_n_615_);
                            crate::leanh::lean_inc_ref(v_default_616_);
                            return v_default_616_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_619_);
                        crate::leanh::lean_dec(v_m_618_);
                        crate::leanh::lean_dec(v_n_615_);
                        crate::leanh::lean_inc_ref(v_default_616_);
                        return v_default_616_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go___boxed(
    mut v_n_632_: *mut crate::leanh::LeanObject,
    mut v_default_633_: *mut crate::leanh::LeanObject,
    mut v_body_634_: *mut crate::leanh::LeanObject,
    mut v_m_635_: *mut crate::leanh::LeanObject,
    mut v_i_636_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_637_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(
        v_n_632_,
        v_default_633_,
        v_body_634_,
        v_m_635_,
        v_i_636_,
    );
    crate::leanh::lean_dec_ref(v_body_634_);
    crate::leanh::lean_dec_ref(v_default_633_);
    return v_res_637_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(
    mut v_body_638_: *mut crate::leanh::LeanObject,
    mut v_n_639_: *mut crate::leanh::LeanObject,
    mut v_i_640_: *mut crate::leanh::LeanObject,
    mut v_default_641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_n_639_);
    v___x_642_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(
        v_n_639_,
        v_default_641_,
        v_body_638_,
        v_n_639_,
        v_i_640_,
    );
    return v___x_642_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux___boxed(
    mut v_body_643_: *mut crate::leanh::LeanObject,
    mut v_n_644_: *mut crate::leanh::LeanObject,
    mut v_i_645_: *mut crate::leanh::LeanObject,
    mut v_default_646_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_647_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux(
        v_body_643_,
        v_n_644_,
        v_i_645_,
        v_default_646_,
    );
    crate::leanh::lean_dec_ref(v_default_646_);
    crate::leanh::lean_dec_ref(v_body_643_);
    return v_res_647_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(
    mut v_e_648_: *mut crate::leanh::LeanObject,
    mut v_body_649_: *mut crate::leanh::LeanObject,
    mut v_n_650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_body_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_body_649_) == 6 {
                    v_body_651_ = crate::leanh::lean_ctor_get(v_body_649_, 2);
                    v___x_652_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_653_ = lean_nat_add(v_n_650_, v___x_652_);
                    crate::leanh::lean_dec(v_n_650_);
                    v_body_649_ = v_body_651_;
                    v_n_650_ = v___x_653_;
                    state = 0;
                    continue;
                } else {
                    v___x_655_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v_n_650_);
                    v___x_656_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceAux_go(
                        v_n_650_,
                        v_e_648_,
                        v_body_649_,
                        v_n_650_,
                        v___x_655_,
                    );
                    return v___x_656_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go___boxed(
    mut v_e_657_: *mut crate::leanh::LeanObject,
    mut v_body_658_: *mut crate::leanh::LeanObject,
    mut v_n_659_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_660_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(
        v_e_657_,
        v_body_658_,
        v_n_659_,
    );
    crate::leanh::lean_dec_ref(v_body_658_);
    crate::leanh::lean_dec_ref(v_e_657_);
    return v_res_660_;
}
pub unsafe fn l_Lean_Meta_Sym_etaReduce(
    mut v_e_661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_662_: u8 = 0;
    v___x_662_ = l_Lean_Expr_isLambda(v_e_661_);
    if v___x_662_ == 0 {
        crate::leanh::lean_inc_ref(v_e_661_);
        return v_e_661_;
    } else {
        let mut v___x_663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_663_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_664_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(
            v_e_661_, v_e_661_, v___x_663_,
        );
        return v___x_664_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_etaReduce___boxed(
    mut v_e_665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_666_ = l_Lean_Meta_Sym_etaReduce(v_e_665_);
    crate::leanh::lean_dec_ref(v_e_665_);
    return v_res_666_;
}
pub unsafe fn l_Lean_Meta_Sym_isEtaReducible(mut v_e_667_: *mut crate::leanh::LeanObject) -> u8 {
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: u8 = 0;
    v___x_668_ = l_Lean_Meta_Sym_etaReduce(v_e_667_);
    v___x_669_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v_e_667_, v___x_668_,
    );
    crate::leanh::lean_dec_ref(v___x_668_);
    if v___x_669_ == 0 {
        let mut v___x_670_: u8 = 0;
        v___x_670_ = 1;
        return v___x_670_;
    } else {
        let mut v___x_671_: u8 = 0;
        v___x_671_ = 0;
        return v___x_671_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_isEtaReducible___boxed(
    mut v_e_672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_673_: u8 = 0;
    let mut v_r_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_673_ = l_Lean_Meta_Sym_isEtaReducible(v_e_672_);
    crate::leanh::lean_dec_ref(v_e_672_);
    v_r_674_ = crate::leanh::lean_box((v_res_673_) as usize);
    return v_r_674_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(
    mut v_a_675_: *mut crate::leanh::LeanObject,
    mut v_b_676_: *mut crate::leanh::LeanObject,
    mut v_x_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_683_: u8 = 0;
    let mut v___x_684_: u8 = 0;
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_692_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_677_) == 0 {
                    crate::leanh::lean_dec(v_b_676_);
                    crate::leanh::lean_dec_ref(v_a_675_);
                    return v_x_677_;
                } else {
                    v_key_678_ = crate::leanh::lean_ctor_get(v_x_677_, 0);
                    v_value_679_ = crate::leanh::lean_ctor_get(v_x_677_, 1);
                    v_tail_680_ = crate::leanh::lean_ctor_get(v_x_677_, 2);
                    v_isSharedCheck_692_ = (!crate::leanh::lean_is_exclusive(v_x_677_)) as u8;
                    if v_isSharedCheck_692_ == 0 {
                        v___x_682_ = v_x_677_;
                        v_isShared_683_ = v_isSharedCheck_692_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_680_);
                        crate::leanh::lean_inc(v_value_679_);
                        crate::leanh::lean_inc(v_key_678_);
                        crate::leanh::lean_dec(v_x_677_);
                        v___x_682_ = crate::leanh::lean_box(0);
                        v_isShared_683_ = v_isSharedCheck_692_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_684_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_key_678_, v_a_675_,
                    );
                if v___x_684_ == 0 {
                    v___x_685_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_675_, v_b_676_, v_tail_680_);
                    if v_isShared_683_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_682_, 2, v___x_685_);
                        v___x_687_ = v___x_682_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_688_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_688_, 0, v_key_678_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_688_, 1, v_value_679_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_688_, 2, v___x_685_);
                        v___x_687_ = v_reuseFailAlloc_688_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_679_);
                    crate::leanh::lean_dec(v_key_678_);
                    if v_isShared_683_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_682_, 1, v_b_676_);
                        crate::leanh::lean_ctor_set(v___x_682_, 0, v_a_675_);
                        v___x_690_ = v___x_682_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_691_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 0, v_a_675_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 1, v_b_676_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 2, v_tail_680_);
                        v___x_690_ = v_reuseFailAlloc_691_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_687_;
            }
            3 => {
                return v___x_690_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(
    mut v_x_693_: *mut crate::leanh::LeanObject,
    mut v_x_694_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_700_: u8 = 0;
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: u64 = 0;
    let mut v___x_703_: u64 = 0;
    let mut v___x_704_: u64 = 0;
    let mut v_fold_705_: u64 = 0;
    let mut v___x_706_: u64 = 0;
    let mut v___x_707_: u64 = 0;
    let mut v___x_708_: u64 = 0;
    let mut v___x_709_: usize = 0;
    let mut v___x_710_: usize = 0;
    let mut v___x_711_: usize = 0;
    let mut v___x_712_: usize = 0;
    let mut v___x_713_: usize = 0;
    let mut v___x_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_720_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_694_) == 0 {
                    return v_x_693_;
                } else {
                    v_key_695_ = crate::leanh::lean_ctor_get(v_x_694_, 0);
                    v_value_696_ = crate::leanh::lean_ctor_get(v_x_694_, 1);
                    v_tail_697_ = crate::leanh::lean_ctor_get(v_x_694_, 2);
                    v_isSharedCheck_720_ = (!crate::leanh::lean_is_exclusive(v_x_694_)) as u8;
                    if v_isSharedCheck_720_ == 0 {
                        v___x_699_ = v_x_694_;
                        v_isShared_700_ = v_isSharedCheck_720_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_697_);
                        crate::leanh::lean_inc(v_value_696_);
                        crate::leanh::lean_inc(v_key_695_);
                        crate::leanh::lean_dec(v_x_694_);
                        v___x_699_ = crate::leanh::lean_box(0);
                        v_isShared_700_ = v_isSharedCheck_720_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_701_ = lean_array_get_size(v_x_693_);
                v___x_702_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_695_);
                v___x_703_ = 32u64;
                v___x_704_ = lean_uint64_shift_right(v___x_702_, v___x_703_);
                v_fold_705_ = lean_uint64_xor(v___x_702_, v___x_704_);
                v___x_706_ = 16u64;
                v___x_707_ = lean_uint64_shift_right(v_fold_705_, v___x_706_);
                v___x_708_ = lean_uint64_xor(v_fold_705_, v___x_707_);
                v___x_709_ = lean_uint64_to_usize(v___x_708_);
                v___x_710_ = lean_usize_of_nat(v___x_701_);
                v___x_711_ = 1usize;
                v___x_712_ = lean_usize_sub(v___x_710_, v___x_711_);
                v___x_713_ = lean_usize_land(v___x_709_, v___x_712_);
                v___x_714_ = lean_array_uget_borrowed(v_x_693_, v___x_713_);
                crate::leanh::lean_inc(v___x_714_);
                if v_isShared_700_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_699_, 2, v___x_714_);
                    v___x_716_ = v___x_699_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_719_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 0, v_key_695_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 1, v_value_696_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_719_, 2, v___x_714_);
                    v___x_716_ = v_reuseFailAlloc_719_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_717_ = lean_array_uset(v_x_693_, v___x_713_, v___x_716_);
                v_x_693_ = v___x_717_;
                v_x_694_ = v_tail_697_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(
    mut v_i_721_: *mut crate::leanh::LeanObject,
    mut v_source_722_: *mut crate::leanh::LeanObject,
    mut v_target_723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: u8 = 0;
    let mut v_es_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_724_ = lean_array_get_size(v_source_722_);
                v___x_725_ = lean_nat_dec_lt(v_i_721_, v___x_724_);
                if v___x_725_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_722_);
                    crate::leanh::lean_dec(v_i_721_);
                    return v_target_723_;
                } else {
                    v_es_726_ = lean_array_fget(v_source_722_, v_i_721_);
                    v___x_727_ = crate::leanh::lean_box(0);
                    v_source_728_ = lean_array_fset(v_source_722_, v_i_721_, v___x_727_);
                    v_target_729_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_target_723_, v_es_726_);
                    v___x_730_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_731_ = lean_nat_add(v_i_721_, v___x_730_);
                    crate::leanh::lean_dec(v_i_721_);
                    v_i_721_ = v___x_731_;
                    v_source_722_ = v_source_728_;
                    v_target_723_ = v_target_729_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(
    mut v_data_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_734_ = lean_array_get_size(v_data_733_);
    v___x_735_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_736_ = lean_nat_mul(v___x_734_, v___x_735_);
    v___x_737_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_738_ = crate::leanh::lean_box(0);
    v___x_739_ = lean_mk_array(v_nbuckets_736_, v___x_738_);
    v___x_740_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v___x_737_, v_data_733_, v___x_739_);
    return v___x_740_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(
    mut v_a_741_: *mut crate::leanh::LeanObject,
    mut v_x_742_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_743_: u8 = 0;
    let mut v_key_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_742_) == 0 {
                    v___x_743_ = 0;
                    return v___x_743_;
                } else {
                    v_key_744_ = crate::leanh::lean_ctor_get(v_x_742_, 0);
                    v_tail_745_ = crate::leanh::lean_ctor_get(v_x_742_, 2);
                    v___x_746_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_744_, v_a_741_,
                        );
                    if v___x_746_ == 0 {
                        v_x_742_ = v_tail_745_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_746_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg___boxed(
    mut v_a_748_: *mut crate::leanh::LeanObject,
    mut v_x_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_750_: u8 = 0;
    let mut v_r_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_750_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_748_, v_x_749_);
    crate::leanh::lean_dec(v_x_749_);
    crate::leanh::lean_dec_ref(v_a_748_);
    v_r_751_ = crate::leanh::lean_box((v_res_750_) as usize);
    return v_r_751_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(
    mut v_m_752_: *mut crate::leanh::LeanObject,
    mut v_a_753_: *mut crate::leanh::LeanObject,
    mut v_b_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v___x_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: u64 = 0;
    let mut v___x_762_: u64 = 0;
    let mut v___x_763_: u64 = 0;
    let mut v_fold_764_: u64 = 0;
    let mut v___x_765_: u64 = 0;
    let mut v___x_766_: u64 = 0;
    let mut v___x_767_: u64 = 0;
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut v___x_770_: usize = 0;
    let mut v___x_771_: usize = 0;
    let mut v___x_772_: usize = 0;
    let mut v_bkt_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: u8 = 0;
    let mut v_val_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_755_ = crate::leanh::lean_ctor_get(v_m_752_, 0);
                v_buckets_756_ = crate::leanh::lean_ctor_get(v_m_752_, 1);
                v_isSharedCheck_799_ = (!crate::leanh::lean_is_exclusive(v_m_752_)) as u8;
                if v_isSharedCheck_799_ == 0 {
                    v___x_758_ = v_m_752_;
                    v_isShared_759_ = v_isSharedCheck_799_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_756_);
                    crate::leanh::lean_inc(v_size_755_);
                    crate::leanh::lean_dec(v_m_752_);
                    v___x_758_ = crate::leanh::lean_box(0);
                    v_isShared_759_ = v_isSharedCheck_799_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_760_ = lean_array_get_size(v_buckets_756_);
                v___x_761_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_753_);
                v___x_762_ = 32u64;
                v___x_763_ = lean_uint64_shift_right(v___x_761_, v___x_762_);
                v_fold_764_ = lean_uint64_xor(v___x_761_, v___x_763_);
                v___x_765_ = 16u64;
                v___x_766_ = lean_uint64_shift_right(v_fold_764_, v___x_765_);
                v___x_767_ = lean_uint64_xor(v_fold_764_, v___x_766_);
                v___x_768_ = lean_uint64_to_usize(v___x_767_);
                v___x_769_ = lean_usize_of_nat(v___x_760_);
                v___x_770_ = 1usize;
                v___x_771_ = lean_usize_sub(v___x_769_, v___x_770_);
                v___x_772_ = lean_usize_land(v___x_768_, v___x_771_);
                v_bkt_773_ = lean_array_uget_borrowed(v_buckets_756_, v___x_772_);
                v___x_774_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_753_, v_bkt_773_);
                if v___x_774_ == 0 {
                    v___x_775_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_776_ = lean_nat_add(v_size_755_, v___x_775_);
                    crate::leanh::lean_dec(v_size_755_);
                    crate::leanh::lean_inc(v_bkt_773_);
                    v___x_777_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_777_, 0, v_a_753_);
                    crate::leanh::lean_ctor_set(v___x_777_, 1, v_b_754_);
                    crate::leanh::lean_ctor_set(v___x_777_, 2, v_bkt_773_);
                    v_buckets_x27_778_ = lean_array_uset(v_buckets_756_, v___x_772_, v___x_777_);
                    v___x_779_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_780_ = lean_nat_mul(v_size_x27_776_, v___x_779_);
                    v___x_781_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_782_ = lean_nat_div(v___x_780_, v___x_781_);
                    crate::leanh::lean_dec(v___x_780_);
                    v___x_783_ = lean_array_get_size(v_buckets_x27_778_);
                    v___x_784_ = lean_nat_dec_le(v___x_782_, v___x_783_);
                    crate::leanh::lean_dec(v___x_782_);
                    if v___x_784_ == 0 {
                        v_val_785_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_buckets_x27_778_);
                        if v_isShared_759_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_758_, 1, v_val_785_);
                            crate::leanh::lean_ctor_set(v___x_758_, 0, v_size_x27_776_);
                            v___x_787_ = v___x_758_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 0, v_size_x27_776_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_788_, 1, v_val_785_);
                            v___x_787_ = v_reuseFailAlloc_788_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_759_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_758_, 1, v_buckets_x27_778_);
                            crate::leanh::lean_ctor_set(v___x_758_, 0, v_size_x27_776_);
                            v___x_790_ = v___x_758_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_791_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_791_, 0, v_size_x27_776_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_791_,
                                1,
                                v_buckets_x27_778_,
                            );
                            v___x_790_ = v_reuseFailAlloc_791_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_773_);
                    v___x_792_ = crate::leanh::lean_box(0);
                    v_buckets_x27_793_ = lean_array_uset(v_buckets_756_, v___x_772_, v___x_792_);
                    v___x_794_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_753_, v_b_754_, v_bkt_773_);
                    v___x_795_ = lean_array_uset(v_buckets_x27_793_, v___x_772_, v___x_794_);
                    if v_isShared_759_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_758_, 1, v___x_795_);
                        v___x_797_ = v___x_758_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_798_, 0, v_size_755_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_798_, 1, v___x_795_);
                        v___x_797_ = v_reuseFailAlloc_798_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_787_;
            }
            3 => {
                return v___x_790_;
            }
            4 => {
                return v___x_797_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(
    mut v_e_800_: *mut crate::leanh::LeanObject,
    mut v_e_x27_801_: *mut crate::leanh::LeanObject,
    mut v_a_802_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_804_ = lean_st_ref_take(v_a_802_);
    crate::leanh::lean_inc_ref(v_e_x27_801_);
    v___x_805_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v___x_804_, v_e_800_, v_e_x27_801_);
    v___x_806_ = lean_st_ref_set(v_a_802_, v___x_805_);
    v___x_807_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_807_, 0, v_e_x27_801_);
    return v___x_807_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg___boxed(
    mut v_e_808_: *mut crate::leanh::LeanObject,
    mut v_e_x27_809_: *mut crate::leanh::LeanObject,
    mut v_a_810_: *mut crate::leanh::LeanObject,
    mut v_a_811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_812_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(
        v_e_808_,
        v_e_x27_809_,
        v_a_810_,
    );
    crate::leanh::lean_dec(v_a_810_);
    return v_res_812_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(
    mut v_e_813_: *mut crate::leanh::LeanObject,
    mut v_e_x27_814_: *mut crate::leanh::LeanObject,
    mut v_a_815_: *mut crate::leanh::LeanObject,
    mut v_a_816_: *mut crate::leanh::LeanObject,
    mut v_a_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(
        v_e_813_,
        v_e_x27_814_,
        v_a_815_,
    );
    return v___x_819_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___boxed(
    mut v_e_820_: *mut crate::leanh::LeanObject,
    mut v_e_x27_821_: *mut crate::leanh::LeanObject,
    mut v_a_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v_a_824_: *mut crate::leanh::LeanObject,
    mut v_a_825_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_826_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache(
        v_e_820_,
        v_e_x27_821_,
        v_a_822_,
        v_a_823_,
        v_a_824_,
    );
    crate::leanh::lean_dec(v_a_824_);
    crate::leanh::lean_dec_ref(v_a_823_);
    crate::leanh::lean_dec(v_a_822_);
    return v_res_826_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0(
    mut v_00_u03b2_827_: *mut crate::leanh::LeanObject,
    mut v_m_828_: *mut crate::leanh::LeanObject,
    mut v_a_829_: *mut crate::leanh::LeanObject,
    mut v_b_830_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_831_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0___redArg(v_m_828_, v_a_829_, v_b_830_);
    return v___x_831_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(
    mut v_00_u03b2_832_: *mut crate::leanh::LeanObject,
    mut v_a_833_: *mut crate::leanh::LeanObject,
    mut v_x_834_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_835_: u8 = 0;
    v___x_835_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___redArg(v_a_833_, v_x_834_);
    return v___x_835_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0___boxed(
    mut v_00_u03b2_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_x_838_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_839_: u8 = 0;
    let mut v_r_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_839_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__0(v_00_u03b2_836_, v_a_837_, v_x_838_);
    crate::leanh::lean_dec(v_x_838_);
    crate::leanh::lean_dec_ref(v_a_837_);
    v_r_840_ = crate::leanh::lean_box((v_res_839_) as usize);
    return v_r_840_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1(
    mut v_00_u03b2_841_: *mut crate::leanh::LeanObject,
    mut v_data_842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_843_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1___redArg(v_data_842_);
    return v___x_843_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2(
    mut v_00_u03b2_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_b_846_: *mut crate::leanh::LeanObject,
    mut v_x_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_848_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__2___redArg(v_a_845_, v_b_846_, v_x_847_);
    return v___x_848_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2(
    mut v_00_u03b2_849_: *mut crate::leanh::LeanObject,
    mut v_i_850_: *mut crate::leanh::LeanObject,
    mut v_source_851_: *mut crate::leanh::LeanObject,
    mut v_target_852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_853_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2___redArg(v_i_850_, v_source_851_, v_target_852_);
    return v___x_853_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3(
    mut v_00_u03b2_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v_x_856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_857_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache_spec__0_spec__1_spec__2_spec__3___redArg(v_x_855_, v_x_856_);
    return v___x_857_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_863_ = l_Lean_maxRecDepthErrorMessage;
    v___x_864_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_864_, 0, v___x_863_);
    return v___x_864_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_865_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__3);
    v___x_866_ = l_Lean_MessageData_ofFormat(v___x_865_);
    return v___x_866_;
}
pub unsafe fn _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__4);
    v___x_868_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__2;
    v___x_869_ = crate::leanh::lean_alloc_ctor(8, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_869_, 0, v___x_868_);
    crate::leanh::lean_ctor_set(v___x_869_, 1, v___x_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(
    mut v_ref_870_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_872_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5_once), _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___closed__5);
    v___x_873_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_873_, 0, v_ref_870_);
    crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_872_);
    v___x_874_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_874_, 0, v___x_873_);
    return v___x_874_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg___boxed(
    mut v_ref_875_: *mut crate::leanh::LeanObject,
    mut v___y_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_877_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_875_);
    return v_res_877_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_ref_879_: *mut crate::leanh::LeanObject,
    mut v___y_880_: *mut crate::leanh::LeanObject,
    mut v___y_881_: *mut crate::leanh::LeanObject,
    mut v___y_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_884_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_879_);
    return v___x_884_;
}
pub unsafe fn l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___boxed(
    mut v_00_u03b1_885_: *mut crate::leanh::LeanObject,
    mut v_ref_886_: *mut crate::leanh::LeanObject,
    mut v___y_887_: *mut crate::leanh::LeanObject,
    mut v___y_888_: *mut crate::leanh::LeanObject,
    mut v___y_889_: *mut crate::leanh::LeanObject,
    mut v___y_890_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_891_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1(v_00_u03b1_885_, v_ref_886_, v___y_887_, v___y_888_, v___y_889_);
    crate::leanh::lean_dec(v___y_889_);
    crate::leanh::lean_dec_ref(v___y_888_);
    crate::leanh::lean_dec(v___y_887_);
    return v_res_891_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(
    mut v_a_892_: *mut crate::leanh::LeanObject,
    mut v_x_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: u8 = 0;
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_893_) == 0 {
                    v___x_894_ = crate::leanh::lean_box(0);
                    return v___x_894_;
                } else {
                    v_key_895_ = crate::leanh::lean_ctor_get(v_x_893_, 0);
                    v_value_896_ = crate::leanh::lean_ctor_get(v_x_893_, 1);
                    v_tail_897_ = crate::leanh::lean_ctor_get(v_x_893_, 2);
                    v___x_898_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_895_, v_a_892_,
                        );
                    if v___x_898_ == 0 {
                        v_x_893_ = v_tail_897_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_896_);
                        v___x_900_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_900_, 0, v_value_896_);
                        return v___x_900_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg___boxed(
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_x_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_901_, v_x_902_);
    crate::leanh::lean_dec(v_x_902_);
    crate::leanh::lean_dec_ref(v_a_901_);
    return v_res_903_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(
    mut v_m_904_: *mut crate::leanh::LeanObject,
    mut v_a_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: u64 = 0;
    let mut v___x_909_: u64 = 0;
    let mut v___x_910_: u64 = 0;
    let mut v_fold_911_: u64 = 0;
    let mut v___x_912_: u64 = 0;
    let mut v___x_913_: u64 = 0;
    let mut v___x_914_: u64 = 0;
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_906_ = crate::leanh::lean_ctor_get(v_m_904_, 1);
    v___x_907_ = lean_array_get_size(v_buckets_906_);
    v___x_908_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_905_);
    v___x_909_ = 32u64;
    v___x_910_ = lean_uint64_shift_right(v___x_908_, v___x_909_);
    v_fold_911_ = lean_uint64_xor(v___x_908_, v___x_910_);
    v___x_912_ = 16u64;
    v___x_913_ = lean_uint64_shift_right(v_fold_911_, v___x_912_);
    v___x_914_ = lean_uint64_xor(v_fold_911_, v___x_913_);
    v___x_915_ = lean_uint64_to_usize(v___x_914_);
    v___x_916_ = lean_usize_of_nat(v___x_907_);
    v___x_917_ = 1usize;
    v___x_918_ = lean_usize_sub(v___x_916_, v___x_917_);
    v___x_919_ = lean_usize_land(v___x_915_, v___x_918_);
    v___x_920_ = lean_array_uget_borrowed(v_buckets_906_, v___x_919_);
    v___x_921_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_905_, v___x_920_);
    return v___x_921_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg___boxed(
    mut v_m_922_: *mut crate::leanh::LeanObject,
    mut v_a_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_922_, v_a_923_);
    crate::leanh::lean_dec_ref(v_a_923_);
    crate::leanh::lean_dec_ref(v_m_922_);
    return v_res_924_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(
    mut v_e_925_: *mut crate::leanh::LeanObject,
    mut v_a_926_: *mut crate::leanh::LeanObject,
    mut v_a_927_: *mut crate::leanh::LeanObject,
    mut v_a_928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_932_: u8 = 0;
    let mut v___y_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_935_: u8 = 0;
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: u8 = 0;
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_946_: u8 = 0;
    let mut v___y_947_: u8 = 0;
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: u8 = 0;
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_955_: u8 = 0;
    let mut v___y_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_961_: u8 = 0;
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: usize = 0;
    let mut v___x_965_: usize = 0;
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_973_: u8 = 0;
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_989_: u8 = 0;
    let mut v_cancelTk_x3f_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_991_: u8 = 0;
    let mut v_inheritedTraceOptions_992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_999_: u8 = 0;
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1003_: u8 = 0;
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderName_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1010_: u8 = 0;
    let mut v___x_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: usize = 0;
    let mut v___x_1016_: usize = 0;
    let mut v___x_1017_: u8 = 0;
    let mut v___x_1018_: usize = 0;
    let mut v___x_1019_: usize = 0;
    let mut v___x_1020_: u8 = 0;
    let mut v_binderName_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderType_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderInfo_1024_: u8 = 0;
    let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: u8 = 0;
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: usize = 0;
    let mut v___x_1037_: u8 = 0;
    let mut v___x_1038_: usize = 0;
    let mut v___x_1039_: usize = 0;
    let mut v___x_1040_: u8 = 0;
    let mut v_declName_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_body_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nondep_1045_: u8 = 0;
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: usize = 0;
    let mut v___x_1053_: usize = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: usize = 0;
    let mut v___x_1056_: usize = 0;
    let mut v___x_1057_: u8 = 0;
    let mut v_fn_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1064_: usize = 0;
    let mut v___x_1065_: usize = 0;
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: usize = 0;
    let mut v___x_1068_: usize = 0;
    let mut v___x_1069_: u8 = 0;
    let mut v_data_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: usize = 0;
    let mut v___x_1075_: usize = 0;
    let mut v___x_1076_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_idx_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: usize = 0;
    let mut v___x_1086_: usize = 0;
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: u8 = 0;
    let mut v___x_1094_: u8 = 0;
    let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_977_ = crate::leanh::lean_ctor_get(v_a_927_, 0);
                v_fileMap_978_ = crate::leanh::lean_ctor_get(v_a_927_, 1);
                v_options_979_ = crate::leanh::lean_ctor_get(v_a_927_, 2);
                v_currRecDepth_980_ = crate::leanh::lean_ctor_get(v_a_927_, 3);
                v_maxRecDepth_981_ = crate::leanh::lean_ctor_get(v_a_927_, 4);
                v_ref_982_ = crate::leanh::lean_ctor_get(v_a_927_, 5);
                v_currNamespace_983_ = crate::leanh::lean_ctor_get(v_a_927_, 6);
                v_openDecls_984_ = crate::leanh::lean_ctor_get(v_a_927_, 7);
                v_initHeartbeats_985_ = crate::leanh::lean_ctor_get(v_a_927_, 8);
                v_maxHeartbeats_986_ = crate::leanh::lean_ctor_get(v_a_927_, 9);
                v_quotContext_987_ = crate::leanh::lean_ctor_get(v_a_927_, 10);
                v_currMacroScope_988_ = crate::leanh::lean_ctor_get(v_a_927_, 11);
                v_diag_989_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_990_ = crate::leanh::lean_ctor_get(v_a_927_, 12);
                v_suppressElabErrors_991_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_927_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_992_ = crate::leanh::lean_ctor_get(v_a_927_, 13);
                v___x_1092_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1093_ = lean_nat_dec_eq(v_maxRecDepth_981_, v___x_1092_);
                if v___x_1093_ == 0 {
                    v___x_1094_ = lean_nat_dec_eq(v_currRecDepth_980_, v_maxRecDepth_981_);
                    if v___x_1094_ == 0 {
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_e_925_);
                        crate::leanh::lean_inc(v_ref_982_);
                        v___x_1095_ = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__1___redArg(v_ref_982_);
                        return v___x_1095_;
                    }
                } else {
                    state = 5;
                    continue;
                }
            }
            1 => {
                if v___y_935_ == 0 {
                    v___x_936_ = l_Lean_Expr_forallE___override(
                        v___y_931_, v___y_933_, v___y_934_, v___y_932_,
                    );
                    v___x_937_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_936_, v_a_926_);
                    return v___x_937_;
                } else {
                    v___x_938_ = l_Lean_instBEqBinderInfo_beq(v___y_932_, v___y_932_);
                    if v___x_938_ == 0 {
                        v___x_939_ = l_Lean_Expr_forallE___override(
                            v___y_931_, v___y_933_, v___y_934_, v___y_932_,
                        );
                        v___x_940_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_939_, v_a_926_);
                        return v___x_940_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_934_);
                        crate::leanh::lean_dec_ref(v___y_933_);
                        crate::leanh::lean_dec(v___y_931_);
                        crate::leanh::lean_inc_ref(v_e_925_);
                        v___x_941_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                        return v___x_941_;
                    }
                }
            }
            2 => {
                if v___y_947_ == 0 {
                    v___x_948_ =
                        l_Lean_Expr_lam___override(v___y_943_, v___y_945_, v___y_944_, v___y_946_);
                    v___x_949_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_948_, v_a_926_);
                    return v___x_949_;
                } else {
                    v___x_950_ = l_Lean_instBEqBinderInfo_beq(v___y_946_, v___y_946_);
                    if v___x_950_ == 0 {
                        v___x_951_ = l_Lean_Expr_lam___override(
                            v___y_943_, v___y_945_, v___y_944_, v___y_946_,
                        );
                        v___x_952_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_951_, v_a_926_);
                        return v___x_952_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_945_);
                        crate::leanh::lean_dec_ref(v___y_944_);
                        crate::leanh::lean_dec(v___y_943_);
                        crate::leanh::lean_inc_ref(v_e_925_);
                        v___x_953_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                        return v___x_953_;
                    }
                }
            }
            3 => {
                if v___y_961_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_960_);
                    v___x_962_ = l_Lean_Expr_letE___override(
                        v___y_957_, v___y_959_, v___y_956_, v___y_958_, v___y_955_,
                    );
                    v___x_963_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_962_, v_a_926_);
                    return v___x_963_;
                } else {
                    v___x_964_ = lean_ptr_addr(v___y_960_);
                    crate::leanh::lean_dec_ref(v___y_960_);
                    v___x_965_ = lean_ptr_addr(v___y_958_);
                    v___x_966_ = lean_usize_dec_eq(v___x_964_, v___x_965_);
                    if v___x_966_ == 0 {
                        v___x_967_ = l_Lean_Expr_letE___override(
                            v___y_957_, v___y_959_, v___y_956_, v___y_958_, v___y_955_,
                        );
                        v___x_968_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_967_, v_a_926_);
                        return v___x_968_;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_959_);
                        crate::leanh::lean_dec_ref(v___y_958_);
                        crate::leanh::lean_dec(v___y_957_);
                        crate::leanh::lean_dec_ref(v___y_956_);
                        crate::leanh::lean_inc_ref(v_e_925_);
                        v___x_969_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                        return v___x_969_;
                    }
                }
            }
            4 => {
                if v___y_973_ == 0 {
                    v___x_974_ = l_Lean_Expr_app___override(v___y_972_, v___y_971_);
                    v___x_975_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_974_, v_a_926_);
                    return v___x_975_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_972_);
                    crate::leanh::lean_dec_ref(v___y_971_);
                    crate::leanh::lean_inc_ref(v_e_925_);
                    v___x_976_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                    return v___x_976_;
                }
            }
            5 => {
                v___x_994_ = lean_st_ref_get(v_a_926_);
                v___x_995_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v___x_994_, v_e_925_);
                crate::leanh::lean_dec(v___x_994_);
                if crate::leanh::lean_obj_tag(v___x_995_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_925_);
                    v_val_996_ = crate::leanh::lean_ctor_get(v___x_995_, 0);
                    v_isSharedCheck_1003_ = (!crate::leanh::lean_is_exclusive(v___x_995_)) as u8;
                    if v_isSharedCheck_1003_ == 0 {
                        v___x_998_ = v___x_995_;
                        v_isShared_999_ = v_isSharedCheck_1003_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_996_);
                        crate::leanh::lean_dec(v___x_995_);
                        v___x_998_ = crate::leanh::lean_box(0);
                        v_isShared_999_ = v_isSharedCheck_1003_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_995_);
                    v___x_1004_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1005_ = lean_nat_add(v_currRecDepth_980_, v___x_1004_);
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_992_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_990_);
                    crate::leanh::lean_inc(v_currMacroScope_988_);
                    crate::leanh::lean_inc(v_quotContext_987_);
                    crate::leanh::lean_inc(v_maxHeartbeats_986_);
                    crate::leanh::lean_inc(v_initHeartbeats_985_);
                    crate::leanh::lean_inc(v_openDecls_984_);
                    crate::leanh::lean_inc(v_currNamespace_983_);
                    crate::leanh::lean_inc(v_ref_982_);
                    crate::leanh::lean_inc(v_maxRecDepth_981_);
                    crate::leanh::lean_inc_ref(v_options_979_);
                    crate::leanh::lean_inc_ref(v_fileMap_978_);
                    crate::leanh::lean_inc_ref(v_fileName_977_);
                    v___x_1006_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_1006_, 0, v_fileName_977_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 1, v_fileMap_978_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 2, v_options_979_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 3, v___x_1005_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 4, v_maxRecDepth_981_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 5, v_ref_982_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 6, v_currNamespace_983_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 7, v_openDecls_984_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 8, v_initHeartbeats_985_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 9, v_maxHeartbeats_986_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 10, v_quotContext_987_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 11, v_currMacroScope_988_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 12, v_cancelTk_x3f_990_);
                    crate::leanh::lean_ctor_set(v___x_1006_, 13, v_inheritedTraceOptions_992_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_989_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_1006_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_991_,
                    );
                    match crate::leanh::lean_obj_tag(v_e_925_) {
                        7 => {
                            v_binderName_1007_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_binderType_1008_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            v_body_1009_ = crate::leanh::lean_ctor_get(v_e_925_, 2);
                            v_binderInfo_1010_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_925_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_binderType_1008_);
                            v___x_1011_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_1008_, v_a_926_, v___x_1006_, v_a_928_);
                            if crate::leanh::lean_obj_tag(v___x_1011_) == 0 {
                                v_a_1012_ = crate::leanh::lean_ctor_get(v___x_1011_, 0);
                                crate::leanh::lean_inc(v_a_1012_);
                                crate::leanh::lean_dec_ref_known(v___x_1011_, 1);
                                crate::leanh::lean_inc_ref(v_body_1009_);
                                v___x_1013_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_1009_, v_a_926_, v___x_1006_, v_a_928_);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                if crate::leanh::lean_obj_tag(v___x_1013_) == 0 {
                                    v_a_1014_ = crate::leanh::lean_ctor_get(v___x_1013_, 0);
                                    crate::leanh::lean_inc(v_a_1014_);
                                    crate::leanh::lean_dec_ref_known(v___x_1013_, 1);
                                    v___x_1015_ = lean_ptr_addr(v_binderType_1008_);
                                    v___x_1016_ = lean_ptr_addr(v_a_1012_);
                                    v___x_1017_ = lean_usize_dec_eq(v___x_1015_, v___x_1016_);
                                    if v___x_1017_ == 0 {
                                        crate::leanh::lean_inc(v_binderName_1007_);
                                        v___y_931_ = v_binderName_1007_;
                                        v___y_932_ = v_binderInfo_1010_;
                                        v___y_933_ = v_a_1012_;
                                        v___y_934_ = v_a_1014_;
                                        v___y_935_ = v___x_1017_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_1018_ = lean_ptr_addr(v_body_1009_);
                                        v___x_1019_ = lean_ptr_addr(v_a_1014_);
                                        v___x_1020_ = lean_usize_dec_eq(v___x_1018_, v___x_1019_);
                                        crate::leanh::lean_inc(v_binderName_1007_);
                                        v___y_931_ = v_binderName_1007_;
                                        v___y_932_ = v_binderInfo_1010_;
                                        v___y_933_ = v_a_1012_;
                                        v___y_934_ = v_a_1014_;
                                        v___y_935_ = v___x_1020_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1012_);
                                    crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                    return v___x_1013_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                return v___x_1011_;
                            }
                        }
                        6 => {
                            v_binderName_1021_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_binderType_1022_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            v_body_1023_ = crate::leanh::lean_ctor_get(v_e_925_, 2);
                            v_binderInfo_1024_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_925_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8)
                                    as u32,
                            );
                            v___x_1025_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_1026_ =
                                l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduce_go(
                                    v_e_925_,
                                    v_e_925_,
                                    v___x_1025_,
                                );
                            v___x_1027_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_e_925_, v___x_1026_);
                            if v___x_1027_ == 0 {
                                v___x_1028_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v___x_1026_, v_a_926_, v___x_1006_, v_a_928_);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                if crate::leanh::lean_obj_tag(v___x_1028_) == 0 {
                                    v_a_1029_ = crate::leanh::lean_ctor_get(v___x_1028_, 0);
                                    crate::leanh::lean_inc(v_a_1029_);
                                    crate::leanh::lean_dec_ref_known(v___x_1028_, 1);
                                    v___x_1030_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_a_1029_, v_a_926_);
                                    return v___x_1030_;
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                    return v___x_1028_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_1026_);
                                crate::leanh::lean_inc_ref(v_binderType_1022_);
                                v___x_1031_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_binderType_1022_, v_a_926_, v___x_1006_, v_a_928_);
                                if crate::leanh::lean_obj_tag(v___x_1031_) == 0 {
                                    v_a_1032_ = crate::leanh::lean_ctor_get(v___x_1031_, 0);
                                    crate::leanh::lean_inc(v_a_1032_);
                                    crate::leanh::lean_dec_ref_known(v___x_1031_, 1);
                                    crate::leanh::lean_inc_ref(v_body_1023_);
                                    v___x_1033_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_1023_, v_a_926_, v___x_1006_, v_a_928_);
                                    crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                    if crate::leanh::lean_obj_tag(v___x_1033_) == 0 {
                                        v_a_1034_ = crate::leanh::lean_ctor_get(v___x_1033_, 0);
                                        crate::leanh::lean_inc(v_a_1034_);
                                        crate::leanh::lean_dec_ref_known(v___x_1033_, 1);
                                        v___x_1035_ = lean_ptr_addr(v_binderType_1022_);
                                        v___x_1036_ = lean_ptr_addr(v_a_1032_);
                                        v___x_1037_ = lean_usize_dec_eq(v___x_1035_, v___x_1036_);
                                        if v___x_1037_ == 0 {
                                            crate::leanh::lean_inc(v_binderName_1021_);
                                            v___y_943_ = v_binderName_1021_;
                                            v___y_944_ = v_a_1034_;
                                            v___y_945_ = v_a_1032_;
                                            v___y_946_ = v_binderInfo_1024_;
                                            v___y_947_ = v___x_1037_;
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_1038_ = lean_ptr_addr(v_body_1023_);
                                            v___x_1039_ = lean_ptr_addr(v_a_1034_);
                                            v___x_1040_ =
                                                lean_usize_dec_eq(v___x_1038_, v___x_1039_);
                                            crate::leanh::lean_inc(v_binderName_1021_);
                                            v___y_943_ = v_binderName_1021_;
                                            v___y_944_ = v_a_1034_;
                                            v___y_945_ = v_a_1032_;
                                            v___y_946_ = v_binderInfo_1024_;
                                            v___y_947_ = v___x_1040_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1032_);
                                        crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                        return v___x_1033_;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                    crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                    return v___x_1031_;
                                }
                            }
                        }
                        8 => {
                            v_declName_1041_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_type_1042_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            v_value_1043_ = crate::leanh::lean_ctor_get(v_e_925_, 2);
                            v_body_1044_ = crate::leanh::lean_ctor_get(v_e_925_, 3);
                            v_nondep_1045_ = crate::leanh::lean_ctor_get_uint8(
                                v_e_925_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 8)
                                    as u32,
                            );
                            crate::leanh::lean_inc_ref(v_type_1042_);
                            v___x_1046_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_type_1042_, v_a_926_, v___x_1006_, v_a_928_);
                            if crate::leanh::lean_obj_tag(v___x_1046_) == 0 {
                                v_a_1047_ = crate::leanh::lean_ctor_get(v___x_1046_, 0);
                                crate::leanh::lean_inc(v_a_1047_);
                                crate::leanh::lean_dec_ref_known(v___x_1046_, 1);
                                crate::leanh::lean_inc_ref(v_value_1043_);
                                v___x_1048_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_value_1043_, v_a_926_, v___x_1006_, v_a_928_);
                                if crate::leanh::lean_obj_tag(v___x_1048_) == 0 {
                                    v_a_1049_ = crate::leanh::lean_ctor_get(v___x_1048_, 0);
                                    crate::leanh::lean_inc(v_a_1049_);
                                    crate::leanh::lean_dec_ref_known(v___x_1048_, 1);
                                    crate::leanh::lean_inc_ref(v_body_1044_);
                                    v___x_1050_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_body_1044_, v_a_926_, v___x_1006_, v_a_928_);
                                    crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                    if crate::leanh::lean_obj_tag(v___x_1050_) == 0 {
                                        v_a_1051_ = crate::leanh::lean_ctor_get(v___x_1050_, 0);
                                        crate::leanh::lean_inc(v_a_1051_);
                                        crate::leanh::lean_dec_ref_known(v___x_1050_, 1);
                                        v___x_1052_ = lean_ptr_addr(v_type_1042_);
                                        v___x_1053_ = lean_ptr_addr(v_a_1047_);
                                        v___x_1054_ = lean_usize_dec_eq(v___x_1052_, v___x_1053_);
                                        if v___x_1054_ == 0 {
                                            crate::leanh::lean_inc_ref(v_body_1044_);
                                            crate::leanh::lean_inc(v_declName_1041_);
                                            v___y_955_ = v_nondep_1045_;
                                            v___y_956_ = v_a_1049_;
                                            v___y_957_ = v_declName_1041_;
                                            v___y_958_ = v_a_1051_;
                                            v___y_959_ = v_a_1047_;
                                            v___y_960_ = v_body_1044_;
                                            v___y_961_ = v___x_1054_;
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_1055_ = lean_ptr_addr(v_value_1043_);
                                            v___x_1056_ = lean_ptr_addr(v_a_1049_);
                                            v___x_1057_ =
                                                lean_usize_dec_eq(v___x_1055_, v___x_1056_);
                                            crate::leanh::lean_inc_ref(v_body_1044_);
                                            crate::leanh::lean_inc(v_declName_1041_);
                                            v___y_955_ = v_nondep_1045_;
                                            v___y_956_ = v_a_1049_;
                                            v___y_957_ = v_declName_1041_;
                                            v___y_958_ = v_a_1051_;
                                            v___y_959_ = v_a_1047_;
                                            v___y_960_ = v_body_1044_;
                                            v___y_961_ = v___x_1057_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_1049_);
                                        crate::leanh::lean_dec(v_a_1047_);
                                        crate::leanh::lean_dec_ref_known(v_e_925_, 4);
                                        return v___x_1050_;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1047_);
                                    crate::leanh::lean_dec_ref_known(v_e_925_, 4);
                                    crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                    return v___x_1048_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_925_, 4);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                return v___x_1046_;
                            }
                        }
                        5 => {
                            v_fn_1058_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_arg_1059_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            crate::leanh::lean_inc_ref(v_fn_1058_);
                            v___x_1060_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_fn_1058_, v_a_926_, v___x_1006_, v_a_928_);
                            if crate::leanh::lean_obj_tag(v___x_1060_) == 0 {
                                v_a_1061_ = crate::leanh::lean_ctor_get(v___x_1060_, 0);
                                crate::leanh::lean_inc(v_a_1061_);
                                crate::leanh::lean_dec_ref_known(v___x_1060_, 1);
                                crate::leanh::lean_inc_ref(v_arg_1059_);
                                v___x_1062_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_arg_1059_, v_a_926_, v___x_1006_, v_a_928_);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                if crate::leanh::lean_obj_tag(v___x_1062_) == 0 {
                                    v_a_1063_ = crate::leanh::lean_ctor_get(v___x_1062_, 0);
                                    crate::leanh::lean_inc(v_a_1063_);
                                    crate::leanh::lean_dec_ref_known(v___x_1062_, 1);
                                    v___x_1064_ = lean_ptr_addr(v_fn_1058_);
                                    v___x_1065_ = lean_ptr_addr(v_a_1061_);
                                    v___x_1066_ = lean_usize_dec_eq(v___x_1064_, v___x_1065_);
                                    if v___x_1066_ == 0 {
                                        v___y_971_ = v_a_1063_;
                                        v___y_972_ = v_a_1061_;
                                        v___y_973_ = v___x_1066_;
                                        state = 4;
                                        continue;
                                    } else {
                                        v___x_1067_ = lean_ptr_addr(v_arg_1059_);
                                        v___x_1068_ = lean_ptr_addr(v_a_1063_);
                                        v___x_1069_ = lean_usize_dec_eq(v___x_1067_, v___x_1068_);
                                        v___y_971_ = v_a_1063_;
                                        v___y_972_ = v_a_1061_;
                                        v___y_973_ = v___x_1069_;
                                        state = 4;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_1061_);
                                    crate::leanh::lean_dec_ref_known(v_e_925_, 2);
                                    return v___x_1062_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_925_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                                return v___x_1060_;
                            }
                        }
                        10 => {
                            v_data_1070_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_expr_1071_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            crate::leanh::lean_inc_ref(v_expr_1071_);
                            v___x_1072_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_expr_1071_, v_a_926_, v___x_1006_, v_a_928_);
                            crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                            if crate::leanh::lean_obj_tag(v___x_1072_) == 0 {
                                v_a_1073_ = crate::leanh::lean_ctor_get(v___x_1072_, 0);
                                crate::leanh::lean_inc(v_a_1073_);
                                crate::leanh::lean_dec_ref_known(v___x_1072_, 1);
                                v___x_1074_ = lean_ptr_addr(v_expr_1071_);
                                v___x_1075_ = lean_ptr_addr(v_a_1073_);
                                v___x_1076_ = lean_usize_dec_eq(v___x_1074_, v___x_1075_);
                                if v___x_1076_ == 0 {
                                    crate::leanh::lean_inc(v_data_1070_);
                                    v___x_1077_ =
                                        l_Lean_Expr_mdata___override(v_data_1070_, v_a_1073_);
                                    v___x_1078_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_1077_, v_a_926_);
                                    return v___x_1078_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1073_);
                                    crate::leanh::lean_inc_ref(v_e_925_);
                                    v___x_1079_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                                    return v___x_1079_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_925_, 2);
                                return v___x_1072_;
                            }
                        }
                        11 => {
                            v_typeName_1080_ = crate::leanh::lean_ctor_get(v_e_925_, 0);
                            v_idx_1081_ = crate::leanh::lean_ctor_get(v_e_925_, 1);
                            v_struct_1082_ = crate::leanh::lean_ctor_get(v_e_925_, 2);
                            crate::leanh::lean_inc_ref(v_struct_1082_);
                            v___x_1083_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(v_struct_1082_, v_a_926_, v___x_1006_, v_a_928_);
                            crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                            if crate::leanh::lean_obj_tag(v___x_1083_) == 0 {
                                v_a_1084_ = crate::leanh::lean_ctor_get(v___x_1083_, 0);
                                crate::leanh::lean_inc(v_a_1084_);
                                crate::leanh::lean_dec_ref_known(v___x_1083_, 1);
                                v___x_1085_ = lean_ptr_addr(v_struct_1082_);
                                v___x_1086_ = lean_ptr_addr(v_a_1084_);
                                v___x_1087_ = lean_usize_dec_eq(v___x_1085_, v___x_1086_);
                                if v___x_1087_ == 0 {
                                    crate::leanh::lean_inc(v_idx_1081_);
                                    crate::leanh::lean_inc(v_typeName_1080_);
                                    v___x_1088_ = l_Lean_Expr_proj___override(
                                        v_typeName_1080_,
                                        v_idx_1081_,
                                        v_a_1084_,
                                    );
                                    v___x_1089_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v___x_1088_, v_a_926_);
                                    return v___x_1089_;
                                } else {
                                    crate::leanh::lean_dec(v_a_1084_);
                                    crate::leanh::lean_inc_ref(v_e_925_);
                                    v___x_1090_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_cache___redArg(v_e_925_, v_e_925_, v_a_926_);
                                    return v___x_1090_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v_e_925_, 3);
                                return v___x_1083_;
                            }
                        }
                        _ => {
                            crate::leanh::lean_dec_ref_known(v___x_1006_, 14);
                            v___x_1091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1091_, 0, v_e_925_);
                            return v___x_1091_;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_999_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_998_, 0);
                    v___x_1001_ = v___x_998_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1002_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1002_, 0, v_val_996_);
                    v___x_1001_ = v_reuseFailAlloc_1002_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1001_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit___boxed(
    mut v_e_1096_: *mut crate::leanh::LeanObject,
    mut v_a_1097_: *mut crate::leanh::LeanObject,
    mut v_a_1098_: *mut crate::leanh::LeanObject,
    mut v_a_1099_: *mut crate::leanh::LeanObject,
    mut v_a_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1101_ = l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(
        v_e_1096_, v_a_1097_, v_a_1098_, v_a_1099_,
    );
    crate::leanh::lean_dec(v_a_1099_);
    crate::leanh::lean_dec_ref(v_a_1098_);
    crate::leanh::lean_dec(v_a_1097_);
    return v_res_1101_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(
    mut v_00_u03b2_1102_: *mut crate::leanh::LeanObject,
    mut v_m_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1105_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___redArg(v_m_1103_, v_a_1104_);
    return v___x_1105_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0___boxed(
    mut v_00_u03b2_1106_: *mut crate::leanh::LeanObject,
    mut v_m_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0(v_00_u03b2_1106_, v_m_1107_, v_a_1108_);
    crate::leanh::lean_dec_ref(v_a_1108_);
    crate::leanh::lean_dec_ref(v_m_1107_);
    return v_res_1109_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(
    mut v_00_u03b2_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
    mut v_x_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___redArg(v_a_1111_, v_x_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0___boxed(
    mut v_00_u03b2_1114_: *mut crate::leanh::LeanObject,
    mut v_a_1115_: *mut crate::leanh::LeanObject,
    mut v_x_1116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1117_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit_spec__0_spec__0(v_00_u03b2_1114_, v_a_1115_, v_x_1116_);
    crate::leanh::lean_dec(v_x_1116_);
    crate::leanh::lean_dec_ref(v_a_1115_);
    return v_res_1117_;
}
pub unsafe fn l_Lean_Meta_Sym_etaReduceWithCache(
    mut v_e_1118_: *mut crate::leanh::LeanObject,
    mut v_c_1119_: *mut crate::leanh::LeanObject,
    mut v_a_1120_: *mut crate::leanh::LeanObject,
    mut v_a_1121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1128_: u8 = 0;
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1134_: u8 = 0;
    let mut v_a_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1138_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1123_ = lean_st_mk_ref(v_c_1119_);
                v___x_1124_ =
                    l___private_Lean_Meta_Sym_Eta_0__Lean_Meta_Sym_etaReduceWithCache_visit(
                        v_e_1118_,
                        v___x_1123_,
                        v_a_1120_,
                        v_a_1121_,
                    );
                if crate::leanh::lean_obj_tag(v___x_1124_) == 0 {
                    v_a_1125_ = crate::leanh::lean_ctor_get(v___x_1124_, 0);
                    v_isSharedCheck_1134_ = (!crate::leanh::lean_is_exclusive(v___x_1124_)) as u8;
                    if v_isSharedCheck_1134_ == 0 {
                        v___x_1127_ = v___x_1124_;
                        v_isShared_1128_ = v_isSharedCheck_1134_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1125_);
                        crate::leanh::lean_dec(v___x_1124_);
                        v___x_1127_ = crate::leanh::lean_box(0);
                        v_isShared_1128_ = v_isSharedCheck_1134_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1123_);
                    v_a_1135_ = crate::leanh::lean_ctor_get(v___x_1124_, 0);
                    v_isSharedCheck_1142_ = (!crate::leanh::lean_is_exclusive(v___x_1124_)) as u8;
                    if v_isSharedCheck_1142_ == 0 {
                        v___x_1137_ = v___x_1124_;
                        v_isShared_1138_ = v_isSharedCheck_1142_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1135_);
                        crate::leanh::lean_dec(v___x_1124_);
                        v___x_1137_ = crate::leanh::lean_box(0);
                        v_isShared_1138_ = v_isSharedCheck_1142_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1129_ = lean_st_ref_get(v___x_1123_);
                crate::leanh::lean_dec(v___x_1123_);
                v___x_1130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1130_, 0, v_a_1125_);
                crate::leanh::lean_ctor_set(v___x_1130_, 1, v___x_1129_);
                if v_isShared_1128_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1130_);
                    v___x_1132_ = v___x_1127_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1133_, 0, v___x_1130_);
                    v___x_1132_ = v_reuseFailAlloc_1133_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1132_;
            }
            3 => {
                if v_isShared_1138_ == 0 {
                    v___x_1140_ = v___x_1137_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1141_, 0, v_a_1135_);
                    v___x_1140_ = v_reuseFailAlloc_1141_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_etaReduceWithCache___boxed(
    mut v_e_1143_: *mut crate::leanh::LeanObject,
    mut v_c_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1148_ = l_Lean_Meta_Sym_etaReduceWithCache(v_e_1143_, v_c_1144_, v_a_1145_, v_a_1146_);
    crate::leanh::lean_dec(v_a_1146_);
    crate::leanh::lean_dec_ref(v_a_1145_);
    return v_res_1148_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_etaReduceAll___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1150_ = crate::leanh::lean_box(0);
    v___x_1151_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1152_ = lean_mk_array(v___x_1151_, v___x_1150_);
    return v___x_1152_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_etaReduceAll___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_etaReduceAll___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_etaReduceAll___closed__1_once),
        _init_l_Lean_Meta_Sym_etaReduceAll___closed__1,
    );
    v___x_1154_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1155_, 0, v___x_1154_);
    crate::leanh::lean_ctor_set(v___x_1155_, 1, v___x_1153_);
    return v___x_1155_;
}
pub unsafe fn l_Lean_Meta_Sym_etaReduceAll(
    mut v_e_1156_: *mut crate::leanh::LeanObject,
    mut v_a_1157_: *mut crate::leanh::LeanObject,
    mut v_a_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1168_: u8 = 0;
    let mut v_fst_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1173_: u8 = 0;
    let mut v_a_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1177_: u8 = 0;
    let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1181_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1160_ = l_Lean_Meta_Sym_etaReduceAll___closed__0;
                v___x_1161_ = lean_find_expr(v___x_1160_, v_e_1156_);
                if crate::leanh::lean_obj_tag(v___x_1161_) == 0 {
                    v___x_1162_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1162_, 0, v_e_1156_);
                    return v___x_1162_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1161_, 1);
                    v___x_1163_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_etaReduceAll___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_etaReduceAll___closed__2_once),
                        _init_l_Lean_Meta_Sym_etaReduceAll___closed__2,
                    );
                    v___x_1164_ = l_Lean_Meta_Sym_etaReduceWithCache(
                        v_e_1156_,
                        v___x_1163_,
                        v_a_1157_,
                        v_a_1158_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1164_) == 0 {
                        v_a_1165_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                        v_isSharedCheck_1173_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                        if v_isSharedCheck_1173_ == 0 {
                            v___x_1167_ = v___x_1164_;
                            v_isShared_1168_ = v_isSharedCheck_1173_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1165_);
                            crate::leanh::lean_dec(v___x_1164_);
                            v___x_1167_ = crate::leanh::lean_box(0);
                            v_isShared_1168_ = v_isSharedCheck_1173_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1174_ = crate::leanh::lean_ctor_get(v___x_1164_, 0);
                        v_isSharedCheck_1181_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1164_)) as u8;
                        if v_isSharedCheck_1181_ == 0 {
                            v___x_1176_ = v___x_1164_;
                            v_isShared_1177_ = v_isSharedCheck_1181_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1174_);
                            crate::leanh::lean_dec(v___x_1164_);
                            v___x_1176_ = crate::leanh::lean_box(0);
                            v_isShared_1177_ = v_isSharedCheck_1181_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_1169_ = crate::leanh::lean_ctor_get(v_a_1165_, 0);
                crate::leanh::lean_inc(v_fst_1169_);
                crate::leanh::lean_dec(v_a_1165_);
                if v_isShared_1168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1167_, 0, v_fst_1169_);
                    v___x_1171_ = v___x_1167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_fst_1169_);
                    v___x_1171_ = v_reuseFailAlloc_1172_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1171_;
            }
            3 => {
                if v_isShared_1177_ == 0 {
                    v___x_1179_ = v___x_1176_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_a_1174_);
                    v___x_1179_ = v_reuseFailAlloc_1180_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1179_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_etaReduceAll___boxed(
    mut v_e_1182_: *mut crate::leanh::LeanObject,
    mut v_a_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ = l_Lean_Meta_Sym_etaReduceAll(v_e_1182_, v_a_1183_, v_a_1184_);
    crate::leanh::lean_dec(v_a_1184_);
    crate::leanh::lean_dec_ref(v_a_1183_);
    return v_res_1186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Eta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Eta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Eta(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_ExprPtr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Transform(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Eta(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Eta(builtin);
}

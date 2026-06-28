// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Reduce
// Imports: Lean.Meta.Sym.DSimp.DSimpM Lean.Meta.Sym.InstantiateS Lean.Meta.Sym.Util Lean.Meta.WHNF Lean.ProjFns
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux,
    l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_isApp, l_Lean_Expr_isHeadBetaTargetFn,
    l_Lean_Expr_sort___override, l_Lean_mkAppN,
};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_value_x3f;
use crate::r#gen::Lean::Meta::Basic::l_Lean_FVarId_getDecl___redArg;
use crate::r#gen::Lean::Meta::Sym::DSimp::DSimpM::{
    initialize_Lean_Meta_Sym_DSimp_DSimpM, runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM,
};
use crate::r#gen::Lean::Meta::Sym::InstantiateS::{
    initialize_Lean_Meta_Sym_InstantiateS, l_Lean_Meta_Sym_betaRevS___redArg,
    l_Lean_Meta_Sym_instantiateRevRangeS, runtime_initialize_Lean_Meta_Sym_InstantiateS,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_shareCommon___redArg, l_Lean_Meta_Sym_shareCommonInc___redArg,
};
use crate::r#gen::Lean::Meta::Sym::Util::{
    initialize_Lean_Meta_Sym_Util, l_Lean_Meta_Sym_foldProjs, runtime_initialize_Lean_Meta_Sym_Util,
};
use crate::r#gen::Lean::Meta::WHNF::{
    initialize_Lean_Meta_WHNF, l_Lean_Meta_reduceProj_x3f, l_Lean_Meta_reduceRecMatcher_x3f,
    l_Lean_Meta_unfoldDefinition_x3f, runtime_initialize_Lean_Meta_WHNF,
};
use crate::r#gen::Lean::ProjFns::{
    initialize_Lean_ProjFns, l_Lean_Environment_getProjectionFnInfo_x3f,
    runtime_initialize_Lean_ProjFns,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::lean_st_ref_get;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 0
                + 8) as u16,
            other: 0,
            tag: 0,
        },
        m_objs: [0 as *mut LeanObject],
    };
static mut l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_Meta_Sym_DSimp_beta___redArg(
    mut v_e_563_: *mut LeanObject,
    mut v_a_564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_566_: u8 = 0;
    let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: u8 = 0;
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_581_: u8 = 0;
    let mut v___x_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_586_: u8 = 0;
    let mut v_a_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_590_: u8 = 0;
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_566_ = l_Lean_Expr_isApp(v_e_563_);
                if v___x_566_ == 0 {
                    lean_dec_ref(v_e_563_);
                    v___x_567_ = lean_alloc_ctor(0, 0, (1) as u32);
                    lean_ctor_set_uint8(v___x_567_, 0 as u32, v___x_566_);
                    v___x_568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_568_, 0, v___x_567_);
                    return v___x_568_;
                } else {
                    v_f_569_ = l_Lean_Expr_getAppFn(v_e_563_);
                    v___x_570_ = 0;
                    v___x_571_ = l_Lean_Expr_isHeadBetaTargetFn(v___x_570_, v_f_569_);
                    if v___x_571_ == 0 {
                        lean_dec_ref(v_f_569_);
                        lean_dec_ref(v_e_563_);
                        v___x_572_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                        v___x_573_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_573_, 0, v___x_572_);
                        return v___x_573_;
                    } else {
                        v___x_574_ = l_Lean_Expr_getAppNumArgs(v_e_563_);
                        v___x_575_ = lean_mk_empty_array_with_capacity(v___x_574_);
                        lean_dec(v___x_574_);
                        v___x_576_ = l___private_Lean_Expr_0__Lean_Expr_getAppRevArgsAux(
                            v_e_563_, v___x_575_,
                        );
                        v___x_577_ =
                            l_Lean_Meta_Sym_betaRevS___redArg(v_f_569_, v___x_576_, v_a_564_);
                        lean_dec_ref(v___x_576_);
                        if lean_obj_tag(v___x_577_) == 0 {
                            v_a_578_ = lean_ctor_get(v___x_577_, 0);
                            v_isSharedCheck_586_ = (!lean_is_exclusive(v___x_577_)) as u8;
                            if v_isSharedCheck_586_ == 0 {
                                v___x_580_ = v___x_577_;
                                v_isShared_581_ = v_isSharedCheck_586_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_578_);
                                lean_dec(v___x_577_);
                                v___x_580_ = lean_box(0);
                                v_isShared_581_ = v_isSharedCheck_586_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_587_ = lean_ctor_get(v___x_577_, 0);
                            v_isSharedCheck_594_ = (!lean_is_exclusive(v___x_577_)) as u8;
                            if v_isSharedCheck_594_ == 0 {
                                v___x_589_ = v___x_577_;
                                v_isShared_590_ = v_isSharedCheck_594_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_587_);
                                lean_dec(v___x_577_);
                                v___x_589_ = lean_box(0);
                                v_isShared_590_ = v_isSharedCheck_594_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_582_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_582_, 0, v_a_578_);
                lean_ctor_set_uint8(
                    v___x_582_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_570_,
                );
                if v_isShared_581_ == 0 {
                    lean_ctor_set(v___x_580_, 0, v___x_582_);
                    v___x_584_ = v___x_580_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_585_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_585_, 0, v___x_582_);
                    v___x_584_ = v_reuseFailAlloc_585_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_584_;
            }
            3 => {
                if v_isShared_590_ == 0 {
                    v___x_592_ = v___x_589_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_593_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_593_, 0, v_a_587_);
                    v___x_592_ = v_reuseFailAlloc_593_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_beta___redArg___boxed(
    mut v_e_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_598_: *mut LeanObject = core::ptr::null_mut();
    v_res_598_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_595_, v_a_596_);
    lean_dec(v_a_596_);
    return v_res_598_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_beta(
    mut v_e_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
    mut v_a_602_: *mut LeanObject,
    mut v_a_603_: *mut LeanObject,
    mut v_a_604_: *mut LeanObject,
    mut v_a_605_: *mut LeanObject,
    mut v_a_606_: *mut LeanObject,
    mut v_a_607_: *mut LeanObject,
    mut v_a_608_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_610_: *mut LeanObject = core::ptr::null_mut();
    v___x_610_ = l_Lean_Meta_Sym_DSimp_beta___redArg(v_e_599_, v_a_604_);
    return v___x_610_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_beta___boxed(
    mut v_e_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v_a_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
    mut v_a_621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_622_: *mut LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lean_Meta_Sym_DSimp_beta(
        v_e_611_, v_a_612_, v_a_613_, v_a_614_, v_a_615_, v_a_616_, v_a_617_, v_a_618_, v_a_619_,
        v_a_620_,
    );
    lean_dec(v_a_620_);
    lean_dec_ref(v_a_619_);
    lean_dec(v_a_618_);
    lean_dec_ref(v_a_617_);
    lean_dec(v_a_616_);
    lean_dec_ref(v_a_615_);
    lean_dec(v_a_614_);
    lean_dec(v_a_613_);
    lean_dec(v_a_612_);
    return v_res_622_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(
    mut v_k_623_: *mut LeanObject,
    mut v_t_624_: *mut LeanObject,
) -> u8 {
    let mut v_k_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: u8 = 0;
    let mut v___x_630_: u8 = 0;
    let mut v___x_632_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_624_) == 0 {
                    v_k_625_ = lean_ctor_get(v_t_624_, 1);
                    v_l_626_ = lean_ctor_get(v_t_624_, 3);
                    v_r_627_ = lean_ctor_get(v_t_624_, 4);
                    v___x_628_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_623_, v_k_625_);
                    match v___x_628_ {
                        0 => {
                            v_t_624_ = v_l_626_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_630_ = 1;
                            return v___x_630_;
                        }
                        _ => {
                            v_t_624_ = v_r_627_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_632_ = 0;
                    return v___x_632_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg___boxed(
    mut v_k_633_: *mut LeanObject,
    mut v_t_634_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_635_: u8 = 0;
    let mut v_r_636_: *mut LeanObject = core::ptr::null_mut();
    v_res_635_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_633_, v_t_634_);
    lean_dec(v_t_634_);
    lean_dec(v_k_633_);
    v_r_636_ = lean_box((v_res_635_) as usize);
    return v_r_636_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(
    mut v_s_637_: *mut LeanObject,
    mut v_e_638_: *mut LeanObject,
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
    mut v_a_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: u8 = 0;
    let mut v___x_645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_652_: u8 = 0;
    let mut v___x_653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_663_: u8 = 0;
    let mut v_a_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_638_) == 1 {
                    v_fvarId_643_ = lean_ctor_get(v_e_638_, 0);
                    lean_inc(v_fvarId_643_);
                    lean_dec_ref_known(v_e_638_, 1);
                    v___x_644_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_fvarId_643_, v_s_637_);
                    if v___x_644_ == 0 {
                        lean_dec(v_fvarId_643_);
                        v___x_645_ = lean_alloc_ctor(0, 0, (1) as u32);
                        lean_ctor_set_uint8(v___x_645_, 0 as u32, v___x_644_);
                        v___x_646_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_646_, 0, v___x_645_);
                        return v___x_646_;
                    } else {
                        v___x_647_ = l_Lean_FVarId_getDecl___redArg(
                            v_fvarId_643_,
                            v_a_639_,
                            v_a_640_,
                            v_a_641_,
                        );
                        if lean_obj_tag(v___x_647_) == 0 {
                            v_a_648_ = lean_ctor_get(v___x_647_, 0);
                            v_isSharedCheck_663_ = (!lean_is_exclusive(v___x_647_)) as u8;
                            if v_isSharedCheck_663_ == 0 {
                                v___x_650_ = v___x_647_;
                                v_isShared_651_ = v_isSharedCheck_663_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_648_);
                                lean_dec(v___x_647_);
                                v___x_650_ = lean_box(0);
                                v_isShared_651_ = v_isSharedCheck_663_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_664_ = lean_ctor_get(v___x_647_, 0);
                            v_isSharedCheck_671_ = (!lean_is_exclusive(v___x_647_)) as u8;
                            if v_isSharedCheck_671_ == 0 {
                                v___x_666_ = v___x_647_;
                                v_isShared_667_ = v_isSharedCheck_671_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_664_);
                                lean_dec(v___x_647_);
                                v___x_666_ = lean_box(0);
                                v_isShared_667_ = v_isSharedCheck_671_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_e_638_);
                    v___x_672_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    v___x_673_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_673_, 0, v___x_672_);
                    return v___x_673_;
                }
            }
            1 => {
                v___x_652_ = 0;
                v___x_653_ = l_Lean_LocalDecl_value_x3f(v_a_648_, v___x_652_);
                lean_dec(v_a_648_);
                if lean_obj_tag(v___x_653_) == 1 {
                    v_val_654_ = lean_ctor_get(v___x_653_, 0);
                    lean_inc(v_val_654_);
                    lean_dec_ref_known(v___x_653_, 1);
                    v___x_655_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v___x_655_, 0, v_val_654_);
                    lean_ctor_set_uint8(
                        v___x_655_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_652_,
                    );
                    if v_isShared_651_ == 0 {
                        lean_ctor_set(v___x_650_, 0, v___x_655_);
                        v___x_657_ = v___x_650_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_658_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_658_, 0, v___x_655_);
                        v___x_657_ = v_reuseFailAlloc_658_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_653_);
                    v___x_659_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    if v_isShared_651_ == 0 {
                        lean_ctor_set(v___x_650_, 0, v___x_659_);
                        v___x_661_ = v___x_650_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_662_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_662_, 0, v___x_659_);
                        v___x_661_ = v_reuseFailAlloc_662_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_657_;
            }
            3 => {
                return v___x_661_;
            }
            4 => {
                if v_isShared_667_ == 0 {
                    v___x_669_ = v___x_666_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_670_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_670_, 0, v_a_664_);
                    v___x_669_ = v_reuseFailAlloc_670_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDelta___redArg___boxed(
    mut v_s_674_: *mut LeanObject,
    mut v_e_675_: *mut LeanObject,
    mut v_a_676_: *mut LeanObject,
    mut v_a_677_: *mut LeanObject,
    mut v_a_678_: *mut LeanObject,
    mut v_a_679_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_680_: *mut LeanObject = core::ptr::null_mut();
    v_res_680_ =
        l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_674_, v_e_675_, v_a_676_, v_a_677_, v_a_678_);
    lean_dec(v_a_678_);
    lean_dec_ref(v_a_677_);
    lean_dec_ref(v_a_676_);
    lean_dec(v_s_674_);
    return v_res_680_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDelta(
    mut v_s_681_: *mut LeanObject,
    mut v_e_682_: *mut LeanObject,
    mut v_a_683_: *mut LeanObject,
    mut v_a_684_: *mut LeanObject,
    mut v_a_685_: *mut LeanObject,
    mut v_a_686_: *mut LeanObject,
    mut v_a_687_: *mut LeanObject,
    mut v_a_688_: *mut LeanObject,
    mut v_a_689_: *mut LeanObject,
    mut v_a_690_: *mut LeanObject,
    mut v_a_691_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    v___x_693_ =
        l_Lean_Meta_Sym_DSimp_zetaDelta___redArg(v_s_681_, v_e_682_, v_a_688_, v_a_690_, v_a_691_);
    return v___x_693_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDelta___boxed(
    mut v_s_694_: *mut LeanObject,
    mut v_e_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
    mut v_a_697_: *mut LeanObject,
    mut v_a_698_: *mut LeanObject,
    mut v_a_699_: *mut LeanObject,
    mut v_a_700_: *mut LeanObject,
    mut v_a_701_: *mut LeanObject,
    mut v_a_702_: *mut LeanObject,
    mut v_a_703_: *mut LeanObject,
    mut v_a_704_: *mut LeanObject,
    mut v_a_705_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_706_: *mut LeanObject = core::ptr::null_mut();
    v_res_706_ = l_Lean_Meta_Sym_DSimp_zetaDelta(
        v_s_694_, v_e_695_, v_a_696_, v_a_697_, v_a_698_, v_a_699_, v_a_700_, v_a_701_, v_a_702_,
        v_a_703_, v_a_704_,
    );
    lean_dec(v_a_704_);
    lean_dec_ref(v_a_703_);
    lean_dec(v_a_702_);
    lean_dec_ref(v_a_701_);
    lean_dec(v_a_700_);
    lean_dec_ref(v_a_699_);
    lean_dec(v_a_698_);
    lean_dec(v_a_697_);
    lean_dec(v_a_696_);
    lean_dec(v_s_694_);
    return v_res_706_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(
    mut v_00_u03b2_707_: *mut LeanObject,
    mut v_k_708_: *mut LeanObject,
    mut v_t_709_: *mut LeanObject,
) -> u8 {
    let mut v___x_710_: u8 = 0;
    v___x_710_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___redArg(v_k_708_, v_t_709_);
    return v___x_710_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0___boxed(
    mut v_00_u03b2_711_: *mut LeanObject,
    mut v_k_712_: *mut LeanObject,
    mut v_t_713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_714_: u8 = 0;
    let mut v_r_715_: *mut LeanObject = core::ptr::null_mut();
    v_res_714_ =
        l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_Sym_DSimp_zetaDelta_spec__0(
            v_00_u03b2_711_,
            v_k_712_,
            v_t_713_,
        );
    lean_dec(v_t_713_);
    lean_dec(v_k_712_);
    v_r_715_ = lean_box((v_res_714_) as usize);
    return v_r_715_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(
    mut v_e_716_: *mut LeanObject,
    mut v_a_717_: *mut LeanObject,
    mut v_a_718_: *mut LeanObject,
    mut v_a_719_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_726_: u8 = 0;
    let mut v___x_727_: u8 = 0;
    let mut v___x_728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut v_a_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_742_: u8 = 0;
    let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_746_: u8 = 0;
    let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_716_) == 1 {
                    v_fvarId_721_ = lean_ctor_get(v_e_716_, 0);
                    lean_inc(v_fvarId_721_);
                    lean_dec_ref_known(v_e_716_, 1);
                    v___x_722_ =
                        l_Lean_FVarId_getDecl___redArg(v_fvarId_721_, v_a_717_, v_a_718_, v_a_719_);
                    if lean_obj_tag(v___x_722_) == 0 {
                        v_a_723_ = lean_ctor_get(v___x_722_, 0);
                        v_isSharedCheck_738_ = (!lean_is_exclusive(v___x_722_)) as u8;
                        if v_isSharedCheck_738_ == 0 {
                            v___x_725_ = v___x_722_;
                            v_isShared_726_ = v_isSharedCheck_738_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_723_);
                            lean_dec(v___x_722_);
                            v___x_725_ = lean_box(0);
                            v_isShared_726_ = v_isSharedCheck_738_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_739_ = lean_ctor_get(v___x_722_, 0);
                        v_isSharedCheck_746_ = (!lean_is_exclusive(v___x_722_)) as u8;
                        if v_isSharedCheck_746_ == 0 {
                            v___x_741_ = v___x_722_;
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_739_);
                            lean_dec(v___x_722_);
                            v___x_741_ = lean_box(0);
                            v_isShared_742_ = v_isSharedCheck_746_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_716_);
                    v___x_747_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    v___x_748_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_748_, 0, v___x_747_);
                    return v___x_748_;
                }
            }
            1 => {
                v___x_727_ = 0;
                v___x_728_ = l_Lean_LocalDecl_value_x3f(v_a_723_, v___x_727_);
                lean_dec(v_a_723_);
                if lean_obj_tag(v___x_728_) == 1 {
                    v_val_729_ = lean_ctor_get(v___x_728_, 0);
                    lean_inc(v_val_729_);
                    lean_dec_ref_known(v___x_728_, 1);
                    v___x_730_ = lean_alloc_ctor(1, 1, (1) as u32);
                    lean_ctor_set(v___x_730_, 0, v_val_729_);
                    lean_ctor_set_uint8(
                        v___x_730_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_727_,
                    );
                    if v_isShared_726_ == 0 {
                        lean_ctor_set(v___x_725_, 0, v___x_730_);
                        v___x_732_ = v___x_725_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
                        v___x_732_ = v_reuseFailAlloc_733_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_728_);
                    v___x_734_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    if v_isShared_726_ == 0 {
                        lean_ctor_set(v___x_725_, 0, v___x_734_);
                        v___x_736_ = v___x_725_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_737_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_737_, 0, v___x_734_);
                        v___x_736_ = v_reuseFailAlloc_737_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_732_;
            }
            3 => {
                return v___x_736_;
            }
            4 => {
                if v_isShared_742_ == 0 {
                    v___x_744_ = v___x_741_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_745_, 0, v_a_739_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_744_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg___boxed(
    mut v_e_749_: *mut LeanObject,
    mut v_a_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
    mut v_a_752_: *mut LeanObject,
    mut v_a_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_754_: *mut LeanObject = core::ptr::null_mut();
    v_res_754_ =
        l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_749_, v_a_750_, v_a_751_, v_a_752_);
    lean_dec(v_a_752_);
    lean_dec_ref(v_a_751_);
    lean_dec_ref(v_a_750_);
    return v_res_754_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDeltaAll(
    mut v_e_755_: *mut LeanObject,
    mut v_a_756_: *mut LeanObject,
    mut v_a_757_: *mut LeanObject,
    mut v_a_758_: *mut LeanObject,
    mut v_a_759_: *mut LeanObject,
    mut v_a_760_: *mut LeanObject,
    mut v_a_761_: *mut LeanObject,
    mut v_a_762_: *mut LeanObject,
    mut v_a_763_: *mut LeanObject,
    mut v_a_764_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    v___x_766_ =
        l_Lean_Meta_Sym_DSimp_zetaDeltaAll___redArg(v_e_755_, v_a_761_, v_a_763_, v_a_764_);
    return v___x_766_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zetaDeltaAll___boxed(
    mut v_e_767_: *mut LeanObject,
    mut v_a_768_: *mut LeanObject,
    mut v_a_769_: *mut LeanObject,
    mut v_a_770_: *mut LeanObject,
    mut v_a_771_: *mut LeanObject,
    mut v_a_772_: *mut LeanObject,
    mut v_a_773_: *mut LeanObject,
    mut v_a_774_: *mut LeanObject,
    mut v_a_775_: *mut LeanObject,
    mut v_a_776_: *mut LeanObject,
    mut v_a_777_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v_res_778_ = l_Lean_Meta_Sym_DSimp_zetaDeltaAll(
        v_e_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_,
        v_a_776_,
    );
    lean_dec(v_a_776_);
    lean_dec_ref(v_a_775_);
    lean_dec(v_a_774_);
    lean_dec_ref(v_a_773_);
    lean_dec(v_a_772_);
    lean_dec_ref(v_a_771_);
    lean_dec(v_a_770_);
    lean_dec(v_a_769_);
    lean_dec(v_a_768_);
    return v_res_778_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(
    mut v_e_779_: *mut LeanObject,
    mut v_subst_780_: *mut LeanObject,
    mut v_a_781_: *mut LeanObject,
    mut v_a_782_: *mut LeanObject,
    mut v_a_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_a_785_: *mut LeanObject,
    mut v_a_786_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_value_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_body_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_799_: u8 = 0;
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_803_: u8 = 0;
    let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_810_: u8 = 0;
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_816_: u8 = 0;
    let mut v_a_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_820_: u8 = 0;
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_824_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_779_) == 8 {
                    v_value_788_ = lean_ctor_get(v_e_779_, 2);
                    lean_inc_ref(v_value_788_);
                    v_body_789_ = lean_ctor_get(v_e_779_, 3);
                    lean_inc_ref(v_body_789_);
                    lean_dec_ref_known(v_e_779_, 4);
                    v___x_790_ = lean_unsigned_to_nat(0);
                    v___x_791_ = lean_array_get_size(v_subst_780_);
                    v___x_792_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                        v_value_788_,
                        v___x_790_,
                        v___x_791_,
                        v_subst_780_,
                        v_a_781_,
                        v_a_782_,
                        v_a_783_,
                        v_a_784_,
                        v_a_785_,
                        v_a_786_,
                    );
                    if lean_obj_tag(v___x_792_) == 0 {
                        v_a_793_ = lean_ctor_get(v___x_792_, 0);
                        lean_inc(v_a_793_);
                        lean_dec_ref_known(v___x_792_, 1);
                        v___x_794_ = lean_array_push(v_subst_780_, v_a_793_);
                        v_e_779_ = v_body_789_;
                        v_subst_780_ = v___x_794_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_body_789_);
                        lean_dec_ref(v_subst_780_);
                        v_a_796_ = lean_ctor_get(v___x_792_, 0);
                        v_isSharedCheck_803_ = (!lean_is_exclusive(v___x_792_)) as u8;
                        if v_isSharedCheck_803_ == 0 {
                            v___x_798_ = v___x_792_;
                            v_isShared_799_ = v_isSharedCheck_803_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_796_);
                            lean_dec(v___x_792_);
                            v___x_798_ = lean_box(0);
                            v_isShared_799_ = v_isSharedCheck_803_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_804_ = lean_unsigned_to_nat(0);
                    v___x_805_ = lean_array_get_size(v_subst_780_);
                    v___x_806_ = l_Lean_Meta_Sym_instantiateRevRangeS(
                        v_e_779_,
                        v___x_804_,
                        v___x_805_,
                        v_subst_780_,
                        v_a_781_,
                        v_a_782_,
                        v_a_783_,
                        v_a_784_,
                        v_a_785_,
                        v_a_786_,
                    );
                    lean_dec_ref(v_subst_780_);
                    if lean_obj_tag(v___x_806_) == 0 {
                        v_a_807_ = lean_ctor_get(v___x_806_, 0);
                        v_isSharedCheck_816_ = (!lean_is_exclusive(v___x_806_)) as u8;
                        if v_isSharedCheck_816_ == 0 {
                            v___x_809_ = v___x_806_;
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_807_);
                            lean_dec(v___x_806_);
                            v___x_809_ = lean_box(0);
                            v_isShared_810_ = v_isSharedCheck_816_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_817_ = lean_ctor_get(v___x_806_, 0);
                        v_isSharedCheck_824_ = (!lean_is_exclusive(v___x_806_)) as u8;
                        if v_isSharedCheck_824_ == 0 {
                            v___x_819_ = v___x_806_;
                            v_isShared_820_ = v_isSharedCheck_824_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_817_);
                            lean_dec(v___x_806_);
                            v___x_819_ = lean_box(0);
                            v_isShared_820_ = v_isSharedCheck_824_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_799_ == 0 {
                    v___x_801_ = v___x_798_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_802_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_802_, 0, v_a_796_);
                    v___x_801_ = v_reuseFailAlloc_802_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_801_;
            }
            3 => {
                v___x_811_ = 0;
                v___x_812_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_812_, 0, v_a_807_);
                lean_ctor_set_uint8(
                    v___x_812_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_811_,
                );
                if v_isShared_810_ == 0 {
                    lean_ctor_set(v___x_809_, 0, v___x_812_);
                    v___x_814_ = v___x_809_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_815_, 0, v___x_812_);
                    v___x_814_ = v_reuseFailAlloc_815_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_814_;
            }
            5 => {
                if v_isShared_820_ == 0 {
                    v___x_822_ = v___x_819_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_823_, 0, v_a_817_);
                    v___x_822_ = v_reuseFailAlloc_823_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_822_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg___boxed(
    mut v_e_825_: *mut LeanObject,
    mut v_subst_826_: *mut LeanObject,
    mut v_a_827_: *mut LeanObject,
    mut v_a_828_: *mut LeanObject,
    mut v_a_829_: *mut LeanObject,
    mut v_a_830_: *mut LeanObject,
    mut v_a_831_: *mut LeanObject,
    mut v_a_832_: *mut LeanObject,
    mut v_a_833_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_834_: *mut LeanObject = core::ptr::null_mut();
    v_res_834_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(
        v_e_825_,
        v_subst_826_,
        v_a_827_,
        v_a_828_,
        v_a_829_,
        v_a_830_,
        v_a_831_,
        v_a_832_,
    );
    lean_dec(v_a_832_);
    lean_dec_ref(v_a_831_);
    lean_dec(v_a_830_);
    lean_dec_ref(v_a_829_);
    lean_dec(v_a_828_);
    lean_dec_ref(v_a_827_);
    return v_res_834_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go(
    mut v_e_835_: *mut LeanObject,
    mut v_subst_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
    mut v_a_838_: *mut LeanObject,
    mut v_a_839_: *mut LeanObject,
    mut v_a_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    v___x_847_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(
        v_e_835_,
        v_subst_836_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
    );
    return v___x_847_;
}
pub unsafe fn l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___boxed(
    mut v_e_848_: *mut LeanObject,
    mut v_subst_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
    mut v_a_851_: *mut LeanObject,
    mut v_a_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
    mut v_a_854_: *mut LeanObject,
    mut v_a_855_: *mut LeanObject,
    mut v_a_856_: *mut LeanObject,
    mut v_a_857_: *mut LeanObject,
    mut v_a_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_860_: *mut LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go(
        v_e_848_,
        v_subst_849_,
        v_a_850_,
        v_a_851_,
        v_a_852_,
        v_a_853_,
        v_a_854_,
        v_a_855_,
        v_a_856_,
        v_a_857_,
        v_a_858_,
    );
    lean_dec(v_a_858_);
    lean_dec_ref(v_a_857_);
    lean_dec(v_a_856_);
    lean_dec_ref(v_a_855_);
    lean_dec(v_a_854_);
    lean_dec_ref(v_a_853_);
    lean_dec(v_a_852_);
    lean_dec(v_a_851_);
    lean_dec(v_a_850_);
    return v_res_860_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zeta___redArg(
    mut v_e_863_: *mut LeanObject,
    mut v_a_864_: *mut LeanObject,
    mut v_a_865_: *mut LeanObject,
    mut v_a_866_: *mut LeanObject,
    mut v_a_867_: *mut LeanObject,
    mut v_a_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_e_863_) == 8 {
        let mut v___x_871_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
        v___x_871_ = l_Lean_Meta_Sym_DSimp_zeta___redArg___closed__0;
        v___x_872_ = l___private_Lean_Meta_Sym_DSimp_Reduce_0__Lean_Meta_Sym_DSimp_zeta_go___redArg(
            v_e_863_, v___x_871_, v_a_864_, v_a_865_, v_a_866_, v_a_867_, v_a_868_, v_a_869_,
        );
        return v___x_872_;
    } else {
        let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_e_863_);
        v___x_873_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
        v___x_874_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_874_, 0, v___x_873_);
        return v___x_874_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zeta___redArg___boxed(
    mut v_e_875_: *mut LeanObject,
    mut v_a_876_: *mut LeanObject,
    mut v_a_877_: *mut LeanObject,
    mut v_a_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(
        v_e_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_,
    );
    lean_dec(v_a_881_);
    lean_dec_ref(v_a_880_);
    lean_dec(v_a_879_);
    lean_dec_ref(v_a_878_);
    lean_dec(v_a_877_);
    lean_dec_ref(v_a_876_);
    return v_res_883_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zeta(
    mut v_e_884_: *mut LeanObject,
    mut v_a_885_: *mut LeanObject,
    mut v_a_886_: *mut LeanObject,
    mut v_a_887_: *mut LeanObject,
    mut v_a_888_: *mut LeanObject,
    mut v_a_889_: *mut LeanObject,
    mut v_a_890_: *mut LeanObject,
    mut v_a_891_: *mut LeanObject,
    mut v_a_892_: *mut LeanObject,
    mut v_a_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_895_: *mut LeanObject = core::ptr::null_mut();
    v___x_895_ = l_Lean_Meta_Sym_DSimp_zeta___redArg(
        v_e_884_, v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_,
    );
    return v___x_895_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_zeta___boxed(
    mut v_e_896_: *mut LeanObject,
    mut v_a_897_: *mut LeanObject,
    mut v_a_898_: *mut LeanObject,
    mut v_a_899_: *mut LeanObject,
    mut v_a_900_: *mut LeanObject,
    mut v_a_901_: *mut LeanObject,
    mut v_a_902_: *mut LeanObject,
    mut v_a_903_: *mut LeanObject,
    mut v_a_904_: *mut LeanObject,
    mut v_a_905_: *mut LeanObject,
    mut v_a_906_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_907_: *mut LeanObject = core::ptr::null_mut();
    v_res_907_ = l_Lean_Meta_Sym_DSimp_zeta(
        v_e_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_,
        v_a_905_,
    );
    lean_dec(v_a_905_);
    lean_dec_ref(v_a_904_);
    lean_dec(v_a_903_);
    lean_dec_ref(v_a_902_);
    lean_dec(v_a_901_);
    lean_dec_ref(v_a_900_);
    lean_dec(v_a_899_);
    lean_dec(v_a_898_);
    lean_dec(v_a_897_);
    return v_res_907_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(
    mut v_declName_908_: *mut LeanObject,
    mut v___y_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_911_ = lean_st_ref_get(v___y_909_);
    v_env_912_ = lean_ctor_get(v___x_911_, 0);
    lean_inc_ref(v_env_912_);
    lean_dec(v___x_911_);
    v___x_913_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_912_, v_declName_908_);
    v___x_914_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_914_, 0, v___x_913_);
    return v___x_914_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg___boxed(
    mut v_declName_915_: *mut LeanObject,
    mut v___y_916_: *mut LeanObject,
    mut v___y_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_918_: *mut LeanObject = core::ptr::null_mut();
    v_res_918_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(
            v_declName_915_,
            v___y_916_,
        );
    lean_dec(v___y_916_);
    return v_res_918_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(
    mut v_declName_919_: *mut LeanObject,
    mut v___y_920_: *mut LeanObject,
    mut v___y_921_: *mut LeanObject,
    mut v___y_922_: *mut LeanObject,
    mut v___y_923_: *mut LeanObject,
    mut v___y_924_: *mut LeanObject,
    mut v___y_925_: *mut LeanObject,
    mut v___y_926_: *mut LeanObject,
    mut v___y_927_: *mut LeanObject,
    mut v___y_928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_930_: *mut LeanObject = core::ptr::null_mut();
    v___x_930_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(
            v_declName_919_,
            v___y_928_,
        );
    return v___x_930_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___boxed(
    mut v_declName_931_: *mut LeanObject,
    mut v___y_932_: *mut LeanObject,
    mut v___y_933_: *mut LeanObject,
    mut v___y_934_: *mut LeanObject,
    mut v___y_935_: *mut LeanObject,
    mut v___y_936_: *mut LeanObject,
    mut v___y_937_: *mut LeanObject,
    mut v___y_938_: *mut LeanObject,
    mut v___y_939_: *mut LeanObject,
    mut v___y_940_: *mut LeanObject,
    mut v___y_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_942_: *mut LeanObject = core::ptr::null_mut();
    v_res_942_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0(
        v_declName_931_,
        v___y_932_,
        v___y_933_,
        v___y_934_,
        v___y_935_,
        v___y_936_,
        v___y_937_,
        v___y_938_,
        v___y_939_,
        v___y_940_,
    );
    lean_dec(v___y_940_);
    lean_dec_ref(v___y_939_);
    lean_dec(v___y_938_);
    lean_dec_ref(v___y_937_);
    lean_dec(v___y_936_);
    lean_dec_ref(v___y_935_);
    lean_dec(v___y_934_);
    lean_dec(v___y_933_);
    lean_dec(v___y_932_);
    return v_res_942_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0() -> *mut LeanObject {
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_944_: *mut LeanObject = core::ptr::null_mut();
    v___x_943_ = lean_box(0);
    v_dummy_944_ = l_Lean_Expr_sort___override(v___x_943_);
    return v_dummy_944_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpProj(
    mut v_e_945_: *mut LeanObject,
    mut v_a_946_: *mut LeanObject,
    mut v_a_947_: *mut LeanObject,
    mut v_a_948_: *mut LeanObject,
    mut v_a_949_: *mut LeanObject,
    mut v_a_950_: *mut LeanObject,
    mut v_a_951_: *mut LeanObject,
    mut v_a_952_: *mut LeanObject,
    mut v_a_953_: *mut LeanObject,
    mut v_a_954_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_f_959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_965_: u8 = 0;
    let mut v___x_966_: u8 = 0;
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dummy_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nargs_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_985_: u8 = 0;
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_990_: u8 = 0;
    let mut v_a_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_994_: u8 = 0;
    let mut v___x_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_998_: u8 = 0;
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1002_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1006_: u8 = 0;
    let mut v_a_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1010_: u8 = 0;
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1014_: u8 = 0;
    let mut v___x_1015_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1019_: u8 = 0;
    let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_f_959_ = l_Lean_Expr_getAppFn(v_e_945_);
                if lean_obj_tag(v_f_959_) == 4 {
                    v_declName_960_ = lean_ctor_get(v_f_959_, 0);
                    lean_inc(v_declName_960_);
                    lean_dec_ref_known(v_f_959_, 2);
                    v___x_961_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Sym_DSimp_dsimpProj_spec__0___redArg(v_declName_960_, v_a_954_);
                    v_a_962_ = lean_ctor_get(v___x_961_, 0);
                    v_isSharedCheck_1019_ = (!lean_is_exclusive(v___x_961_)) as u8;
                    if v_isSharedCheck_1019_ == 0 {
                        v___x_964_ = v___x_961_;
                        v_isShared_965_ = v_isSharedCheck_1019_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_962_);
                        lean_dec(v___x_961_);
                        v___x_964_ = lean_box(0);
                        v_isShared_965_ = v_isSharedCheck_1019_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_959_);
                    lean_dec_ref(v_e_945_);
                    v___x_1020_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    v___x_1021_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1021_, 0, v___x_1020_);
                    return v___x_1021_;
                }
            }
            1 => {
                v___x_957_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                v___x_958_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_958_, 0, v___x_957_);
                return v___x_958_;
            }
            2 => {
                if lean_obj_tag(v_a_962_) == 1 {
                    lean_dec_ref_known(v_a_962_, 1);
                    lean_del_object(v___x_964_);
                    v___x_966_ = 0;
                    v___x_967_ = l_Lean_Meta_unfoldDefinition_x3f(
                        v_e_945_, v___x_966_, v_a_951_, v_a_952_, v_a_953_, v_a_954_,
                    );
                    if lean_obj_tag(v___x_967_) == 0 {
                        v_a_968_ = lean_ctor_get(v___x_967_, 0);
                        lean_inc(v_a_968_);
                        lean_dec_ref_known(v___x_967_, 1);
                        if lean_obj_tag(v_a_968_) == 0 {
                            state = 1;
                            continue;
                        } else {
                            v_val_969_ = lean_ctor_get(v_a_968_, 0);
                            lean_inc(v_val_969_);
                            lean_dec_ref_known(v_a_968_, 1);
                            v___x_970_ = l_Lean_Expr_getAppFn(v_val_969_);
                            v___x_971_ = l_Lean_Meta_reduceProj_x3f(
                                v___x_970_, v_a_951_, v_a_952_, v_a_953_, v_a_954_,
                            );
                            if lean_obj_tag(v___x_971_) == 0 {
                                v_a_972_ = lean_ctor_get(v___x_971_, 0);
                                lean_inc(v_a_972_);
                                lean_dec_ref_known(v___x_971_, 1);
                                if lean_obj_tag(v_a_972_) == 0 {
                                    lean_dec(v_val_969_);
                                    state = 1;
                                    continue;
                                } else {
                                    v_val_973_ = lean_ctor_get(v_a_972_, 0);
                                    lean_inc(v_val_973_);
                                    lean_dec_ref_known(v_a_972_, 1);
                                    v_dummy_974_ = lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0_once
                                        ),
                                        _init_l_Lean_Meta_Sym_DSimp_dsimpProj___closed__0,
                                    );
                                    v_nargs_975_ = l_Lean_Expr_getAppNumArgs(v_val_969_);
                                    lean_inc(v_nargs_975_);
                                    v___x_976_ = lean_mk_array(v_nargs_975_, v_dummy_974_);
                                    v___x_977_ = lean_unsigned_to_nat(1);
                                    v___x_978_ = lean_nat_sub(v_nargs_975_, v___x_977_);
                                    lean_dec(v_nargs_975_);
                                    v___x_979_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                        v_val_969_, v___x_976_, v___x_978_,
                                    );
                                    v___x_980_ = l_Lean_mkAppN(v_val_973_, v___x_979_);
                                    lean_dec_ref(v___x_979_);
                                    v___x_981_ =
                                        l_Lean_Meta_Sym_shareCommon___redArg(v___x_980_, v_a_950_);
                                    if lean_obj_tag(v___x_981_) == 0 {
                                        v_a_982_ = lean_ctor_get(v___x_981_, 0);
                                        v_isSharedCheck_990_ =
                                            (!lean_is_exclusive(v___x_981_)) as u8;
                                        if v_isSharedCheck_990_ == 0 {
                                            v___x_984_ = v___x_981_;
                                            v_isShared_985_ = v_isSharedCheck_990_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_982_);
                                            lean_dec(v___x_981_);
                                            v___x_984_ = lean_box(0);
                                            v_isShared_985_ = v_isSharedCheck_990_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        v_a_991_ = lean_ctor_get(v___x_981_, 0);
                                        v_isSharedCheck_998_ =
                                            (!lean_is_exclusive(v___x_981_)) as u8;
                                        if v_isSharedCheck_998_ == 0 {
                                            v___x_993_ = v___x_981_;
                                            v_isShared_994_ = v_isSharedCheck_998_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_991_);
                                            lean_dec(v___x_981_);
                                            v___x_993_ = lean_box(0);
                                            v_isShared_994_ = v_isSharedCheck_998_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_val_969_);
                                v_a_999_ = lean_ctor_get(v___x_971_, 0);
                                v_isSharedCheck_1006_ = (!lean_is_exclusive(v___x_971_)) as u8;
                                if v_isSharedCheck_1006_ == 0 {
                                    v___x_1001_ = v___x_971_;
                                    v_isShared_1002_ = v_isSharedCheck_1006_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_999_);
                                    lean_dec(v___x_971_);
                                    v___x_1001_ = lean_box(0);
                                    v_isShared_1002_ = v_isSharedCheck_1006_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        v_a_1007_ = lean_ctor_get(v___x_967_, 0);
                        v_isSharedCheck_1014_ = (!lean_is_exclusive(v___x_967_)) as u8;
                        if v_isSharedCheck_1014_ == 0 {
                            v___x_1009_ = v___x_967_;
                            v_isShared_1010_ = v_isSharedCheck_1014_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_1007_);
                            lean_dec(v___x_967_);
                            v___x_1009_ = lean_box(0);
                            v_isShared_1010_ = v_isSharedCheck_1014_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_962_);
                    lean_dec_ref(v_e_945_);
                    v___x_1015_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    if v_isShared_965_ == 0 {
                        lean_ctor_set(v___x_964_, 0, v___x_1015_);
                        v___x_1017_ = v___x_964_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1018_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1018_, 0, v___x_1015_);
                        v___x_1017_ = v_reuseFailAlloc_1018_;
                        state = 11;
                        continue;
                    }
                }
            }
            3 => {
                v___x_986_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_986_, 0, v_a_982_);
                lean_ctor_set_uint8(
                    v___x_986_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_966_,
                );
                if v_isShared_985_ == 0 {
                    lean_ctor_set(v___x_984_, 0, v___x_986_);
                    v___x_988_ = v___x_984_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_989_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_989_, 0, v___x_986_);
                    v___x_988_ = v_reuseFailAlloc_989_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_988_;
            }
            5 => {
                if v_isShared_994_ == 0 {
                    v___x_996_ = v___x_993_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_997_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_997_, 0, v_a_991_);
                    v___x_996_ = v_reuseFailAlloc_997_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_996_;
            }
            7 => {
                if v_isShared_1002_ == 0 {
                    v___x_1004_ = v___x_1001_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1005_, 0, v_a_999_);
                    v___x_1004_ = v_reuseFailAlloc_1005_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1004_;
            }
            9 => {
                if v_isShared_1010_ == 0 {
                    v___x_1012_ = v___x_1009_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1013_, 0, v_a_1007_);
                    v___x_1012_ = v_reuseFailAlloc_1013_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1012_;
            }
            11 => {
                return v___x_1017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpProj___boxed(
    mut v_e_1022_: *mut LeanObject,
    mut v_a_1023_: *mut LeanObject,
    mut v_a_1024_: *mut LeanObject,
    mut v_a_1025_: *mut LeanObject,
    mut v_a_1026_: *mut LeanObject,
    mut v_a_1027_: *mut LeanObject,
    mut v_a_1028_: *mut LeanObject,
    mut v_a_1029_: *mut LeanObject,
    mut v_a_1030_: *mut LeanObject,
    mut v_a_1031_: *mut LeanObject,
    mut v_a_1032_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1033_: *mut LeanObject = core::ptr::null_mut();
    v_res_1033_ = l_Lean_Meta_Sym_DSimp_dsimpProj(
        v_e_1022_, v_a_1023_, v_a_1024_, v_a_1025_, v_a_1026_, v_a_1027_, v_a_1028_, v_a_1029_,
        v_a_1030_, v_a_1031_,
    );
    lean_dec(v_a_1031_);
    lean_dec_ref(v_a_1030_);
    lean_dec(v_a_1029_);
    lean_dec_ref(v_a_1028_);
    lean_dec(v_a_1027_);
    lean_dec_ref(v_a_1026_);
    lean_dec(v_a_1025_);
    lean_dec(v_a_1024_);
    lean_dec(v_a_1023_);
    return v_res_1033_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(
    mut v_e_1034_: *mut LeanObject,
    mut v_a_1035_: *mut LeanObject,
    mut v_a_1036_: *mut LeanObject,
    mut v_a_1037_: *mut LeanObject,
    mut v_a_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1045_: u8 = 0;
    let mut v_val_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1053_: u8 = 0;
    let mut v___x_1054_: u8 = 0;
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v_a_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1063_: u8 = 0;
    let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1067_: u8 = 0;
    let mut v_a_1068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1071_: u8 = 0;
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1075_: u8 = 0;
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1080_: u8 = 0;
    let mut v_a_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1084_: u8 = 0;
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1088_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1041_ = l_Lean_Meta_reduceRecMatcher_x3f(
                    v_e_1034_, v_a_1036_, v_a_1037_, v_a_1038_, v_a_1039_,
                );
                if lean_obj_tag(v___x_1041_) == 0 {
                    v_a_1042_ = lean_ctor_get(v___x_1041_, 0);
                    v_isSharedCheck_1080_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1080_ == 0 {
                        v___x_1044_ = v___x_1041_;
                        v_isShared_1045_ = v_isSharedCheck_1080_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_1042_);
                        lean_dec(v___x_1041_);
                        v___x_1044_ = lean_box(0);
                        v_isShared_1045_ = v_isSharedCheck_1080_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1081_ = lean_ctor_get(v___x_1041_, 0);
                    v_isSharedCheck_1088_ = (!lean_is_exclusive(v___x_1041_)) as u8;
                    if v_isSharedCheck_1088_ == 0 {
                        v___x_1083_ = v___x_1041_;
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_1081_);
                        lean_dec(v___x_1041_);
                        v___x_1083_ = lean_box(0);
                        v_isShared_1084_ = v_isSharedCheck_1088_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_1042_) == 1 {
                    lean_del_object(v___x_1044_);
                    v_val_1046_ = lean_ctor_get(v_a_1042_, 0);
                    lean_inc(v_val_1046_);
                    lean_dec_ref_known(v_a_1042_, 1);
                    v___x_1047_ = l_Lean_Meta_Sym_foldProjs(
                        v_val_1046_,
                        v_a_1036_,
                        v_a_1037_,
                        v_a_1038_,
                        v_a_1039_,
                    );
                    if lean_obj_tag(v___x_1047_) == 0 {
                        v_a_1048_ = lean_ctor_get(v___x_1047_, 0);
                        lean_inc(v_a_1048_);
                        lean_dec_ref_known(v___x_1047_, 1);
                        v___x_1049_ = l_Lean_Meta_Sym_shareCommonInc___redArg(v_a_1048_, v_a_1035_);
                        if lean_obj_tag(v___x_1049_) == 0 {
                            v_a_1050_ = lean_ctor_get(v___x_1049_, 0);
                            v_isSharedCheck_1059_ = (!lean_is_exclusive(v___x_1049_)) as u8;
                            if v_isSharedCheck_1059_ == 0 {
                                v___x_1052_ = v___x_1049_;
                                v_isShared_1053_ = v_isSharedCheck_1059_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_1050_);
                                lean_dec(v___x_1049_);
                                v___x_1052_ = lean_box(0);
                                v_isShared_1053_ = v_isSharedCheck_1059_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_a_1060_ = lean_ctor_get(v___x_1049_, 0);
                            v_isSharedCheck_1067_ = (!lean_is_exclusive(v___x_1049_)) as u8;
                            if v_isSharedCheck_1067_ == 0 {
                                v___x_1062_ = v___x_1049_;
                                v_isShared_1063_ = v_isSharedCheck_1067_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_1060_);
                                lean_dec(v___x_1049_);
                                v___x_1062_ = lean_box(0);
                                v_isShared_1063_ = v_isSharedCheck_1067_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_a_1068_ = lean_ctor_get(v___x_1047_, 0);
                        v_isSharedCheck_1075_ = (!lean_is_exclusive(v___x_1047_)) as u8;
                        if v_isSharedCheck_1075_ == 0 {
                            v___x_1070_ = v___x_1047_;
                            v_isShared_1071_ = v_isSharedCheck_1075_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_1068_);
                            lean_dec(v___x_1047_);
                            v___x_1070_ = lean_box(0);
                            v_isShared_1071_ = v_isSharedCheck_1075_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_1042_);
                    v___x_1076_ = l_Lean_Meta_Sym_DSimp_beta___redArg___closed__0;
                    if v_isShared_1045_ == 0 {
                        lean_ctor_set(v___x_1044_, 0, v___x_1076_);
                        v___x_1078_ = v___x_1044_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
                        v___x_1078_ = v_reuseFailAlloc_1079_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1054_ = 0;
                v___x_1055_ = lean_alloc_ctor(1, 1, (1) as u32);
                lean_ctor_set(v___x_1055_, 0, v_a_1050_);
                lean_ctor_set_uint8(
                    v___x_1055_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v___x_1054_,
                );
                if v_isShared_1053_ == 0 {
                    lean_ctor_set(v___x_1052_, 0, v___x_1055_);
                    v___x_1057_ = v___x_1052_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1058_, 0, v___x_1055_);
                    v___x_1057_ = v_reuseFailAlloc_1058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1057_;
            }
            4 => {
                if v_isShared_1063_ == 0 {
                    v___x_1065_ = v___x_1062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1066_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1066_, 0, v_a_1060_);
                    v___x_1065_ = v_reuseFailAlloc_1066_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1065_;
            }
            6 => {
                if v_isShared_1071_ == 0 {
                    v___x_1073_ = v___x_1070_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1074_, 0, v_a_1068_);
                    v___x_1073_ = v_reuseFailAlloc_1074_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1073_;
            }
            8 => {
                return v___x_1078_;
            }
            9 => {
                if v_isShared_1084_ == 0 {
                    v___x_1086_ = v___x_1083_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1087_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_a_1081_);
                    v___x_1086_ = v_reuseFailAlloc_1087_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1086_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg___boxed(
    mut v_e_1089_: *mut LeanObject,
    mut v_a_1090_: *mut LeanObject,
    mut v_a_1091_: *mut LeanObject,
    mut v_a_1092_: *mut LeanObject,
    mut v_a_1093_: *mut LeanObject,
    mut v_a_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1096_: *mut LeanObject = core::ptr::null_mut();
    v_res_1096_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(
        v_e_1089_, v_a_1090_, v_a_1091_, v_a_1092_, v_a_1093_, v_a_1094_,
    );
    lean_dec(v_a_1094_);
    lean_dec_ref(v_a_1093_);
    lean_dec(v_a_1092_);
    lean_dec_ref(v_a_1091_);
    lean_dec(v_a_1090_);
    lean_dec_ref(v_e_1089_);
    return v_res_1096_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpMatch(
    mut v_e_1097_: *mut LeanObject,
    mut v_a_1098_: *mut LeanObject,
    mut v_a_1099_: *mut LeanObject,
    mut v_a_1100_: *mut LeanObject,
    mut v_a_1101_: *mut LeanObject,
    mut v_a_1102_: *mut LeanObject,
    mut v_a_1103_: *mut LeanObject,
    mut v_a_1104_: *mut LeanObject,
    mut v_a_1105_: *mut LeanObject,
    mut v_a_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1108_: *mut LeanObject = core::ptr::null_mut();
    v___x_1108_ = l_Lean_Meta_Sym_DSimp_dsimpMatch___redArg(
        v_e_1097_, v_a_1102_, v_a_1103_, v_a_1104_, v_a_1105_, v_a_1106_,
    );
    return v___x_1108_;
}
pub unsafe fn l_Lean_Meta_Sym_DSimp_dsimpMatch___boxed(
    mut v_e_1109_: *mut LeanObject,
    mut v_a_1110_: *mut LeanObject,
    mut v_a_1111_: *mut LeanObject,
    mut v_a_1112_: *mut LeanObject,
    mut v_a_1113_: *mut LeanObject,
    mut v_a_1114_: *mut LeanObject,
    mut v_a_1115_: *mut LeanObject,
    mut v_a_1116_: *mut LeanObject,
    mut v_a_1117_: *mut LeanObject,
    mut v_a_1118_: *mut LeanObject,
    mut v_a_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1120_: *mut LeanObject = core::ptr::null_mut();
    v_res_1120_ = l_Lean_Meta_Sym_DSimp_dsimpMatch(
        v_e_1109_, v_a_1110_, v_a_1111_, v_a_1112_, v_a_1113_, v_a_1114_, v_a_1115_, v_a_1116_,
        v_a_1117_, v_a_1118_,
    );
    lean_dec(v_a_1118_);
    lean_dec_ref(v_a_1117_);
    lean_dec(v_a_1116_);
    lean_dec_ref(v_a_1115_);
    lean_dec(v_a_1114_);
    lean_dec_ref(v_a_1113_);
    lean_dec(v_a_1112_);
    lean_dec(v_a_1111_);
    lean_dec(v_a_1110_);
    lean_dec_ref(v_e_1109_);
    return v_res_1120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_DSimp_Reduce(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_InstantiateS(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_WHNF(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_ProjFns(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_DSimp_Reduce(builtin);
}

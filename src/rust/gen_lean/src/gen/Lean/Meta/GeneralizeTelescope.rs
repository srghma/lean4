// Lean compiler output
// Module: Lean.Meta.GeneralizeTelescope
// Imports: Lean.Meta.KAbstract Lean.Meta.Check
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_size,
    lean_array_push, lean_array_size, lean_array_to_list, lean_array_uget,
    lean_array_uget_borrowed, lean_array_uset, lean_expr_instantiate1, lean_infer_type,
    lean_nat_add, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_hasLooseBVars, l_Lean_Expr_hasMVar};
use crate::r#gen::Lean::LocalContext::l_Lean_LocalDecl_userName;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp, l_Lean_FVarId_getDecl___redArg,
};
use crate::r#gen::Lean::Meta::Check::{
    initialize_Lean_Meta_Check, l_Lean_Meta_isTypeCorrect, runtime_initialize_Lean_Meta_Check,
};
use crate::r#gen::Lean::Meta::KAbstract::{
    initialize_Lean_Meta_KAbstract, l_Lean_Meta_kabstract, runtime_initialize_Lean_Meta_KAbstract,
};
use crate::r#gen::Lean::MetavarContext::l_Lean_instantiateMVarsCore;
pub static l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [120, 0],
};
static mut l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__0_value
        ) as *mut leanh::LeanObject,
        13655884332201764339 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 99, 114, 101, 97, 116, 101, 32, 116, 101,
        108, 101, 115, 99, 111, 112, 101, 32, 103, 101, 110, 101, 114, 97, 108, 105, 122, 105, 110,
        103, 32, 0,
    ],
};
static mut l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_generalizeTelescope___redArg___closed__0_value:
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
static mut l_Lean_Meta_generalizeTelescope___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_generalizeTelescope___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_updateTypes(
    mut v_e_582_: *mut leanh::LeanObject,
    mut v_eNew_583_: *mut leanh::LeanObject,
    mut v_entries_584_: *mut leanh::LeanObject,
    mut v_i_585_: *mut leanh::LeanObject,
    mut v_a_586_: *mut leanh::LeanObject,
    mut v_a_587_: *mut leanh::LeanObject,
    mut v_a_588_: *mut leanh::LeanObject,
    mut v_a_589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: u8 = 0;
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_599_: u8 = 0;
    let mut v___x_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: u8 = 0;
    let mut v___x_604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_618_: u8 = 0;
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_622_: u8 = 0;
    let mut v_isSharedCheck_623_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_591_ = lean_array_get_size(v_entries_584_);
                v___x_592_ = lean_nat_dec_lt(v_i_585_, v___x_591_);
                if v___x_592_ == 0 {
                    leanh::lean_dec(v_i_585_);
                    leanh::lean_dec_ref(v_e_582_);
                    v___x_593_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_593_, 0, v_entries_584_);
                    return v___x_593_;
                } else {
                    v_entry_594_ = lean_array_fget(v_entries_584_, v_i_585_);
                    v_expr_595_ = leanh::lean_ctor_get(v_entry_594_, 0);
                    v_type_596_ = leanh::lean_ctor_get(v_entry_594_, 1);
                    v_isSharedCheck_623_ = (!leanh::lean_is_exclusive(v_entry_594_)) as u8;
                    if v_isSharedCheck_623_ == 0 {
                        v___x_598_ = v_entry_594_;
                        v_isShared_599_ = v_isSharedCheck_623_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_type_596_);
                        leanh::lean_inc(v_expr_595_);
                        leanh::lean_dec(v_entry_594_);
                        v___x_598_ = leanh::lean_box(0);
                        v_isShared_599_ = v_isSharedCheck_623_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_600_ = leanh::lean_box(0);
                leanh::lean_inc_ref(v_e_582_);
                v___x_601_ = l_Lean_Meta_kabstract(
                    v_type_596_,
                    v_e_582_,
                    v___x_600_,
                    v_a_586_,
                    v_a_587_,
                    v_a_588_,
                    v_a_589_,
                );
                if leanh::lean_obj_tag(v___x_601_) == 0 {
                    v_a_602_ = leanh::lean_ctor_get(v___x_601_, 0);
                    leanh::lean_inc(v_a_602_);
                    leanh::lean_dec_ref_known(v___x_601_, 1);
                    v___x_603_ = l_Lean_Expr_hasLooseBVars(v_a_602_);
                    if v___x_603_ == 0 {
                        leanh::lean_dec(v_a_602_);
                        leanh::lean_del_object(v___x_598_);
                        leanh::lean_dec_ref(v_expr_595_);
                        v___x_604_ = leanh::lean_unsigned_to_nat(1);
                        v___x_605_ = lean_nat_add(v_i_585_, v___x_604_);
                        leanh::lean_dec(v_i_585_);
                        v_i_585_ = v___x_605_;
                        state = 0;
                        continue;
                    } else {
                        v___x_607_ = lean_expr_instantiate1(v_a_602_, v_eNew_583_);
                        leanh::lean_dec(v_a_602_);
                        if v_isShared_599_ == 0 {
                            leanh::lean_ctor_set(v___x_598_, 1, v___x_607_);
                            v___x_609_ = v___x_598_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_614_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_614_, 0, v_expr_595_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_614_, 1, v___x_607_);
                            v___x_609_ = v_reuseFailAlloc_614_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_598_);
                    leanh::lean_dec_ref(v_expr_595_);
                    leanh::lean_dec(v_i_585_);
                    leanh::lean_dec_ref(v_entries_584_);
                    leanh::lean_dec_ref(v_e_582_);
                    v_a_615_ = leanh::lean_ctor_get(v___x_601_, 0);
                    v_isSharedCheck_622_ = (!leanh::lean_is_exclusive(v___x_601_)) as u8;
                    if v_isSharedCheck_622_ == 0 {
                        v___x_617_ = v___x_601_;
                        v_isShared_618_ = v_isSharedCheck_622_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_615_);
                        leanh::lean_dec(v___x_601_);
                        v___x_617_ = leanh::lean_box(0);
                        v_isShared_618_ = v_isSharedCheck_622_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_ctor_set_uint8(
                    v___x_609_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_603_,
                );
                v___x_610_ = lean_array_fset(v_entries_584_, v_i_585_, v___x_609_);
                v___x_611_ = leanh::lean_unsigned_to_nat(1);
                v___x_612_ = lean_nat_add(v_i_585_, v___x_611_);
                leanh::lean_dec(v_i_585_);
                v_entries_584_ = v___x_610_;
                v_i_585_ = v___x_612_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_618_ == 0 {
                    v___x_620_ = v___x_617_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_621_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_621_, 0, v_a_615_);
                    v___x_620_ = v_reuseFailAlloc_621_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_updateTypes___boxed(
    mut v_e_624_: *mut leanh::LeanObject,
    mut v_eNew_625_: *mut leanh::LeanObject,
    mut v_entries_626_: *mut leanh::LeanObject,
    mut v_i_627_: *mut leanh::LeanObject,
    mut v_a_628_: *mut leanh::LeanObject,
    mut v_a_629_: *mut leanh::LeanObject,
    mut v_a_630_: *mut leanh::LeanObject,
    mut v_a_631_: *mut leanh::LeanObject,
    mut v_a_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_633_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(
        v_e_624_,
        v_eNew_625_,
        v_entries_626_,
        v_i_627_,
        v_a_628_,
        v_a_629_,
        v_a_630_,
        v_a_631_,
    );
    leanh::lean_dec(v_a_631_);
    leanh::lean_dec_ref(v_a_630_);
    leanh::lean_dec(v_a_629_);
    leanh::lean_dec_ref(v_a_628_);
    leanh::lean_dec_ref(v_eNew_625_);
    return v_res_633_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(
    mut v_msgData_634_: *mut leanh::LeanObject,
    mut v___y_635_: *mut leanh::LeanObject,
    mut v___y_636_: *mut leanh::LeanObject,
    mut v___y_637_: *mut leanh::LeanObject,
    mut v___y_638_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_640_ = lean_st_ref_get(v___y_638_);
    v_env_641_ = leanh::lean_ctor_get(v___x_640_, 0);
    leanh::lean_inc_ref(v_env_641_);
    leanh::lean_dec(v___x_640_);
    v___x_642_ = lean_st_ref_get(v___y_636_);
    v_mctx_643_ = leanh::lean_ctor_get(v___x_642_, 0);
    leanh::lean_inc_ref(v_mctx_643_);
    leanh::lean_dec(v___x_642_);
    v_lctx_644_ = leanh::lean_ctor_get(v___y_635_, 2);
    v_options_645_ = leanh::lean_ctor_get(v___y_637_, 2);
    leanh::lean_inc_ref(v_options_645_);
    leanh::lean_inc_ref(v_lctx_644_);
    v___x_646_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_646_, 0, v_env_641_);
    leanh::lean_ctor_set(v___x_646_, 1, v_mctx_643_);
    leanh::lean_ctor_set(v___x_646_, 2, v_lctx_644_);
    leanh::lean_ctor_set(v___x_646_, 3, v_options_645_);
    v___x_647_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_647_, 0, v___x_646_);
    leanh::lean_ctor_set(v___x_647_, 1, v_msgData_634_);
    v___x_648_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_648_, 0, v___x_647_);
    return v___x_648_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4___boxed(
    mut v_msgData_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
    mut v___y_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
    mut v___y_653_: *mut leanh::LeanObject,
    mut v___y_654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_655_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msgData_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_);
    leanh::lean_dec(v___y_653_);
    leanh::lean_dec_ref(v___y_652_);
    leanh::lean_dec(v___y_651_);
    leanh::lean_dec_ref(v___y_650_);
    return v_res_655_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(
    mut v_msg_656_: *mut leanh::LeanObject,
    mut v___y_657_: *mut leanh::LeanObject,
    mut v___y_658_: *mut leanh::LeanObject,
    mut v___y_659_: *mut leanh::LeanObject,
    mut v___y_660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_667_: u8 = 0;
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_672_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_662_ = leanh::lean_ctor_get(v___y_659_, 5);
                v___x_663_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3_spec__4(v_msg_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
                v_a_664_ = leanh::lean_ctor_get(v___x_663_, 0);
                v_isSharedCheck_672_ = (!leanh::lean_is_exclusive(v___x_663_)) as u8;
                if v_isSharedCheck_672_ == 0 {
                    v___x_666_ = v___x_663_;
                    v_isShared_667_ = v_isSharedCheck_672_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_664_);
                    leanh::lean_dec(v___x_663_);
                    v___x_666_ = leanh::lean_box(0);
                    v_isShared_667_ = v_isSharedCheck_672_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_662_);
                v___x_668_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_668_, 0, v_ref_662_);
                leanh::lean_ctor_set(v___x_668_, 1, v_a_664_);
                if v_isShared_667_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_666_, 1);
                    leanh::lean_ctor_set(v___x_666_, 0, v___x_668_);
                    v___x_670_ = v___x_666_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_671_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_671_, 0, v___x_668_);
                    v___x_670_ = v_reuseFailAlloc_671_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_670_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg___boxed(
    mut v_msg_673_: *mut leanh::LeanObject,
    mut v___y_674_: *mut leanh::LeanObject,
    mut v___y_675_: *mut leanh::LeanObject,
    mut v___y_676_: *mut leanh::LeanObject,
    mut v___y_677_: *mut leanh::LeanObject,
    mut v___y_678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_);
    leanh::lean_dec(v___y_677_);
    leanh::lean_dec_ref(v___y_676_);
    leanh::lean_dec(v___y_675_);
    leanh::lean_dec_ref(v___y_674_);
    return v_res_679_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(
    mut v_k_680_: *mut leanh::LeanObject,
    mut v_b_681_: *mut leanh::LeanObject,
    mut v___y_682_: *mut leanh::LeanObject,
    mut v___y_683_: *mut leanh::LeanObject,
    mut v___y_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_685_);
    leanh::lean_inc_ref(v___y_684_);
    leanh::lean_inc(v___y_683_);
    leanh::lean_inc_ref(v___y_682_);
    v___x_687_ = leanh::lean_apply_6(
        v_k_680_,
        v_b_681_,
        v___y_682_,
        v___y_683_,
        v___y_684_,
        v___y_685_,
        leanh::lean_box(0),
    );
    return v___x_687_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed(
    mut v_k_688_: *mut leanh::LeanObject,
    mut v_b_689_: *mut leanh::LeanObject,
    mut v___y_690_: *mut leanh::LeanObject,
    mut v___y_691_: *mut leanh::LeanObject,
    mut v___y_692_: *mut leanh::LeanObject,
    mut v___y_693_: *mut leanh::LeanObject,
    mut v___y_694_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_695_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0(v_k_688_, v_b_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_);
    leanh::lean_dec(v___y_693_);
    leanh::lean_dec_ref(v___y_692_);
    leanh::lean_dec(v___y_691_);
    leanh::lean_dec_ref(v___y_690_);
    return v_res_695_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(
    mut v_name_696_: *mut leanh::LeanObject,
    mut v_bi_697_: u8,
    mut v_type_698_: *mut leanh::LeanObject,
    mut v_k_699_: *mut leanh::LeanObject,
    mut v_kind_700_: u8,
    mut v___y_701_: *mut leanh::LeanObject,
    mut v___y_702_: *mut leanh::LeanObject,
    mut v___y_703_: *mut leanh::LeanObject,
    mut v___y_704_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_711_: u8 = 0;
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut v_a_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_719_: u8 = 0;
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_706_ = leanh::lean_alloc_closure(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 7, 1);
                leanh::lean_closure_set(v___f_706_, 0, v_k_699_);
                v___x_707_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(
                    leanh::lean_box(0),
                    v_name_696_,
                    v_bi_697_,
                    v_type_698_,
                    v___f_706_,
                    v_kind_700_,
                    v___y_701_,
                    v___y_702_,
                    v___y_703_,
                    v___y_704_,
                );
                if leanh::lean_obj_tag(v___x_707_) == 0 {
                    v_a_708_ = leanh::lean_ctor_get(v___x_707_, 0);
                    v_isSharedCheck_715_ = (!leanh::lean_is_exclusive(v___x_707_)) as u8;
                    if v_isSharedCheck_715_ == 0 {
                        v___x_710_ = v___x_707_;
                        v_isShared_711_ = v_isSharedCheck_715_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_708_);
                        leanh::lean_dec(v___x_707_);
                        v___x_710_ = leanh::lean_box(0);
                        v_isShared_711_ = v_isSharedCheck_715_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_716_ = leanh::lean_ctor_get(v___x_707_, 0);
                    v_isSharedCheck_723_ = (!leanh::lean_is_exclusive(v___x_707_)) as u8;
                    if v_isSharedCheck_723_ == 0 {
                        v___x_718_ = v___x_707_;
                        v_isShared_719_ = v_isSharedCheck_723_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_716_);
                        leanh::lean_dec(v___x_707_);
                        v___x_718_ = leanh::lean_box(0);
                        v_isShared_719_ = v_isSharedCheck_723_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_711_ == 0 {
                    v___x_713_ = v___x_710_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_714_, 0, v_a_708_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_713_;
            }
            3 => {
                if v_isShared_719_ == 0 {
                    v___x_721_ = v___x_718_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_722_, 0, v_a_716_);
                    v___x_721_ = v_reuseFailAlloc_722_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg___boxed(
    mut v_name_724_: *mut leanh::LeanObject,
    mut v_bi_725_: *mut leanh::LeanObject,
    mut v_type_726_: *mut leanh::LeanObject,
    mut v_k_727_: *mut leanh::LeanObject,
    mut v_kind_728_: *mut leanh::LeanObject,
    mut v___y_729_: *mut leanh::LeanObject,
    mut v___y_730_: *mut leanh::LeanObject,
    mut v___y_731_: *mut leanh::LeanObject,
    mut v___y_732_: *mut leanh::LeanObject,
    mut v___y_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_734_: u8 = 0;
    let mut v_kind_boxed_735_: u8 = 0;
    let mut v_res_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_734_ = (leanh::lean_unbox(v_bi_725_) as u8);
    v_kind_boxed_735_ = (leanh::lean_unbox(v_kind_728_) as u8);
    v_res_736_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_724_, v_bi_boxed_734_, v_type_726_, v_k_727_, v_kind_boxed_735_, v___y_729_, v___y_730_, v___y_731_, v___y_732_);
    leanh::lean_dec(v___y_732_);
    leanh::lean_dec_ref(v___y_731_);
    leanh::lean_dec(v___y_730_);
    leanh::lean_dec_ref(v___y_729_);
    return v_res_736_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(
    mut v_name_737_: *mut leanh::LeanObject,
    mut v_type_738_: *mut leanh::LeanObject,
    mut v_k_739_: *mut leanh::LeanObject,
    mut v___y_740_: *mut leanh::LeanObject,
    mut v___y_741_: *mut leanh::LeanObject,
    mut v___y_742_: *mut leanh::LeanObject,
    mut v___y_743_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_745_: u8 = 0;
    let mut v___x_746_: u8 = 0;
    let mut v___x_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_745_ = 0;
    v___x_746_ = 0;
    v___x_747_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_737_, v___x_745_, v_type_738_, v_k_739_, v___x_746_, v___y_740_, v___y_741_, v___y_742_, v___y_743_);
    return v___x_747_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg___boxed(
    mut v_name_748_: *mut leanh::LeanObject,
    mut v_type_749_: *mut leanh::LeanObject,
    mut v_k_750_: *mut leanh::LeanObject,
    mut v___y_751_: *mut leanh::LeanObject,
    mut v___y_752_: *mut leanh::LeanObject,
    mut v___y_753_: *mut leanh::LeanObject,
    mut v___y_754_: *mut leanh::LeanObject,
    mut v___y_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_748_, v_type_749_, v_k_750_, v___y_751_, v___y_752_, v___y_753_, v___y_754_);
    leanh::lean_dec(v___y_754_);
    leanh::lean_dec_ref(v___y_753_);
    leanh::lean_dec(v___y_752_);
    leanh::lean_dec_ref(v___y_751_);
    return v_res_756_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(
    mut v_a_757_: *mut leanh::LeanObject,
    mut v_a_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_757_) == 0 {
                    v___x_759_ = l_List_reverse___redArg(v_a_758_);
                    return v___x_759_;
                } else {
                    v_head_760_ = leanh::lean_ctor_get(v_a_757_, 0);
                    v_tail_761_ = leanh::lean_ctor_get(v_a_757_, 1);
                    v_isSharedCheck_770_ = (!leanh::lean_is_exclusive(v_a_757_)) as u8;
                    if v_isSharedCheck_770_ == 0 {
                        v___x_763_ = v_a_757_;
                        v_isShared_764_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_761_);
                        leanh::lean_inc(v_head_760_);
                        leanh::lean_dec(v_a_757_);
                        v___x_763_ = leanh::lean_box(0);
                        v_isShared_764_ = v_isSharedCheck_770_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_765_ = l_Lean_MessageData_ofExpr(v_head_760_);
                if v_isShared_764_ == 0 {
                    leanh::lean_ctor_set(v___x_763_, 1, v_a_758_);
                    leanh::lean_ctor_set(v___x_763_, 0, v___x_765_);
                    v___x_767_ = v___x_763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_769_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_769_, 0, v___x_765_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_769_, 1, v_a_758_);
                    v___x_767_ = v_reuseFailAlloc_769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_757_ = v_tail_761_;
                v_a_758_ = v___x_767_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(
    mut v_sz_771_: usize,
    mut v_i_772_: usize,
    mut v_bs_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_774_: u8 = 0;
    let mut v_v_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_779_: usize = 0;
    let mut v___x_780_: usize = 0;
    let mut v___x_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_774_ = lean_usize_dec_lt(v_i_772_, v_sz_771_);
                if v___x_774_ == 0 {
                    return v_bs_773_;
                } else {
                    v_v_775_ = lean_array_uget_borrowed(v_bs_773_, v_i_772_);
                    v_expr_776_ = leanh::lean_ctor_get(v_v_775_, 0);
                    leanh::lean_inc_ref(v_expr_776_);
                    v___x_777_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_778_ = lean_array_uset(v_bs_773_, v_i_772_, v___x_777_);
                    v___x_779_ = 1usize;
                    v___x_780_ = lean_usize_add(v_i_772_, v___x_779_);
                    v___x_781_ = lean_array_uset(v_bs_x27_778_, v_i_772_, v_expr_776_);
                    v_i_772_ = v___x_780_;
                    v_bs_773_ = v___x_781_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1___boxed(
    mut v_sz_783_: *mut leanh::LeanObject,
    mut v_i_784_: *mut leanh::LeanObject,
    mut v_bs_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_786_: usize = 0;
    let mut v_i_boxed_787_: usize = 0;
    let mut v_res_788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_786_ = leanh::lean_unbox_usize(v_sz_783_);
    leanh::lean_dec(v_sz_783_);
    v_i_boxed_787_ = leanh::lean_unbox_usize(v_i_784_);
    leanh::lean_dec(v_i_784_);
    v_res_788_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_boxed_786_, v_i_boxed_787_, v_bs_785_);
    return v_res_788_;
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed(
    mut v_i_789_: *mut leanh::LeanObject,
    mut v_e_790_: *mut leanh::LeanObject,
    mut v_entries_791_: *mut leanh::LeanObject,
    mut v_fvars_792_: *mut leanh::LeanObject,
    mut v_k_793_: *mut leanh::LeanObject,
    mut v_x_794_: *mut leanh::LeanObject,
    mut v___y_795_: *mut leanh::LeanObject,
    mut v___y_796_: *mut leanh::LeanObject,
    mut v___y_797_: *mut leanh::LeanObject,
    mut v___y_798_: *mut leanh::LeanObject,
    mut v___y_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_800_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(
        v_i_789_,
        v_e_790_,
        v_entries_791_,
        v_fvars_792_,
        v_k_793_,
        v_x_794_,
        v___y_795_,
        v___y_796_,
        v___y_797_,
        v___y_798_,
    );
    leanh::lean_dec(v___y_798_);
    leanh::lean_dec_ref(v___y_797_);
    leanh::lean_dec(v___y_796_);
    leanh::lean_dec_ref(v___y_795_);
    leanh::lean_dec(v_i_789_);
    return v_res_800_;
}
pub unsafe fn _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_805_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__2;
    v___x_806_ = l_Lean_stringToMessageData(v___x_805_);
    return v___x_806_;
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(
    mut v_k_807_: *mut leanh::LeanObject,
    mut v_entries_808_: *mut leanh::LeanObject,
    mut v_i_809_: *mut leanh::LeanObject,
    mut v_fvars_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
    mut v_a_813_: *mut leanh::LeanObject,
    mut v_a_814_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_baseUserName_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_831_: u8 = 0;
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_835_: u8 = 0;
    let mut v___y_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: u8 = 0;
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_modified_850_: u8 = 0;
    let mut v___y_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: u8 = 0;
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_860_: usize = 0;
    let mut v___x_861_: usize = 0;
    let mut v___x_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_876_: u8 = 0;
    let mut v_a_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_880_: u8 = 0;
    let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_884_: u8 = 0;
    let mut v_fvarId_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_896_: u8 = 0;
    let mut v___x_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_900_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_844_ = lean_array_get_size(v_entries_808_);
                v___x_845_ = lean_nat_dec_lt(v_i_809_, v___x_844_);
                if v___x_845_ == 0 {
                    leanh::lean_dec(v_i_809_);
                    leanh::lean_dec_ref(v_entries_808_);
                    leanh::lean_inc(v_a_814_);
                    leanh::lean_inc_ref(v_a_813_);
                    leanh::lean_inc(v_a_812_);
                    leanh::lean_inc_ref(v_a_811_);
                    v___x_846_ = leanh::lean_apply_6(
                        v_k_807_,
                        v_fvars_810_,
                        v_a_811_,
                        v_a_812_,
                        v_a_813_,
                        v_a_814_,
                        leanh::lean_box(0),
                    );
                    return v___x_846_;
                } else {
                    v___x_847_ = lean_array_fget_borrowed(v_entries_808_, v_i_809_);
                    v_expr_848_ = leanh::lean_ctor_get(v___x_847_, 0);
                    v_type_849_ = leanh::lean_ctor_get(v___x_847_, 1);
                    v_modified_850_ = leanh::lean_ctor_get_uint8(
                        v___x_847_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    if leanh::lean_obj_tag(v_expr_848_) == 1 {
                        if v_modified_850_ == 0 {
                            v_fvarId_885_ = leanh::lean_ctor_get(v_expr_848_, 0);
                            leanh::lean_inc(v_fvarId_885_);
                            v___x_886_ = l_Lean_FVarId_getDecl___redArg(
                                v_fvarId_885_,
                                v_a_811_,
                                v_a_813_,
                                v_a_814_,
                            );
                            if leanh::lean_obj_tag(v___x_886_) == 0 {
                                v_a_887_ = leanh::lean_ctor_get(v___x_886_, 0);
                                leanh::lean_inc(v_a_887_);
                                leanh::lean_dec_ref_known(v___x_886_, 1);
                                if leanh::lean_obj_tag(v_a_887_) == 0 {
                                    leanh::lean_dec_ref_known(v_a_887_, 4);
                                    v___x_888_ = leanh::lean_unsigned_to_nat(1);
                                    v___x_889_ = lean_nat_add(v_i_809_, v___x_888_);
                                    leanh::lean_dec(v_i_809_);
                                    leanh::lean_inc_ref(v_expr_848_);
                                    v___x_890_ = lean_array_push(v_fvars_810_, v_expr_848_);
                                    v_i_809_ = v___x_889_;
                                    v_fvars_810_ = v___x_890_;
                                    state = 0;
                                    continue;
                                } else {
                                    v___x_892_ = l_Lean_LocalDecl_userName(v_a_887_);
                                    leanh::lean_dec_ref_known(v_a_887_, 5);
                                    leanh::lean_inc_ref(v_type_849_);
                                    leanh::lean_inc_ref(v_expr_848_);
                                    v_baseUserName_817_ = v___x_892_;
                                    v_e_818_ = v_expr_848_;
                                    v_type_819_ = v_type_849_;
                                    v___y_820_ = v_a_811_;
                                    v___y_821_ = v_a_812_;
                                    v___y_822_ = v_a_813_;
                                    v___y_823_ = v_a_814_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v_fvars_810_);
                                leanh::lean_dec(v_i_809_);
                                leanh::lean_dec_ref(v_entries_808_);
                                leanh::lean_dec_ref(v_k_807_);
                                v_a_893_ = leanh::lean_ctor_get(v___x_886_, 0);
                                v_isSharedCheck_900_ =
                                    (!leanh::lean_is_exclusive(v___x_886_)) as u8;
                                if v_isSharedCheck_900_ == 0 {
                                    v___x_895_ = v___x_886_;
                                    v_isShared_896_ = v_isSharedCheck_900_;
                                    state = 10;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_893_);
                                    leanh::lean_dec(v___x_886_);
                                    v___x_895_ = leanh::lean_box(0);
                                    v_isShared_896_ = v_isSharedCheck_900_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            v___y_852_ = v_a_811_;
                            v___y_853_ = v_a_812_;
                            v___y_854_ = v_a_813_;
                            v___y_855_ = v_a_814_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_852_ = v_a_811_;
                        v___y_853_ = v_a_812_;
                        v___y_854_ = v_a_813_;
                        v___y_855_ = v_a_814_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_824_ =
                    l_Lean_Core_mkFreshUserName(v_baseUserName_817_, v___y_822_, v___y_823_);
                if leanh::lean_obj_tag(v___x_824_) == 0 {
                    v_a_825_ = leanh::lean_ctor_get(v___x_824_, 0);
                    leanh::lean_inc(v_a_825_);
                    leanh::lean_dec_ref_known(v___x_824_, 1);
                    v___f_826_ = leanh::lean_alloc_closure(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0___boxed as *mut core::ffi::c_void, 11, 5);
                    leanh::lean_closure_set(v___f_826_, 0, v_i_809_);
                    leanh::lean_closure_set(v___f_826_, 1, v_e_818_);
                    leanh::lean_closure_set(v___f_826_, 2, v_entries_808_);
                    leanh::lean_closure_set(v___f_826_, 3, v_fvars_810_);
                    leanh::lean_closure_set(v___f_826_, 4, v_k_807_);
                    v___x_827_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_a_825_, v_type_819_, v___f_826_, v___y_820_, v___y_821_, v___y_822_, v___y_823_);
                    return v___x_827_;
                } else {
                    leanh::lean_dec_ref(v_type_819_);
                    leanh::lean_dec_ref(v_e_818_);
                    leanh::lean_dec_ref(v_fvars_810_);
                    leanh::lean_dec(v_i_809_);
                    leanh::lean_dec_ref(v_entries_808_);
                    leanh::lean_dec_ref(v_k_807_);
                    v_a_828_ = leanh::lean_ctor_get(v___x_824_, 0);
                    v_isSharedCheck_835_ = (!leanh::lean_is_exclusive(v___x_824_)) as u8;
                    if v_isSharedCheck_835_ == 0 {
                        v___x_830_ = v___x_824_;
                        v_isShared_831_ = v_isSharedCheck_835_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_828_);
                        leanh::lean_dec(v___x_824_);
                        v___x_830_ = leanh::lean_box(0);
                        v_isShared_831_ = v_isSharedCheck_835_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_831_ == 0 {
                    v___x_833_ = v___x_830_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_834_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_834_, 0, v_a_828_);
                    v___x_833_ = v_reuseFailAlloc_834_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_833_;
            }
            4 => {
                v___x_843_ =
                    l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__1;
                v_baseUserName_817_ = v___x_843_;
                v_e_818_ = v___y_838_;
                v_type_819_ = v___y_837_;
                v___y_820_ = v___y_839_;
                v___y_821_ = v___y_840_;
                v___y_822_ = v___y_841_;
                v___y_823_ = v___y_842_;
                state = 1;
                continue;
            }
            5 => {
                if v_modified_850_ == 0 {
                    leanh::lean_inc_ref(v_expr_848_);
                    leanh::lean_inc_ref(v_type_849_);
                    v___y_837_ = v_type_849_;
                    v___y_838_ = v_expr_848_;
                    v___y_839_ = v___y_852_;
                    v___y_840_ = v___y_853_;
                    v___y_841_ = v___y_854_;
                    v___y_842_ = v___y_855_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc_ref(v_type_849_);
                    v___x_856_ = l_Lean_Meta_isTypeCorrect(
                        v_type_849_,
                        v___y_852_,
                        v___y_853_,
                        v___y_854_,
                        v___y_855_,
                    );
                    if leanh::lean_obj_tag(v___x_856_) == 0 {
                        v_a_857_ = leanh::lean_ctor_get(v___x_856_, 0);
                        leanh::lean_inc(v_a_857_);
                        leanh::lean_dec_ref_known(v___x_856_, 1);
                        v___x_858_ = (leanh::lean_unbox(v_a_857_) as u8);
                        leanh::lean_dec(v_a_857_);
                        if v___x_858_ == 0 {
                            v___x_859_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3_once), _init_l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___closed__3);
                            v_sz_860_ = lean_array_size(v_entries_808_);
                            v___x_861_ = 0usize;
                            leanh::lean_inc_ref(v_entries_808_);
                            v___x_862_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__1(v_sz_860_, v___x_861_, v_entries_808_);
                            v___x_863_ = lean_array_to_list(v___x_862_);
                            v___x_864_ = leanh::lean_box(0);
                            v___x_865_ = l_List_mapTR_loop___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__2(v___x_863_, v___x_864_);
                            v___x_866_ = l_Lean_MessageData_ofList(v___x_865_);
                            v___x_867_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_867_, 0, v___x_859_);
                            leanh::lean_ctor_set(v___x_867_, 1, v___x_866_);
                            v___x_868_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v___x_867_, v___y_852_, v___y_853_, v___y_854_, v___y_855_);
                            if leanh::lean_obj_tag(v___x_868_) == 0 {
                                leanh::lean_dec_ref_known(v___x_868_, 1);
                                leanh::lean_inc_ref(v_expr_848_);
                                leanh::lean_inc_ref(v_type_849_);
                                v___y_837_ = v_type_849_;
                                v___y_838_ = v_expr_848_;
                                v___y_839_ = v___y_852_;
                                v___y_840_ = v___y_853_;
                                v___y_841_ = v___y_854_;
                                v___y_842_ = v___y_855_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_fvars_810_);
                                leanh::lean_dec(v_i_809_);
                                leanh::lean_dec_ref(v_entries_808_);
                                leanh::lean_dec_ref(v_k_807_);
                                v_a_869_ = leanh::lean_ctor_get(v___x_868_, 0);
                                v_isSharedCheck_876_ =
                                    (!leanh::lean_is_exclusive(v___x_868_)) as u8;
                                if v_isSharedCheck_876_ == 0 {
                                    v___x_871_ = v___x_868_;
                                    v_isShared_872_ = v_isSharedCheck_876_;
                                    state = 6;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_869_);
                                    leanh::lean_dec(v___x_868_);
                                    v___x_871_ = leanh::lean_box(0);
                                    v_isShared_872_ = v_isSharedCheck_876_;
                                    state = 6;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_inc_ref(v_expr_848_);
                            leanh::lean_inc_ref(v_type_849_);
                            v___y_837_ = v_type_849_;
                            v___y_838_ = v_expr_848_;
                            v___y_839_ = v___y_852_;
                            v___y_840_ = v___y_853_;
                            v___y_841_ = v___y_854_;
                            v___y_842_ = v___y_855_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_fvars_810_);
                        leanh::lean_dec(v_i_809_);
                        leanh::lean_dec_ref(v_entries_808_);
                        leanh::lean_dec_ref(v_k_807_);
                        v_a_877_ = leanh::lean_ctor_get(v___x_856_, 0);
                        v_isSharedCheck_884_ = (!leanh::lean_is_exclusive(v___x_856_)) as u8;
                        if v_isSharedCheck_884_ == 0 {
                            v___x_879_ = v___x_856_;
                            v_isShared_880_ = v_isSharedCheck_884_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_877_);
                            leanh::lean_dec(v___x_856_);
                            v___x_879_ = leanh::lean_box(0);
                            v_isShared_880_ = v_isSharedCheck_884_;
                            state = 8;
                            continue;
                        }
                    }
                }
            }
            6 => {
                if v_isShared_872_ == 0 {
                    v___x_874_ = v___x_871_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_875_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_875_, 0, v_a_869_);
                    v___x_874_ = v_reuseFailAlloc_875_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_874_;
            }
            8 => {
                if v_isShared_880_ == 0 {
                    v___x_882_ = v___x_879_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_883_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_883_, 0, v_a_877_);
                    v___x_882_ = v_reuseFailAlloc_883_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_882_;
            }
            10 => {
                if v_isShared_896_ == 0 {
                    v___x_898_ = v___x_895_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_899_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_899_, 0, v_a_893_);
                    v___x_898_ = v_reuseFailAlloc_899_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_898_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___lam__0(
    mut v_i_901_: *mut leanh::LeanObject,
    mut v_e_902_: *mut leanh::LeanObject,
    mut v_entries_903_: *mut leanh::LeanObject,
    mut v_fvars_904_: *mut leanh::LeanObject,
    mut v_k_905_: *mut leanh::LeanObject,
    mut v_x_906_: *mut leanh::LeanObject,
    mut v___y_907_: *mut leanh::LeanObject,
    mut v___y_908_: *mut leanh::LeanObject,
    mut v___y_909_: *mut leanh::LeanObject,
    mut v___y_910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_921_: u8 = 0;
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_912_ = leanh::lean_unsigned_to_nat(1);
                v___x_913_ = lean_nat_add(v_i_901_, v___x_912_);
                leanh::lean_inc(v___x_913_);
                v___x_914_ = l_Lean_Meta_GeneralizeTelescope_updateTypes(
                    v_e_902_,
                    v_x_906_,
                    v_entries_903_,
                    v___x_913_,
                    v___y_907_,
                    v___y_908_,
                    v___y_909_,
                    v___y_910_,
                );
                if leanh::lean_obj_tag(v___x_914_) == 0 {
                    v_a_915_ = leanh::lean_ctor_get(v___x_914_, 0);
                    leanh::lean_inc(v_a_915_);
                    leanh::lean_dec_ref_known(v___x_914_, 1);
                    v___x_916_ = lean_array_push(v_fvars_904_, v_x_906_);
                    v___x_917_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(
                        v_k_905_, v_a_915_, v___x_913_, v___x_916_, v___y_907_, v___y_908_,
                        v___y_909_, v___y_910_,
                    );
                    return v___x_917_;
                } else {
                    leanh::lean_dec(v___x_913_);
                    leanh::lean_dec_ref(v_x_906_);
                    leanh::lean_dec_ref(v_k_905_);
                    leanh::lean_dec_ref(v_fvars_904_);
                    v_a_918_ = leanh::lean_ctor_get(v___x_914_, 0);
                    v_isSharedCheck_925_ = (!leanh::lean_is_exclusive(v___x_914_)) as u8;
                    if v_isSharedCheck_925_ == 0 {
                        v___x_920_ = v___x_914_;
                        v_isShared_921_ = v_isSharedCheck_925_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_918_);
                        leanh::lean_dec(v___x_914_);
                        v___x_920_ = leanh::lean_box(0);
                        v_isShared_921_ = v_isSharedCheck_925_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_921_ == 0 {
                    v___x_923_ = v___x_920_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_924_, 0, v_a_918_);
                    v___x_923_ = v_reuseFailAlloc_924_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg___boxed(
    mut v_k_926_: *mut leanh::LeanObject,
    mut v_entries_927_: *mut leanh::LeanObject,
    mut v_i_928_: *mut leanh::LeanObject,
    mut v_fvars_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_935_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(
        v_k_926_,
        v_entries_927_,
        v_i_928_,
        v_fvars_929_,
        v_a_930_,
        v_a_931_,
        v_a_932_,
        v_a_933_,
    );
    leanh::lean_dec(v_a_933_);
    leanh::lean_dec_ref(v_a_932_);
    leanh::lean_dec(v_a_931_);
    leanh::lean_dec_ref(v_a_930_);
    return v_res_935_;
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(
    mut v_00_u03b1_936_: *mut leanh::LeanObject,
    mut v_k_937_: *mut leanh::LeanObject,
    mut v_entries_938_: *mut leanh::LeanObject,
    mut v_i_939_: *mut leanh::LeanObject,
    mut v_fvars_940_: *mut leanh::LeanObject,
    mut v_a_941_: *mut leanh::LeanObject,
    mut v_a_942_: *mut leanh::LeanObject,
    mut v_a_943_: *mut leanh::LeanObject,
    mut v_a_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(
        v_k_937_,
        v_entries_938_,
        v_i_939_,
        v_fvars_940_,
        v_a_941_,
        v_a_942_,
        v_a_943_,
        v_a_944_,
    );
    return v___x_946_;
}
pub unsafe fn l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___boxed(
    mut v_00_u03b1_947_: *mut leanh::LeanObject,
    mut v_k_948_: *mut leanh::LeanObject,
    mut v_entries_949_: *mut leanh::LeanObject,
    mut v_i_950_: *mut leanh::LeanObject,
    mut v_fvars_951_: *mut leanh::LeanObject,
    mut v_a_952_: *mut leanh::LeanObject,
    mut v_a_953_: *mut leanh::LeanObject,
    mut v_a_954_: *mut leanh::LeanObject,
    mut v_a_955_: *mut leanh::LeanObject,
    mut v_a_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux(
        v_00_u03b1_947_,
        v_k_948_,
        v_entries_949_,
        v_i_950_,
        v_fvars_951_,
        v_a_952_,
        v_a_953_,
        v_a_954_,
        v_a_955_,
    );
    leanh::lean_dec(v_a_955_);
    leanh::lean_dec_ref(v_a_954_);
    leanh::lean_dec(v_a_953_);
    leanh::lean_dec_ref(v_a_952_);
    return v_res_957_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(
    mut v_00_u03b1_958_: *mut leanh::LeanObject,
    mut v_name_959_: *mut leanh::LeanObject,
    mut v_bi_960_: u8,
    mut v_type_961_: *mut leanh::LeanObject,
    mut v_k_962_: *mut leanh::LeanObject,
    mut v_kind_963_: u8,
    mut v___y_964_: *mut leanh::LeanObject,
    mut v___y_965_: *mut leanh::LeanObject,
    mut v___y_966_: *mut leanh::LeanObject,
    mut v___y_967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_969_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___redArg(v_name_959_, v_bi_960_, v_type_961_, v_k_962_, v_kind_963_, v___y_964_, v___y_965_, v___y_966_, v___y_967_);
    return v___x_969_;
}
pub unsafe fn l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0___boxed(
    mut v_00_u03b1_970_: *mut leanh::LeanObject,
    mut v_name_971_: *mut leanh::LeanObject,
    mut v_bi_972_: *mut leanh::LeanObject,
    mut v_type_973_: *mut leanh::LeanObject,
    mut v_k_974_: *mut leanh::LeanObject,
    mut v_kind_975_: *mut leanh::LeanObject,
    mut v___y_976_: *mut leanh::LeanObject,
    mut v___y_977_: *mut leanh::LeanObject,
    mut v___y_978_: *mut leanh::LeanObject,
    mut v___y_979_: *mut leanh::LeanObject,
    mut v___y_980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_bi_boxed_981_: u8 = 0;
    let mut v_kind_boxed_982_: u8 = 0;
    let mut v_res_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_bi_boxed_981_ = (leanh::lean_unbox(v_bi_972_) as u8);
    v_kind_boxed_982_ = (leanh::lean_unbox(v_kind_975_) as u8);
    v_res_983_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0_spec__0(v_00_u03b1_970_, v_name_971_, v_bi_boxed_981_, v_type_973_, v_k_974_, v_kind_boxed_982_, v___y_976_, v___y_977_, v___y_978_, v___y_979_);
    leanh::lean_dec(v___y_979_);
    leanh::lean_dec_ref(v___y_978_);
    leanh::lean_dec(v___y_977_);
    leanh::lean_dec_ref(v___y_976_);
    return v_res_983_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(
    mut v_00_u03b1_984_: *mut leanh::LeanObject,
    mut v_name_985_: *mut leanh::LeanObject,
    mut v_type_986_: *mut leanh::LeanObject,
    mut v_k_987_: *mut leanh::LeanObject,
    mut v___y_988_: *mut leanh::LeanObject,
    mut v___y_989_: *mut leanh::LeanObject,
    mut v___y_990_: *mut leanh::LeanObject,
    mut v___y_991_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___redArg(v_name_985_, v_type_986_, v_k_987_, v___y_988_, v___y_989_, v___y_990_, v___y_991_);
    return v___x_993_;
}
pub unsafe fn l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0___boxed(
    mut v_00_u03b1_994_: *mut leanh::LeanObject,
    mut v_name_995_: *mut leanh::LeanObject,
    mut v_type_996_: *mut leanh::LeanObject,
    mut v_k_997_: *mut leanh::LeanObject,
    mut v___y_998_: *mut leanh::LeanObject,
    mut v___y_999_: *mut leanh::LeanObject,
    mut v___y_1000_: *mut leanh::LeanObject,
    mut v___y_1001_: *mut leanh::LeanObject,
    mut v___y_1002_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ = l_Lean_Meta_withLocalDeclD___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__0(v_00_u03b1_994_, v_name_995_, v_type_996_, v_k_997_, v___y_998_, v___y_999_, v___y_1000_, v___y_1001_);
    leanh::lean_dec(v___y_1001_);
    leanh::lean_dec_ref(v___y_1000_);
    leanh::lean_dec(v___y_999_);
    leanh::lean_dec_ref(v___y_998_);
    return v_res_1003_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(
    mut v_00_u03b1_1004_: *mut leanh::LeanObject,
    mut v_msg_1005_: *mut leanh::LeanObject,
    mut v___y_1006_: *mut leanh::LeanObject,
    mut v___y_1007_: *mut leanh::LeanObject,
    mut v___y_1008_: *mut leanh::LeanObject,
    mut v___y_1009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1011_ = l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___redArg(v_msg_1005_, v___y_1006_, v___y_1007_, v___y_1008_, v___y_1009_);
    return v___x_1011_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3___boxed(
    mut v_00_u03b1_1012_: *mut leanh::LeanObject,
    mut v_msg_1013_: *mut leanh::LeanObject,
    mut v___y_1014_: *mut leanh::LeanObject,
    mut v___y_1015_: *mut leanh::LeanObject,
    mut v___y_1016_: *mut leanh::LeanObject,
    mut v___y_1017_: *mut leanh::LeanObject,
    mut v___y_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1019_ =
        l_Lean_throwError___at___00Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux_spec__3(
            v_00_u03b1_1012_,
            v_msg_1013_,
            v___y_1014_,
            v___y_1015_,
            v___y_1016_,
            v___y_1017_,
        );
    leanh::lean_dec(v___y_1017_);
    leanh::lean_dec_ref(v___y_1016_);
    leanh::lean_dec(v___y_1015_);
    leanh::lean_dec_ref(v___y_1014_);
    return v_res_1019_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(
    mut v_e_1020_: *mut leanh::LeanObject,
    mut v___y_1021_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1023_: u8 = 0;
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1037_: u8 = 0;
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1043_: u8 = 0;
    let mut v_unused_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1023_ = l_Lean_Expr_hasMVar(v_e_1020_);
                if v___x_1023_ == 0 {
                    v___x_1024_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1024_, 0, v_e_1020_);
                    return v___x_1024_;
                } else {
                    v___x_1025_ = lean_st_ref_get(v___y_1021_);
                    v_mctx_1026_ = leanh::lean_ctor_get(v___x_1025_, 0);
                    leanh::lean_inc_ref(v_mctx_1026_);
                    leanh::lean_dec(v___x_1025_);
                    v___x_1027_ = l_Lean_instantiateMVarsCore(v_mctx_1026_, v_e_1020_);
                    v_fst_1028_ = leanh::lean_ctor_get(v___x_1027_, 0);
                    leanh::lean_inc(v_fst_1028_);
                    v_snd_1029_ = leanh::lean_ctor_get(v___x_1027_, 1);
                    leanh::lean_inc(v_snd_1029_);
                    leanh::lean_dec_ref(v___x_1027_);
                    v___x_1030_ = lean_st_ref_take(v___y_1021_);
                    v_cache_1031_ = leanh::lean_ctor_get(v___x_1030_, 1);
                    v_zetaDeltaFVarIds_1032_ = leanh::lean_ctor_get(v___x_1030_, 2);
                    v_postponed_1033_ = leanh::lean_ctor_get(v___x_1030_, 3);
                    v_diag_1034_ = leanh::lean_ctor_get(v___x_1030_, 4);
                    v_isSharedCheck_1043_ = (!leanh::lean_is_exclusive(v___x_1030_)) as u8;
                    if v_isSharedCheck_1043_ == 0 {
                        v_unused_1044_ = leanh::lean_ctor_get(v___x_1030_, 0);
                        leanh::lean_dec(v_unused_1044_);
                        v___x_1036_ = v___x_1030_;
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_1034_);
                        leanh::lean_inc(v_postponed_1033_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_1032_);
                        leanh::lean_inc(v_cache_1031_);
                        leanh::lean_dec(v___x_1030_);
                        v___x_1036_ = leanh::lean_box(0);
                        v_isShared_1037_ = v_isSharedCheck_1043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1037_ == 0 {
                    leanh::lean_ctor_set(v___x_1036_, 0, v_snd_1029_);
                    v___x_1039_ = v___x_1036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1042_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_snd_1029_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_cache_1031_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1042_,
                        2,
                        v_zetaDeltaFVarIds_1032_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 3, v_postponed_1033_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1042_, 4, v_diag_1034_);
                    v___x_1039_ = v_reuseFailAlloc_1042_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1040_ = lean_st_ref_set(v___y_1021_, v___x_1039_);
                v___x_1041_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1041_, 0, v_fst_1028_);
                return v___x_1041_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg___boxed(
    mut v_e_1045_: *mut leanh::LeanObject,
    mut v___y_1046_: *mut leanh::LeanObject,
    mut v___y_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1048_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(
        v_e_1045_,
        v___y_1046_,
    );
    leanh::lean_dec(v___y_1046_);
    return v_res_1048_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(
    mut v_e_1049_: *mut leanh::LeanObject,
    mut v___y_1050_: *mut leanh::LeanObject,
    mut v___y_1051_: *mut leanh::LeanObject,
    mut v___y_1052_: *mut leanh::LeanObject,
    mut v___y_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(
        v_e_1049_,
        v___y_1051_,
    );
    return v___x_1055_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___boxed(
    mut v_e_1056_: *mut leanh::LeanObject,
    mut v___y_1057_: *mut leanh::LeanObject,
    mut v___y_1058_: *mut leanh::LeanObject,
    mut v___y_1059_: *mut leanh::LeanObject,
    mut v___y_1060_: *mut leanh::LeanObject,
    mut v___y_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1062_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0(
        v_e_1056_,
        v___y_1057_,
        v___y_1058_,
        v___y_1059_,
        v___y_1060_,
    );
    leanh::lean_dec(v___y_1060_);
    leanh::lean_dec_ref(v___y_1059_);
    leanh::lean_dec(v___y_1058_);
    leanh::lean_dec_ref(v___y_1057_);
    return v_res_1062_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(
    mut v_sz_1063_: usize,
    mut v_i_1064_: usize,
    mut v_bs_1065_: *mut leanh::LeanObject,
    mut v___y_1066_: *mut leanh::LeanObject,
    mut v___y_1067_: *mut leanh::LeanObject,
    mut v___y_1068_: *mut leanh::LeanObject,
    mut v___y_1069_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1071_: u8 = 0;
    let mut v___x_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1080_: u8 = 0;
    let mut v___x_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: usize = 0;
    let mut v___x_1083_: usize = 0;
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1089_: u8 = 0;
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1093_: u8 = 0;
    let mut v_a_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1071_ = lean_usize_dec_lt(v_i_1064_, v_sz_1063_);
                if v___x_1071_ == 0 {
                    v___x_1072_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1072_, 0, v_bs_1065_);
                    return v___x_1072_;
                } else {
                    v_v_1073_ = lean_array_uget(v_bs_1065_, v_i_1064_);
                    leanh::lean_inc(v___y_1069_);
                    leanh::lean_inc_ref(v___y_1068_);
                    leanh::lean_inc(v___y_1067_);
                    leanh::lean_inc_ref(v___y_1066_);
                    leanh::lean_inc(v_v_1073_);
                    v___x_1074_ = lean_infer_type(
                        v_v_1073_,
                        v___y_1066_,
                        v___y_1067_,
                        v___y_1068_,
                        v___y_1069_,
                    );
                    if leanh::lean_obj_tag(v___x_1074_) == 0 {
                        v_a_1075_ = leanh::lean_ctor_get(v___x_1074_, 0);
                        leanh::lean_inc(v_a_1075_);
                        leanh::lean_dec_ref_known(v___x_1074_, 1);
                        v___x_1076_ = l_Lean_instantiateMVars___at___00Lean_Meta_generalizeTelescope_spec__0___redArg(v_a_1075_, v___y_1067_);
                        if leanh::lean_obj_tag(v___x_1076_) == 0 {
                            v_a_1077_ = leanh::lean_ctor_get(v___x_1076_, 0);
                            leanh::lean_inc(v_a_1077_);
                            leanh::lean_dec_ref_known(v___x_1076_, 1);
                            v___x_1078_ = leanh::lean_unsigned_to_nat(0);
                            v_bs_x27_1079_ = lean_array_uset(v_bs_1065_, v_i_1064_, v___x_1078_);
                            v___x_1080_ = 0;
                            v___x_1081_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                            leanh::lean_ctor_set(v___x_1081_, 0, v_v_1073_);
                            leanh::lean_ctor_set(v___x_1081_, 1, v_a_1077_);
                            leanh::lean_ctor_set_uint8(
                                v___x_1081_,
                                (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                                v___x_1080_,
                            );
                            v___x_1082_ = 1usize;
                            v___x_1083_ = lean_usize_add(v_i_1064_, v___x_1082_);
                            v___x_1084_ = lean_array_uset(v_bs_x27_1079_, v_i_1064_, v___x_1081_);
                            v_i_1064_ = v___x_1083_;
                            v_bs_1065_ = v___x_1084_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_v_1073_);
                            leanh::lean_dec_ref(v_bs_1065_);
                            v_a_1086_ = leanh::lean_ctor_get(v___x_1076_, 0);
                            v_isSharedCheck_1093_ =
                                (!leanh::lean_is_exclusive(v___x_1076_)) as u8;
                            if v_isSharedCheck_1093_ == 0 {
                                v___x_1088_ = v___x_1076_;
                                v_isShared_1089_ = v_isSharedCheck_1093_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1086_);
                                leanh::lean_dec(v___x_1076_);
                                v___x_1088_ = leanh::lean_box(0);
                                v_isShared_1089_ = v_isSharedCheck_1093_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_1073_);
                        leanh::lean_dec_ref(v_bs_1065_);
                        v_a_1094_ = leanh::lean_ctor_get(v___x_1074_, 0);
                        v_isSharedCheck_1101_ =
                            (!leanh::lean_is_exclusive(v___x_1074_)) as u8;
                        if v_isSharedCheck_1101_ == 0 {
                            v___x_1096_ = v___x_1074_;
                            v_isShared_1097_ = v_isSharedCheck_1101_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1094_);
                            leanh::lean_dec(v___x_1074_);
                            v___x_1096_ = leanh::lean_box(0);
                            v_isShared_1097_ = v_isSharedCheck_1101_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_1089_ == 0 {
                    v___x_1091_ = v___x_1088_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1092_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_a_1086_);
                    v___x_1091_ = v_reuseFailAlloc_1092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1091_;
            }
            3 => {
                if v_isShared_1097_ == 0 {
                    v___x_1099_ = v___x_1096_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1100_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1100_, 0, v_a_1094_);
                    v___x_1099_ = v_reuseFailAlloc_1100_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1___boxed(
    mut v_sz_1102_: *mut leanh::LeanObject,
    mut v_i_1103_: *mut leanh::LeanObject,
    mut v_bs_1104_: *mut leanh::LeanObject,
    mut v___y_1105_: *mut leanh::LeanObject,
    mut v___y_1106_: *mut leanh::LeanObject,
    mut v___y_1107_: *mut leanh::LeanObject,
    mut v___y_1108_: *mut leanh::LeanObject,
    mut v___y_1109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1110_: usize = 0;
    let mut v_i_boxed_1111_: usize = 0;
    let mut v_res_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1110_ = leanh::lean_unbox_usize(v_sz_1102_);
    leanh::lean_dec(v_sz_1102_);
    v_i_boxed_1111_ = leanh::lean_unbox_usize(v_i_1103_);
    leanh::lean_dec(v_i_1103_);
    v_res_1112_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_boxed_1110_, v_i_boxed_1111_, v_bs_1104_, v___y_1105_, v___y_1106_, v___y_1107_, v___y_1108_);
    leanh::lean_dec(v___y_1108_);
    leanh::lean_dec_ref(v___y_1107_);
    leanh::lean_dec(v___y_1106_);
    leanh::lean_dec_ref(v___y_1105_);
    return v_res_1112_;
}
pub unsafe fn l_Lean_Meta_generalizeTelescope___redArg(
    mut v_es_1115_: *mut leanh::LeanObject,
    mut v_k_1116_: *mut leanh::LeanObject,
    mut v_a_1117_: *mut leanh::LeanObject,
    mut v_a_1118_: *mut leanh::LeanObject,
    mut v_a_1119_: *mut leanh::LeanObject,
    mut v_a_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1122_: usize = 0;
    let mut v___x_1123_: usize = 0;
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1132_: u8 = 0;
    let mut v___x_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1136_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_1122_ = lean_array_size(v_es_1115_);
                v___x_1123_ = 0usize;
                v___x_1124_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_generalizeTelescope_spec__1(v_sz_1122_, v___x_1123_, v_es_1115_, v_a_1117_, v_a_1118_, v_a_1119_, v_a_1120_);
                if leanh::lean_obj_tag(v___x_1124_) == 0 {
                    v_a_1125_ = leanh::lean_ctor_get(v___x_1124_, 0);
                    leanh::lean_inc(v_a_1125_);
                    leanh::lean_dec_ref_known(v___x_1124_, 1);
                    v___x_1126_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1127_ = l_Lean_Meta_generalizeTelescope___redArg___closed__0;
                    v___x_1128_ = l_Lean_Meta_GeneralizeTelescope_generalizeTelescopeAux___redArg(
                        v_k_1116_,
                        v_a_1125_,
                        v___x_1126_,
                        v___x_1127_,
                        v_a_1117_,
                        v_a_1118_,
                        v_a_1119_,
                        v_a_1120_,
                    );
                    return v___x_1128_;
                } else {
                    leanh::lean_dec_ref(v_k_1116_);
                    v_a_1129_ = leanh::lean_ctor_get(v___x_1124_, 0);
                    v_isSharedCheck_1136_ = (!leanh::lean_is_exclusive(v___x_1124_)) as u8;
                    if v_isSharedCheck_1136_ == 0 {
                        v___x_1131_ = v___x_1124_;
                        v_isShared_1132_ = v_isSharedCheck_1136_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1129_);
                        leanh::lean_dec(v___x_1124_);
                        v___x_1131_ = leanh::lean_box(0);
                        v_isShared_1132_ = v_isSharedCheck_1136_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1132_ == 0 {
                    v___x_1134_ = v___x_1131_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1135_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
                    v___x_1134_ = v_reuseFailAlloc_1135_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1134_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_generalizeTelescope___redArg___boxed(
    mut v_es_1137_: *mut leanh::LeanObject,
    mut v_k_1138_: *mut leanh::LeanObject,
    mut v_a_1139_: *mut leanh::LeanObject,
    mut v_a_1140_: *mut leanh::LeanObject,
    mut v_a_1141_: *mut leanh::LeanObject,
    mut v_a_1142_: *mut leanh::LeanObject,
    mut v_a_1143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1144_ = l_Lean_Meta_generalizeTelescope___redArg(
        v_es_1137_, v_k_1138_, v_a_1139_, v_a_1140_, v_a_1141_, v_a_1142_,
    );
    leanh::lean_dec(v_a_1142_);
    leanh::lean_dec_ref(v_a_1141_);
    leanh::lean_dec(v_a_1140_);
    leanh::lean_dec_ref(v_a_1139_);
    return v_res_1144_;
}
pub unsafe fn l_Lean_Meta_generalizeTelescope(
    mut v_00_u03b1_1145_: *mut leanh::LeanObject,
    mut v_es_1146_: *mut leanh::LeanObject,
    mut v_k_1147_: *mut leanh::LeanObject,
    mut v_a_1148_: *mut leanh::LeanObject,
    mut v_a_1149_: *mut leanh::LeanObject,
    mut v_a_1150_: *mut leanh::LeanObject,
    mut v_a_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1153_ = l_Lean_Meta_generalizeTelescope___redArg(
        v_es_1146_, v_k_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_,
    );
    return v___x_1153_;
}
pub unsafe fn l_Lean_Meta_generalizeTelescope___boxed(
    mut v_00_u03b1_1154_: *mut leanh::LeanObject,
    mut v_es_1155_: *mut leanh::LeanObject,
    mut v_k_1156_: *mut leanh::LeanObject,
    mut v_a_1157_: *mut leanh::LeanObject,
    mut v_a_1158_: *mut leanh::LeanObject,
    mut v_a_1159_: *mut leanh::LeanObject,
    mut v_a_1160_: *mut leanh::LeanObject,
    mut v_a_1161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1162_ = l_Lean_Meta_generalizeTelescope(
        v_00_u03b1_1154_,
        v_es_1155_,
        v_k_1156_,
        v_a_1157_,
        v_a_1158_,
        v_a_1159_,
        v_a_1160_,
    );
    leanh::lean_dec(v_a_1160_);
    leanh::lean_dec_ref(v_a_1159_);
    leanh::lean_dec(v_a_1158_);
    leanh::lean_dec_ref(v_a_1157_);
    return v_res_1162_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_GeneralizeTelescope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_KAbstract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_GeneralizeTelescope(
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
pub unsafe fn initialize_Lean_Meta_GeneralizeTelescope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_KAbstract(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Check(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_GeneralizeTelescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_GeneralizeTelescope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_GeneralizeTelescope(builtin);
}
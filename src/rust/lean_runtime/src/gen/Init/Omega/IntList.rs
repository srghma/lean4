// Lean compiler output
// Module: Init.Omega.IntList
// Imports: Init.Data.Int.DivMod.Bootstrap Init.Data.Nat.Gcd Init.Data.Int.Lemmas Init.Data.Int.Order Init.Data.Nat.Dvd Init.PropLemmas Init.RCases
use crate::r#gen::Init::Data::Int::DivMod::Basic::l_Int_bmod;
use crate::r#gen::Init::Data::Int::DivMod::Bootstrap::{
    initialize_Init_Data_Int_DivMod_Bootstrap, runtime_initialize_Init_Data_Int_DivMod_Bootstrap,
};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::List::Basic::{l_List_mapTR_loop___redArg, l_List_reverse___redArg};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Nat::Gcd::{
    initialize_Init_Data_Nat_Gcd, runtime_initialize_Init_Data_Nat_Gcd,
};
use crate::r#gen::Init::GetElem::l_List_get_x3fInternal___redArg;
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs,
    lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::lean_int_ediv;
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Omega_IntList_get___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Omega_IntList_get___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Omega_IntList_instAdd___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_IntList_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_IntList_instAdd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instAdd___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_IntList_instAdd: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instAdd___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_IntList_instMul___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_IntList_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_IntList_instMul___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instMul___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_IntList_instMul: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instMul___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_IntList_instNeg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_IntList_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_IntList_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_IntList_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instNeg___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_IntList_instSub___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_IntList_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_IntList_instSub___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instSub___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_IntList_instSub: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instSub___closed__0_value) as *mut LeanObject;
pub static l_Lean_Omega_IntList_instHMulInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Omega_IntList_instHMulInt___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Omega_IntList_instHMulInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instHMulInt___closed__0_value) as *mut LeanObject;
pub static mut l_Lean_Omega_IntList_instHMulInt: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Omega_IntList_instHMulInt___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(
    mut v_x_529_: *mut LeanObject,
    mut v_x_530_: *mut LeanObject,
    mut v_h__1_531_: *mut LeanObject,
    mut v_h__2_532_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_529_) == 0 {
        if lean_obj_tag(v_x_530_) == 0 {
            let mut v___x_533_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_534_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_532_);
            v___x_533_ = lean_box(0);
            v___x_534_ = lean_apply_1(v_h__1_531_, v___x_533_);
            return v___x_534_;
        } else {
            let mut v___x_535_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_531_);
            v___x_535_ = lean_apply_3(v_h__2_532_, v_x_529_, v_x_530_, lean_box(0));
            return v___x_535_;
        }
    } else {
        let mut v___x_536_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_531_);
        v___x_536_ = lean_apply_3(v_h__2_532_, v_x_529_, v_x_530_, lean_box(0));
        return v___x_536_;
    }
}
pub unsafe fn l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter(
    mut v_00_u03b1_537_: *mut LeanObject,
    mut v_00_u03b2_538_: *mut LeanObject,
    mut v_motive_539_: *mut LeanObject,
    mut v_x_540_: *mut LeanObject,
    mut v_x_541_: *mut LeanObject,
    mut v_h__1_542_: *mut LeanObject,
    mut v_h__2_543_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_540_) == 0 {
        if lean_obj_tag(v_x_541_) == 0 {
            let mut v___x_544_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_545_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_543_);
            v___x_544_ = lean_box(0);
            v___x_545_ = lean_apply_1(v_h__1_542_, v___x_544_);
            return v___x_545_;
        } else {
            let mut v___x_546_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_542_);
            v___x_546_ = lean_apply_3(v_h__2_543_, v_x_540_, v_x_541_, lean_box(0));
            return v___x_546_;
        }
    } else {
        let mut v___x_547_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_542_);
        v___x_547_ = lean_apply_3(v_h__2_543_, v_x_540_, v_x_541_, lean_box(0));
        return v___x_547_;
    }
}
pub unsafe fn l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(
    mut v_x_548_: *mut LeanObject,
    mut v_x_549_: *mut LeanObject,
    mut v_h__1_550_: *mut LeanObject,
    mut v_h__2_551_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_548_) == 1 {
        if lean_obj_tag(v_x_549_) == 1 {
            let mut v_val_552_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_553_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_554_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_551_);
            v_val_552_ = lean_ctor_get(v_x_548_, 0);
            lean_inc(v_val_552_);
            lean_dec_ref_known(v_x_548_, 1);
            v_val_553_ = lean_ctor_get(v_x_549_, 0);
            lean_inc(v_val_553_);
            lean_dec_ref_known(v_x_549_, 1);
            v___x_554_ = lean_apply_2(v_h__1_550_, v_val_552_, v_val_553_);
            return v___x_554_;
        } else {
            let mut v___x_555_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_550_);
            v___x_555_ = lean_apply_3(v_h__2_551_, v_x_548_, v_x_549_, lean_box(0));
            return v___x_555_;
        }
    } else {
        let mut v___x_556_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_550_);
        v___x_556_ = lean_apply_3(v_h__2_551_, v_x_548_, v_x_549_, lean_box(0));
        return v___x_556_;
    }
}
pub unsafe fn l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter(
    mut v_00_u03b1_557_: *mut LeanObject,
    mut v_00_u03b2_558_: *mut LeanObject,
    mut v_motive_559_: *mut LeanObject,
    mut v_x_560_: *mut LeanObject,
    mut v_x_561_: *mut LeanObject,
    mut v_h__1_562_: *mut LeanObject,
    mut v_h__2_563_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_560_) == 1 {
        if lean_obj_tag(v_x_561_) == 1 {
            let mut v_val_564_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_565_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_566_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_563_);
            v_val_564_ = lean_ctor_get(v_x_560_, 0);
            lean_inc(v_val_564_);
            lean_dec_ref_known(v_x_560_, 1);
            v_val_565_ = lean_ctor_get(v_x_561_, 0);
            lean_inc(v_val_565_);
            lean_dec_ref_known(v_x_561_, 1);
            v___x_566_ = lean_apply_2(v_h__1_562_, v_val_564_, v_val_565_);
            return v___x_566_;
        } else {
            let mut v___x_567_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_562_);
            v___x_567_ = lean_apply_3(v_h__2_563_, v_x_560_, v_x_561_, lean_box(0));
            return v___x_567_;
        }
    } else {
        let mut v___x_568_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_562_);
        v___x_568_ = lean_apply_3(v_h__2_563_, v_x_560_, v_x_561_, lean_box(0));
        return v___x_568_;
    }
}
pub unsafe fn _init_l_Lean_Omega_IntList_get___closed__0() -> *mut LeanObject {
    let mut v___x_569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_570_: *mut LeanObject = core::ptr::null_mut();
    v___x_569_ = lean_unsigned_to_nat(0);
    v___x_570_ = lean_nat_to_int(v___x_569_);
    return v___x_570_;
}
pub unsafe fn l_Lean_Omega_IntList_get(
    mut v_xs_571_: *mut LeanObject,
    mut v_i_572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    v___x_573_ = l_List_get_x3fInternal___redArg(v_xs_571_, v_i_572_);
    if lean_obj_tag(v___x_573_) == 0 {
        let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
        v___x_574_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
            _init_l_Lean_Omega_IntList_get___closed__0,
        );
        return v___x_574_;
    } else {
        let mut v_val_575_: *mut LeanObject = core::ptr::null_mut();
        v_val_575_ = lean_ctor_get(v___x_573_, 0);
        lean_inc(v_val_575_);
        lean_dec_ref_known(v___x_573_, 1);
        return v_val_575_;
    }
}
pub unsafe fn l_Lean_Omega_IntList_get___boxed(
    mut v_xs_576_: *mut LeanObject,
    mut v_i_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_578_: *mut LeanObject = core::ptr::null_mut();
    v_res_578_ = l_Lean_Omega_IntList_get(v_xs_576_, v_i_577_);
    lean_dec(v_xs_576_);
    return v_res_578_;
}
pub unsafe fn l_Lean_Omega_IntList_set(
    mut v_xs_579_: *mut LeanObject,
    mut v_i_580_: *mut LeanObject,
    mut v_y_581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_583_: u8 = 0;
    let mut v___x_584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_594_: u8 = 0;
    let mut v_zero_595_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_596_: u8 = 0;
    let mut v___x_598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_606_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_xs_579_) == 0 {
                    v_zero_582_ = lean_unsigned_to_nat(0);
                    v_isZero_583_ = lean_nat_dec_eq(v_i_580_, v_zero_582_);
                    if v_isZero_583_ == 1 {
                        v___x_584_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_584_, 0, v_y_581_);
                        lean_ctor_set(v___x_584_, 1, v_xs_579_);
                        return v___x_584_;
                    } else {
                        v_one_585_ = lean_unsigned_to_nat(1);
                        v_n_586_ = lean_nat_sub(v_i_580_, v_one_585_);
                        v___x_587_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                            _init_l_Lean_Omega_IntList_get___closed__0,
                        );
                        v___x_588_ = l_Lean_Omega_IntList_set(v_xs_579_, v_n_586_, v_y_581_);
                        lean_dec(v_n_586_);
                        v___x_589_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_589_, 0, v___x_587_);
                        lean_ctor_set(v___x_589_, 1, v___x_588_);
                        return v___x_589_;
                    }
                } else {
                    v_head_590_ = lean_ctor_get(v_xs_579_, 0);
                    v_tail_591_ = lean_ctor_get(v_xs_579_, 1);
                    v_isSharedCheck_606_ = (!lean_is_exclusive(v_xs_579_)) as u8;
                    if v_isSharedCheck_606_ == 0 {
                        v___x_593_ = v_xs_579_;
                        v_isShared_594_ = v_isSharedCheck_606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_591_);
                        lean_inc(v_head_590_);
                        lean_dec(v_xs_579_);
                        v___x_593_ = lean_box(0);
                        v_isShared_594_ = v_isSharedCheck_606_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_zero_595_ = lean_unsigned_to_nat(0);
                v_isZero_596_ = lean_nat_dec_eq(v_i_580_, v_zero_595_);
                if v_isZero_596_ == 1 {
                    lean_dec(v_head_590_);
                    if v_isShared_594_ == 0 {
                        lean_ctor_set(v___x_593_, 0, v_y_581_);
                        v___x_598_ = v___x_593_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_599_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_599_, 0, v_y_581_);
                        lean_ctor_set(v_reuseFailAlloc_599_, 1, v_tail_591_);
                        v___x_598_ = v_reuseFailAlloc_599_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_one_600_ = lean_unsigned_to_nat(1);
                    v_n_601_ = lean_nat_sub(v_i_580_, v_one_600_);
                    v___x_602_ = l_Lean_Omega_IntList_set(v_tail_591_, v_n_601_, v_y_581_);
                    lean_dec(v_n_601_);
                    if v_isShared_594_ == 0 {
                        lean_ctor_set(v___x_593_, 1, v___x_602_);
                        v___x_604_ = v___x_593_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_605_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_605_, 0, v_head_590_);
                        lean_ctor_set(v_reuseFailAlloc_605_, 1, v___x_602_);
                        v___x_604_ = v_reuseFailAlloc_605_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_598_;
            }
            3 => {
                return v___x_604_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_IntList_set___boxed(
    mut v_xs_607_: *mut LeanObject,
    mut v_i_608_: *mut LeanObject,
    mut v_y_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_610_: *mut LeanObject = core::ptr::null_mut();
    v_res_610_ = l_Lean_Omega_IntList_set(v_xs_607_, v_i_608_, v_y_609_);
    lean_dec(v_i_608_);
    return v_res_610_;
}
pub unsafe fn l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(
    mut v_x_611_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: u8 = 0;
    let mut v___x_617_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_611_) == 0 {
                    v___x_612_ = lean_box(0);
                    return v___x_612_;
                } else {
                    v_head_613_ = lean_ctor_get(v_x_611_, 0);
                    v_tail_614_ = lean_ctor_get(v_x_611_, 1);
                    v___x_615_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                        core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                        _init_l_Lean_Omega_IntList_get___closed__0,
                    );
                    v___x_616_ = lean_int_dec_eq(v_head_613_, v___x_615_);
                    if v___x_616_ == 0 {
                        lean_inc(v_head_613_);
                        v___x_617_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_617_, 0, v_head_613_);
                        return v___x_617_;
                    } else {
                        v_x_611_ = v_tail_614_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0___boxed(
    mut v_x_619_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_620_: *mut LeanObject = core::ptr::null_mut();
    v_res_620_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_x_619_);
    lean_dec(v_x_619_);
    return v_res_620_;
}
pub unsafe fn l_Lean_Omega_IntList_leading(mut v_xs_621_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_622_: *mut LeanObject = core::ptr::null_mut();
    v___x_622_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_xs_621_);
    if lean_obj_tag(v___x_622_) == 0 {
        let mut v___x_623_: *mut LeanObject = core::ptr::null_mut();
        v___x_623_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
            core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
            _init_l_Lean_Omega_IntList_get___closed__0,
        );
        return v___x_623_;
    } else {
        let mut v_val_624_: *mut LeanObject = core::ptr::null_mut();
        v_val_624_ = lean_ctor_get(v___x_622_, 0);
        lean_inc(v_val_624_);
        lean_dec_ref_known(v___x_622_, 1);
        return v_val_624_;
    }
}
pub unsafe fn l_Lean_Omega_IntList_leading___boxed(
    mut v_xs_625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_626_: *mut LeanObject = core::ptr::null_mut();
    v_res_626_ = l_Lean_Omega_IntList_leading(v_xs_625_);
    lean_dec(v_xs_625_);
    return v_res_626_;
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(
    mut v_x_627_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_632_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_639_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_627_) == 0 {
                    return v_x_627_;
                } else {
                    v_head_628_ = lean_ctor_get(v_x_627_, 0);
                    v_tail_629_ = lean_ctor_get(v_x_627_, 1);
                    v_isSharedCheck_639_ = (!lean_is_exclusive(v_x_627_)) as u8;
                    if v_isSharedCheck_639_ == 0 {
                        v___x_631_ = v_x_627_;
                        v_isShared_632_ = v_isSharedCheck_639_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_629_);
                        lean_inc(v_head_628_);
                        lean_dec(v_x_627_);
                        v___x_631_ = lean_box(0);
                        v_isShared_632_ = v_isSharedCheck_639_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_633_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_634_ = lean_int_add(v___x_633_, v_head_628_);
                lean_dec(v_head_628_);
                v___x_635_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_629_);
                if v_isShared_632_ == 0 {
                    lean_ctor_set(v___x_631_, 1, v___x_635_);
                    lean_ctor_set(v___x_631_, 0, v___x_634_);
                    v___x_637_ = v___x_631_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_638_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_638_, 0, v___x_634_);
                    lean_ctor_set(v_reuseFailAlloc_638_, 1, v___x_635_);
                    v___x_637_ = v_reuseFailAlloc_638_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_637_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(
    mut v_x_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_645_: u8 = 0;
    let mut v___x_646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_640_) == 0 {
                    return v_x_640_;
                } else {
                    v_head_641_ = lean_ctor_get(v_x_640_, 0);
                    v_tail_642_ = lean_ctor_get(v_x_640_, 1);
                    v_isSharedCheck_652_ = (!lean_is_exclusive(v_x_640_)) as u8;
                    if v_isSharedCheck_652_ == 0 {
                        v___x_644_ = v_x_640_;
                        v_isShared_645_ = v_isSharedCheck_652_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_642_);
                        lean_inc(v_head_641_);
                        lean_dec(v_x_640_);
                        v___x_644_ = lean_box(0);
                        v_isShared_645_ = v_isSharedCheck_652_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_646_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_647_ = lean_int_add(v___x_646_, v_head_641_);
                lean_dec(v_head_641_);
                v___x_648_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_642_);
                if v_isShared_645_ == 0 {
                    lean_ctor_set(v___x_644_, 1, v___x_648_);
                    lean_ctor_set(v___x_644_, 0, v___x_647_);
                    v___x_650_ = v___x_644_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_651_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_651_, 0, v___x_647_);
                    lean_ctor_set(v_reuseFailAlloc_651_, 1, v___x_648_);
                    v___x_650_ = v_reuseFailAlloc_651_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_650_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(
    mut v_x_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_658_: u8 = 0;
    let mut v___x_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_665_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_653_) == 0 {
                    return v_x_653_;
                } else {
                    v_head_654_ = lean_ctor_get(v_x_653_, 0);
                    v_tail_655_ = lean_ctor_get(v_x_653_, 1);
                    v_isSharedCheck_665_ = (!lean_is_exclusive(v_x_653_)) as u8;
                    if v_isSharedCheck_665_ == 0 {
                        v___x_657_ = v_x_653_;
                        v_isShared_658_ = v_isSharedCheck_665_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_655_);
                        lean_inc(v_head_654_);
                        lean_dec(v_x_653_);
                        v___x_657_ = lean_box(0);
                        v_isShared_658_ = v_isSharedCheck_665_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_659_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_660_ = lean_int_add(v_head_654_, v___x_659_);
                lean_dec(v_head_654_);
                v___x_661_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_655_);
                if v_isShared_658_ == 0 {
                    lean_ctor_set(v___x_657_, 1, v___x_661_);
                    lean_ctor_set(v___x_657_, 0, v___x_660_);
                    v___x_663_ = v___x_657_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_660_);
                    lean_ctor_set(v_reuseFailAlloc_664_, 1, v___x_661_);
                    v___x_663_ = v_reuseFailAlloc_664_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_663_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(
    mut v_x_666_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_671_: u8 = 0;
    let mut v___x_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_678_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_666_) == 0 {
                    return v_x_666_;
                } else {
                    v_head_667_ = lean_ctor_get(v_x_666_, 0);
                    v_tail_668_ = lean_ctor_get(v_x_666_, 1);
                    v_isSharedCheck_678_ = (!lean_is_exclusive(v_x_666_)) as u8;
                    if v_isSharedCheck_678_ == 0 {
                        v___x_670_ = v_x_666_;
                        v_isShared_671_ = v_isSharedCheck_678_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_668_);
                        lean_inc(v_head_667_);
                        lean_dec(v_x_666_);
                        v___x_670_ = lean_box(0);
                        v_isShared_671_ = v_isSharedCheck_678_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_672_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_673_ = lean_int_add(v_head_667_, v___x_672_);
                lean_dec(v_head_667_);
                v___x_674_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_668_);
                if v_isShared_671_ == 0 {
                    lean_ctor_set(v___x_670_, 1, v___x_674_);
                    lean_ctor_set(v___x_670_, 0, v___x_673_);
                    v___x_676_ = v___x_670_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_677_, 0, v___x_673_);
                    lean_ctor_set(v_reuseFailAlloc_677_, 1, v___x_674_);
                    v___x_676_ = v_reuseFailAlloc_677_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_676_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(
    mut v_x_679_: *mut LeanObject,
    mut v_x_680_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_689_: u8 = 0;
    let mut v___x_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_695_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_679_) == 0 {
                    v___x_681_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(v_x_680_);
                    return v___x_681_;
                } else {
                    if lean_obj_tag(v_x_680_) == 0 {
                        v___x_682_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(v_x_679_);
                        return v___x_682_;
                    } else {
                        v_head_683_ = lean_ctor_get(v_x_679_, 0);
                        lean_inc(v_head_683_);
                        v_tail_684_ = lean_ctor_get(v_x_679_, 1);
                        lean_inc(v_tail_684_);
                        lean_dec_ref_known(v_x_679_, 2);
                        v_head_685_ = lean_ctor_get(v_x_680_, 0);
                        v_tail_686_ = lean_ctor_get(v_x_680_, 1);
                        v_isSharedCheck_695_ = (!lean_is_exclusive(v_x_680_)) as u8;
                        if v_isSharedCheck_695_ == 0 {
                            v___x_688_ = v_x_680_;
                            v_isShared_689_ = v_isSharedCheck_695_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_686_);
                            lean_inc(v_head_685_);
                            lean_dec(v_x_680_);
                            v___x_688_ = lean_box(0);
                            v_isShared_689_ = v_isSharedCheck_695_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_690_ = lean_int_add(v_head_683_, v_head_685_);
                lean_dec(v_head_685_);
                lean_dec(v_head_683_);
                v___x_691_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(
                    v_tail_684_,
                    v_tail_686_,
                );
                if v_isShared_689_ == 0 {
                    lean_ctor_set(v___x_688_, 1, v___x_691_);
                    lean_ctor_set(v___x_688_, 0, v___x_690_);
                    v___x_693_ = v___x_688_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_694_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_690_);
                    lean_ctor_set(v_reuseFailAlloc_694_, 1, v___x_691_);
                    v___x_693_ = v_reuseFailAlloc_694_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_693_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_IntList_add(
    mut v_xs_696_: *mut LeanObject,
    mut v_ys_697_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    v___x_698_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_696_, v_ys_697_);
    return v___x_698_;
}
pub unsafe fn l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(
    mut v_x_701_: *mut LeanObject,
    mut v_x_702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v___x_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_715_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_701_) == 0 {
                    lean_dec(v_x_702_);
                    return v_x_701_;
                } else {
                    if lean_obj_tag(v_x_702_) == 0 {
                        return v_x_702_;
                    } else {
                        v_head_703_ = lean_ctor_get(v_x_701_, 0);
                        v_tail_704_ = lean_ctor_get(v_x_701_, 1);
                        v_head_705_ = lean_ctor_get(v_x_702_, 0);
                        v_tail_706_ = lean_ctor_get(v_x_702_, 1);
                        v_isSharedCheck_715_ = (!lean_is_exclusive(v_x_702_)) as u8;
                        if v_isSharedCheck_715_ == 0 {
                            v___x_708_ = v_x_702_;
                            v_isShared_709_ = v_isSharedCheck_715_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_706_);
                            lean_inc(v_head_705_);
                            lean_dec(v_x_702_);
                            v___x_708_ = lean_box(0);
                            v_isShared_709_ = v_isSharedCheck_715_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_710_ = lean_int_mul(v_head_703_, v_head_705_);
                lean_dec(v_head_705_);
                v___x_711_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(
                    v_tail_704_,
                    v_tail_706_,
                );
                if v_isShared_709_ == 0 {
                    lean_ctor_set(v___x_708_, 1, v___x_711_);
                    lean_ctor_set(v___x_708_, 0, v___x_710_);
                    v___x_713_ = v___x_708_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_714_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_714_, 0, v___x_710_);
                    lean_ctor_set(v_reuseFailAlloc_714_, 1, v___x_711_);
                    v___x_713_ = v_reuseFailAlloc_714_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_713_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0___boxed(
    mut v_x_716_: *mut LeanObject,
    mut v_x_717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_718_: *mut LeanObject = core::ptr::null_mut();
    v_res_718_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_x_716_, v_x_717_);
    lean_dec(v_x_716_);
    return v_res_718_;
}
pub unsafe fn l_Lean_Omega_IntList_mul(
    mut v_xs_719_: *mut LeanObject,
    mut v_ys_720_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    v___x_721_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_719_, v_ys_720_);
    return v___x_721_;
}
pub unsafe fn l_Lean_Omega_IntList_mul___boxed(
    mut v_xs_722_: *mut LeanObject,
    mut v_ys_723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_724_: *mut LeanObject = core::ptr::null_mut();
    v_res_724_ = l_Lean_Omega_IntList_mul(v_xs_722_, v_ys_723_);
    lean_dec(v_xs_722_);
    return v_res_724_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(
    mut v_a_727_: *mut LeanObject,
    mut v_a_728_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_734_: u8 = 0;
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_740_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_727_) == 0 {
                    v___x_729_ = l_List_reverse___redArg(v_a_728_);
                    return v___x_729_;
                } else {
                    v_head_730_ = lean_ctor_get(v_a_727_, 0);
                    v_tail_731_ = lean_ctor_get(v_a_727_, 1);
                    v_isSharedCheck_740_ = (!lean_is_exclusive(v_a_727_)) as u8;
                    if v_isSharedCheck_740_ == 0 {
                        v___x_733_ = v_a_727_;
                        v_isShared_734_ = v_isSharedCheck_740_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_731_);
                        lean_inc(v_head_730_);
                        lean_dec(v_a_727_);
                        v___x_733_ = lean_box(0);
                        v_isShared_734_ = v_isSharedCheck_740_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_735_ = lean_int_neg(v_head_730_);
                lean_dec(v_head_730_);
                if v_isShared_734_ == 0 {
                    lean_ctor_set(v___x_733_, 1, v_a_728_);
                    lean_ctor_set(v___x_733_, 0, v___x_735_);
                    v___x_737_ = v___x_733_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_739_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_739_, 0, v___x_735_);
                    lean_ctor_set(v_reuseFailAlloc_739_, 1, v_a_728_);
                    v___x_737_ = v_reuseFailAlloc_739_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_727_ = v_tail_731_;
                v_a_728_ = v___x_737_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_IntList_neg(mut v_xs_741_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = lean_box(0);
    v___x_743_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_741_, v___x_742_);
    return v___x_743_;
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(
    mut v_x_746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_751_: u8 = 0;
    let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_746_) == 0 {
                    return v_x_746_;
                } else {
                    v_head_747_ = lean_ctor_get(v_x_746_, 0);
                    v_tail_748_ = lean_ctor_get(v_x_746_, 1);
                    v_isSharedCheck_758_ = (!lean_is_exclusive(v_x_746_)) as u8;
                    if v_isSharedCheck_758_ == 0 {
                        v___x_750_ = v_x_746_;
                        v_isShared_751_ = v_isSharedCheck_758_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_748_);
                        lean_inc(v_head_747_);
                        lean_dec(v_x_746_);
                        v___x_750_ = lean_box(0);
                        v_isShared_751_ = v_isSharedCheck_758_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_752_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_753_ = lean_int_sub(v___x_752_, v_head_747_);
                lean_dec(v_head_747_);
                v___x_754_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_748_);
                if v_isShared_751_ == 0 {
                    lean_ctor_set(v___x_750_, 1, v___x_754_);
                    lean_ctor_set(v___x_750_, 0, v___x_753_);
                    v___x_756_ = v___x_750_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_753_);
                    lean_ctor_set(v_reuseFailAlloc_757_, 1, v___x_754_);
                    v___x_756_ = v_reuseFailAlloc_757_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(
    mut v_x_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_764_: u8 = 0;
    let mut v___x_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_771_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_759_) == 0 {
                    return v_x_759_;
                } else {
                    v_head_760_ = lean_ctor_get(v_x_759_, 0);
                    v_tail_761_ = lean_ctor_get(v_x_759_, 1);
                    v_isSharedCheck_771_ = (!lean_is_exclusive(v_x_759_)) as u8;
                    if v_isSharedCheck_771_ == 0 {
                        v___x_763_ = v_x_759_;
                        v_isShared_764_ = v_isSharedCheck_771_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_761_);
                        lean_inc(v_head_760_);
                        lean_dec(v_x_759_);
                        v___x_763_ = lean_box(0);
                        v_isShared_764_ = v_isSharedCheck_771_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_765_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_766_ = lean_int_sub(v___x_765_, v_head_760_);
                lean_dec(v_head_760_);
                v___x_767_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_761_);
                if v_isShared_764_ == 0 {
                    lean_ctor_set(v___x_763_, 1, v___x_767_);
                    lean_ctor_set(v___x_763_, 0, v___x_766_);
                    v___x_769_ = v___x_763_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_770_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_770_, 0, v___x_766_);
                    lean_ctor_set(v_reuseFailAlloc_770_, 1, v___x_767_);
                    v___x_769_ = v_reuseFailAlloc_770_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_769_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(
    mut v_x_772_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_777_: u8 = 0;
    let mut v___x_778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_784_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_772_) == 0 {
                    return v_x_772_;
                } else {
                    v_head_773_ = lean_ctor_get(v_x_772_, 0);
                    v_tail_774_ = lean_ctor_get(v_x_772_, 1);
                    v_isSharedCheck_784_ = (!lean_is_exclusive(v_x_772_)) as u8;
                    if v_isSharedCheck_784_ == 0 {
                        v___x_776_ = v_x_772_;
                        v_isShared_777_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_774_);
                        lean_inc(v_head_773_);
                        lean_dec(v_x_772_);
                        v___x_776_ = lean_box(0);
                        v_isShared_777_ = v_isSharedCheck_784_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_778_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_779_ = lean_int_sub(v_head_773_, v___x_778_);
                lean_dec(v_head_773_);
                v___x_780_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_774_);
                if v_isShared_777_ == 0 {
                    lean_ctor_set(v___x_776_, 1, v___x_780_);
                    lean_ctor_set(v___x_776_, 0, v___x_779_);
                    v___x_782_ = v___x_776_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_783_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_783_, 0, v___x_779_);
                    lean_ctor_set(v_reuseFailAlloc_783_, 1, v___x_780_);
                    v___x_782_ = v_reuseFailAlloc_783_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_782_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(
    mut v_x_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_790_: u8 = 0;
    let mut v___x_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_797_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_785_) == 0 {
                    return v_x_785_;
                } else {
                    v_head_786_ = lean_ctor_get(v_x_785_, 0);
                    v_tail_787_ = lean_ctor_get(v_x_785_, 1);
                    v_isSharedCheck_797_ = (!lean_is_exclusive(v_x_785_)) as u8;
                    if v_isSharedCheck_797_ == 0 {
                        v___x_789_ = v_x_785_;
                        v_isShared_790_ = v_isSharedCheck_797_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_787_);
                        lean_inc(v_head_786_);
                        lean_dec(v_x_785_);
                        v___x_789_ = lean_box(0);
                        v_isShared_790_ = v_isSharedCheck_797_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_791_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_792_ = lean_int_sub(v_head_786_, v___x_791_);
                lean_dec(v_head_786_);
                v___x_793_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_787_);
                if v_isShared_790_ == 0 {
                    lean_ctor_set(v___x_789_, 1, v___x_793_);
                    lean_ctor_set(v___x_789_, 0, v___x_792_);
                    v___x_795_ = v___x_789_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_792_);
                    lean_ctor_set(v_reuseFailAlloc_796_, 1, v___x_793_);
                    v___x_795_ = v_reuseFailAlloc_796_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_795_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(
    mut v_x_798_: *mut LeanObject,
    mut v_x_799_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_808_: u8 = 0;
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_798_) == 0 {
                    v___x_800_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(v_x_799_);
                    return v___x_800_;
                } else {
                    if lean_obj_tag(v_x_799_) == 0 {
                        v___x_801_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(v_x_798_);
                        return v___x_801_;
                    } else {
                        v_head_802_ = lean_ctor_get(v_x_798_, 0);
                        lean_inc(v_head_802_);
                        v_tail_803_ = lean_ctor_get(v_x_798_, 1);
                        lean_inc(v_tail_803_);
                        lean_dec_ref_known(v_x_798_, 2);
                        v_head_804_ = lean_ctor_get(v_x_799_, 0);
                        v_tail_805_ = lean_ctor_get(v_x_799_, 1);
                        v_isSharedCheck_814_ = (!lean_is_exclusive(v_x_799_)) as u8;
                        if v_isSharedCheck_814_ == 0 {
                            v___x_807_ = v_x_799_;
                            v_isShared_808_ = v_isSharedCheck_814_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_805_);
                            lean_inc(v_head_804_);
                            lean_dec(v_x_799_);
                            v___x_807_ = lean_box(0);
                            v_isShared_808_ = v_isSharedCheck_814_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_809_ = lean_int_sub(v_head_802_, v_head_804_);
                lean_dec(v_head_804_);
                lean_dec(v_head_802_);
                v___x_810_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(
                    v_tail_803_,
                    v_tail_805_,
                );
                if v_isShared_808_ == 0 {
                    lean_ctor_set(v___x_807_, 1, v___x_810_);
                    lean_ctor_set(v___x_807_, 0, v___x_809_);
                    v___x_812_ = v___x_807_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_813_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_813_, 0, v___x_809_);
                    lean_ctor_set(v_reuseFailAlloc_813_, 1, v___x_810_);
                    v___x_812_ = v_reuseFailAlloc_813_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_812_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Omega_IntList_sub(
    mut v_xs_815_: *mut LeanObject,
    mut v_ys_816_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    v___x_817_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_815_, v_ys_816_);
    return v___x_817_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(
    mut v_i_820_: *mut LeanObject,
    mut v_a_821_: *mut LeanObject,
    mut v_a_822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_828_: u8 = 0;
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_834_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_821_) == 0 {
                    v___x_823_ = l_List_reverse___redArg(v_a_822_);
                    return v___x_823_;
                } else {
                    v_head_824_ = lean_ctor_get(v_a_821_, 0);
                    v_tail_825_ = lean_ctor_get(v_a_821_, 1);
                    v_isSharedCheck_834_ = (!lean_is_exclusive(v_a_821_)) as u8;
                    if v_isSharedCheck_834_ == 0 {
                        v___x_827_ = v_a_821_;
                        v_isShared_828_ = v_isSharedCheck_834_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_825_);
                        lean_inc(v_head_824_);
                        lean_dec(v_a_821_);
                        v___x_827_ = lean_box(0);
                        v_isShared_828_ = v_isSharedCheck_834_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_829_ = lean_int_mul(v_i_820_, v_head_824_);
                lean_dec(v_head_824_);
                if v_isShared_828_ == 0 {
                    lean_ctor_set(v___x_827_, 1, v_a_822_);
                    lean_ctor_set(v___x_827_, 0, v___x_829_);
                    v___x_831_ = v___x_827_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_833_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_829_);
                    lean_ctor_set(v_reuseFailAlloc_833_, 1, v_a_822_);
                    v___x_831_ = v_reuseFailAlloc_833_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_821_ = v_tail_825_;
                v_a_822_ = v___x_831_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(
    mut v_i_835_: *mut LeanObject,
    mut v_a_836_: *mut LeanObject,
    mut v_a_837_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_838_: *mut LeanObject = core::ptr::null_mut();
    v_res_838_ =
        l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_835_, v_a_836_, v_a_837_);
    lean_dec(v_i_835_);
    return v_res_838_;
}
pub unsafe fn l_Lean_Omega_IntList_smul(
    mut v_xs_839_: *mut LeanObject,
    mut v_i_840_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    v___x_841_ = lean_box(0);
    v___x_842_ =
        l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_840_, v_xs_839_, v___x_841_);
    return v___x_842_;
}
pub unsafe fn l_Lean_Omega_IntList_smul___boxed(
    mut v_xs_843_: *mut LeanObject,
    mut v_i_844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_845_: *mut LeanObject = core::ptr::null_mut();
    v_res_845_ = l_Lean_Omega_IntList_smul(v_xs_843_, v_i_844_);
    lean_dec(v_i_844_);
    return v_res_845_;
}
pub unsafe fn l_Lean_Omega_IntList_instHMulInt___lam__0(
    mut v_i_846_: *mut LeanObject,
    mut v_xs_847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    v___x_848_ = l_Lean_Omega_IntList_smul(v_xs_847_, v_i_846_);
    return v___x_848_;
}
pub unsafe fn l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(
    mut v_i_849_: *mut LeanObject,
    mut v_xs_850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_851_: *mut LeanObject = core::ptr::null_mut();
    v_res_851_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_849_, v_xs_850_);
    lean_dec(v_i_849_);
    return v_res_851_;
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(
    mut v_a_854_: *mut LeanObject,
    mut v_b_855_: *mut LeanObject,
    mut v_x_856_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_861_: u8 = 0;
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_856_) == 0 {
                    return v_x_856_;
                } else {
                    v_head_857_ = lean_ctor_get(v_x_856_, 0);
                    v_tail_858_ = lean_ctor_get(v_x_856_, 1);
                    v_isSharedCheck_870_ = (!lean_is_exclusive(v_x_856_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_860_ = v_x_856_;
                        v_isShared_861_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_858_);
                        lean_inc(v_head_857_);
                        lean_dec(v_x_856_);
                        v___x_860_ = lean_box(0);
                        v_isShared_861_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_862_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_863_ = lean_int_mul(v_a_854_, v___x_862_);
                v___x_864_ = lean_int_mul(v_b_855_, v_head_857_);
                lean_dec(v_head_857_);
                v___x_865_ = lean_int_add(v___x_863_, v___x_864_);
                lean_dec(v___x_864_);
                lean_dec(v___x_863_);
                v___x_866_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_854_, v_b_855_, v_tail_858_);
                if v_isShared_861_ == 0 {
                    lean_ctor_set(v___x_860_, 1, v___x_866_);
                    lean_ctor_set(v___x_860_, 0, v___x_865_);
                    v___x_868_ = v___x_860_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_869_, 0, v___x_865_);
                    lean_ctor_set(v_reuseFailAlloc_869_, 1, v___x_866_);
                    v___x_868_ = v_reuseFailAlloc_869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_868_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(
    mut v_a_871_: *mut LeanObject,
    mut v_b_872_: *mut LeanObject,
    mut v_x_873_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_874_: *mut LeanObject = core::ptr::null_mut();
    v_res_874_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_871_, v_b_872_, v_x_873_);
    lean_dec(v_b_872_);
    lean_dec(v_a_871_);
    return v_res_874_;
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(
    mut v_a_875_: *mut LeanObject,
    mut v_b_876_: *mut LeanObject,
    mut v_x_877_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_882_: u8 = 0;
    let mut v___x_883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_891_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_877_) == 0 {
                    return v_x_877_;
                } else {
                    v_head_878_ = lean_ctor_get(v_x_877_, 0);
                    v_tail_879_ = lean_ctor_get(v_x_877_, 1);
                    v_isSharedCheck_891_ = (!lean_is_exclusive(v_x_877_)) as u8;
                    if v_isSharedCheck_891_ == 0 {
                        v___x_881_ = v_x_877_;
                        v_isShared_882_ = v_isSharedCheck_891_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_879_);
                        lean_inc(v_head_878_);
                        lean_dec(v_x_877_);
                        v___x_881_ = lean_box(0);
                        v_isShared_882_ = v_isSharedCheck_891_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_883_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_884_ = lean_int_mul(v_a_875_, v___x_883_);
                v___x_885_ = lean_int_mul(v_b_876_, v_head_878_);
                lean_dec(v_head_878_);
                v___x_886_ = lean_int_add(v___x_884_, v___x_885_);
                lean_dec(v___x_885_);
                lean_dec(v___x_884_);
                v___x_887_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_875_, v_b_876_, v_tail_879_);
                if v_isShared_882_ == 0 {
                    lean_ctor_set(v___x_881_, 1, v___x_887_);
                    lean_ctor_set(v___x_881_, 0, v___x_886_);
                    v___x_889_ = v___x_881_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_890_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_890_, 0, v___x_886_);
                    lean_ctor_set(v_reuseFailAlloc_890_, 1, v___x_887_);
                    v___x_889_ = v_reuseFailAlloc_890_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_889_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(
    mut v_a_892_: *mut LeanObject,
    mut v_b_893_: *mut LeanObject,
    mut v_x_894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_895_: *mut LeanObject = core::ptr::null_mut();
    v_res_895_ =
        l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(
            v_a_892_, v_b_893_, v_x_894_,
        );
    lean_dec(v_b_893_);
    lean_dec(v_a_892_);
    return v_res_895_;
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(
    mut v_a_896_: *mut LeanObject,
    mut v_b_897_: *mut LeanObject,
    mut v_x_898_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_903_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_912_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_898_) == 0 {
                    return v_x_898_;
                } else {
                    v_head_899_ = lean_ctor_get(v_x_898_, 0);
                    v_tail_900_ = lean_ctor_get(v_x_898_, 1);
                    v_isSharedCheck_912_ = (!lean_is_exclusive(v_x_898_)) as u8;
                    if v_isSharedCheck_912_ == 0 {
                        v___x_902_ = v_x_898_;
                        v_isShared_903_ = v_isSharedCheck_912_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_900_);
                        lean_inc(v_head_899_);
                        lean_dec(v_x_898_);
                        v___x_902_ = lean_box(0);
                        v_isShared_903_ = v_isSharedCheck_912_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_904_ = lean_int_mul(v_a_896_, v_head_899_);
                lean_dec(v_head_899_);
                v___x_905_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_906_ = lean_int_mul(v_b_897_, v___x_905_);
                v___x_907_ = lean_int_add(v___x_904_, v___x_906_);
                lean_dec(v___x_906_);
                lean_dec(v___x_904_);
                v___x_908_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_896_, v_b_897_, v_tail_900_);
                if v_isShared_903_ == 0 {
                    lean_ctor_set(v___x_902_, 1, v___x_908_);
                    lean_ctor_set(v___x_902_, 0, v___x_907_);
                    v___x_910_ = v___x_902_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_911_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_911_, 0, v___x_907_);
                    lean_ctor_set(v_reuseFailAlloc_911_, 1, v___x_908_);
                    v___x_910_ = v_reuseFailAlloc_911_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(
    mut v_a_913_: *mut LeanObject,
    mut v_b_914_: *mut LeanObject,
    mut v_x_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v_res_916_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_913_, v_b_914_, v_x_915_);
    lean_dec(v_b_914_);
    lean_dec(v_a_913_);
    return v_res_916_;
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(
    mut v_a_917_: *mut LeanObject,
    mut v_b_918_: *mut LeanObject,
    mut v_x_919_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_924_: u8 = 0;
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_933_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_919_) == 0 {
                    return v_x_919_;
                } else {
                    v_head_920_ = lean_ctor_get(v_x_919_, 0);
                    v_tail_921_ = lean_ctor_get(v_x_919_, 1);
                    v_isSharedCheck_933_ = (!lean_is_exclusive(v_x_919_)) as u8;
                    if v_isSharedCheck_933_ == 0 {
                        v___x_923_ = v_x_919_;
                        v_isShared_924_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_921_);
                        lean_inc(v_head_920_);
                        lean_dec(v_x_919_);
                        v___x_923_ = lean_box(0);
                        v_isShared_924_ = v_isSharedCheck_933_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_925_ = lean_int_mul(v_a_917_, v_head_920_);
                lean_dec(v_head_920_);
                v___x_926_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
                    core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
                    _init_l_Lean_Omega_IntList_get___closed__0,
                );
                v___x_927_ = lean_int_mul(v_b_918_, v___x_926_);
                v___x_928_ = lean_int_add(v___x_925_, v___x_927_);
                lean_dec(v___x_927_);
                lean_dec(v___x_925_);
                v___x_929_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_917_, v_b_918_, v_tail_921_);
                if v_isShared_924_ == 0 {
                    lean_ctor_set(v___x_923_, 1, v___x_929_);
                    lean_ctor_set(v___x_923_, 0, v___x_928_);
                    v___x_931_ = v___x_923_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_932_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_932_, 0, v___x_928_);
                    lean_ctor_set(v_reuseFailAlloc_932_, 1, v___x_929_);
                    v___x_931_ = v_reuseFailAlloc_932_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_931_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(
    mut v_a_934_: *mut LeanObject,
    mut v_b_935_: *mut LeanObject,
    mut v_x_936_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_937_: *mut LeanObject = core::ptr::null_mut();
    v_res_937_ =
        l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(
            v_a_934_, v_b_935_, v_x_936_,
        );
    lean_dec(v_b_935_);
    lean_dec(v_a_934_);
    return v_res_937_;
}
pub unsafe fn l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(
    mut v_a_938_: *mut LeanObject,
    mut v_b_939_: *mut LeanObject,
    mut v_x_940_: *mut LeanObject,
    mut v_x_941_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_950_: u8 = 0;
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_940_) == 0 {
                    v___x_942_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_938_, v_b_939_, v_x_941_);
                    return v___x_942_;
                } else {
                    if lean_obj_tag(v_x_941_) == 0 {
                        v___x_943_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_938_, v_b_939_, v_x_940_);
                        return v___x_943_;
                    } else {
                        v_head_944_ = lean_ctor_get(v_x_940_, 0);
                        lean_inc(v_head_944_);
                        v_tail_945_ = lean_ctor_get(v_x_940_, 1);
                        lean_inc(v_tail_945_);
                        lean_dec_ref_known(v_x_940_, 2);
                        v_head_946_ = lean_ctor_get(v_x_941_, 0);
                        v_tail_947_ = lean_ctor_get(v_x_941_, 1);
                        v_isSharedCheck_958_ = (!lean_is_exclusive(v_x_941_)) as u8;
                        if v_isSharedCheck_958_ == 0 {
                            v___x_949_ = v_x_941_;
                            v_isShared_950_ = v_isSharedCheck_958_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_tail_947_);
                            lean_inc(v_head_946_);
                            lean_dec(v_x_941_);
                            v___x_949_ = lean_box(0);
                            v_isShared_950_ = v_isSharedCheck_958_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_951_ = lean_int_mul(v_a_938_, v_head_944_);
                lean_dec(v_head_944_);
                v___x_952_ = lean_int_mul(v_b_939_, v_head_946_);
                lean_dec(v_head_946_);
                v___x_953_ = lean_int_add(v___x_951_, v___x_952_);
                lean_dec(v___x_952_);
                lean_dec(v___x_951_);
                v___x_954_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(
                    v_a_938_,
                    v_b_939_,
                    v_tail_945_,
                    v_tail_947_,
                );
                if v_isShared_950_ == 0 {
                    lean_ctor_set(v___x_949_, 1, v___x_954_);
                    lean_ctor_set(v___x_949_, 0, v___x_953_);
                    v___x_956_ = v___x_949_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_957_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_957_, 0, v___x_953_);
                    lean_ctor_set(v_reuseFailAlloc_957_, 1, v___x_954_);
                    v___x_956_ = v_reuseFailAlloc_957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_956_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(
    mut v_a_959_: *mut LeanObject,
    mut v_b_960_: *mut LeanObject,
    mut v_x_961_: *mut LeanObject,
    mut v_x_962_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_963_: *mut LeanObject = core::ptr::null_mut();
    v_res_963_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(
        v_a_959_, v_b_960_, v_x_961_, v_x_962_,
    );
    lean_dec(v_b_960_);
    lean_dec(v_a_959_);
    return v_res_963_;
}
pub unsafe fn l_Lean_Omega_IntList_combo(
    mut v_a_964_: *mut LeanObject,
    mut v_xs_965_: *mut LeanObject,
    mut v_b_966_: *mut LeanObject,
    mut v_ys_967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_968_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(
        v_a_964_, v_b_966_, v_xs_965_, v_ys_967_,
    );
    return v___x_968_;
}
pub unsafe fn l_Lean_Omega_IntList_combo___boxed(
    mut v_a_969_: *mut LeanObject,
    mut v_xs_970_: *mut LeanObject,
    mut v_b_971_: *mut LeanObject,
    mut v_ys_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_973_: *mut LeanObject = core::ptr::null_mut();
    v_res_973_ = l_Lean_Omega_IntList_combo(v_a_969_, v_xs_970_, v_b_971_, v_ys_972_);
    lean_dec(v_b_971_);
    lean_dec(v_a_969_);
    return v_res_973_;
}
pub unsafe fn l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(
    mut v_init_974_: *mut LeanObject,
    mut v_x_975_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_975_) == 0 {
        lean_inc(v_init_974_);
        return v_init_974_;
    } else {
        let mut v_head_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_979_: *mut LeanObject = core::ptr::null_mut();
        v_head_976_ = lean_ctor_get(v_x_975_, 0);
        v_tail_977_ = lean_ctor_get(v_x_975_, 1);
        v___x_978_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_974_, v_tail_977_);
        v___x_979_ = lean_int_add(v_head_976_, v___x_978_);
        lean_dec(v___x_978_);
        return v___x_979_;
    }
}
pub unsafe fn l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0___boxed(
    mut v_init_980_: *mut LeanObject,
    mut v_x_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_980_, v_x_981_);
    lean_dec(v_x_981_);
    lean_dec(v_init_980_);
    return v_res_982_;
}
pub unsafe fn l_Lean_Omega_IntList_sum(mut v_xs_983_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    v___x_984_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Omega_IntList_get___closed__0_once),
        _init_l_Lean_Omega_IntList_get___closed__0,
    );
    v___x_985_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v___x_984_, v_xs_983_);
    return v___x_985_;
}
pub unsafe fn l_Lean_Omega_IntList_sum___boxed(mut v_xs_986_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_987_: *mut LeanObject = core::ptr::null_mut();
    v_res_987_ = l_Lean_Omega_IntList_sum(v_xs_986_);
    lean_dec(v_xs_986_);
    return v_res_987_;
}
pub unsafe fn l_Lean_Omega_IntList_dot(
    mut v_xs_988_: *mut LeanObject,
    mut v_ys_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut LeanObject = core::ptr::null_mut();
    v___x_990_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_988_, v_ys_989_);
    v___x_991_ = l_Lean_Omega_IntList_sum(v___x_990_);
    lean_dec(v___x_990_);
    return v___x_991_;
}
pub unsafe fn l_Lean_Omega_IntList_dot___boxed(
    mut v_xs_992_: *mut LeanObject,
    mut v_ys_993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_994_: *mut LeanObject = core::ptr::null_mut();
    v_res_994_ = l_Lean_Omega_IntList_dot(v_xs_992_, v_ys_993_);
    lean_dec(v_xs_992_);
    return v_res_994_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(
    mut v_g_995_: *mut LeanObject,
    mut v_a_996_: *mut LeanObject,
    mut v_a_997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1003_: u8 = 0;
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_996_) == 0 {
                    v___x_998_ = l_List_reverse___redArg(v_a_997_);
                    return v___x_998_;
                } else {
                    v_head_999_ = lean_ctor_get(v_a_996_, 0);
                    v_tail_1000_ = lean_ctor_get(v_a_996_, 1);
                    v_isSharedCheck_1009_ = (!lean_is_exclusive(v_a_996_)) as u8;
                    if v_isSharedCheck_1009_ == 0 {
                        v___x_1002_ = v_a_996_;
                        v_isShared_1003_ = v_isSharedCheck_1009_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1000_);
                        lean_inc(v_head_999_);
                        lean_dec(v_a_996_);
                        v___x_1002_ = lean_box(0);
                        v_isShared_1003_ = v_isSharedCheck_1009_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1004_ = lean_int_ediv(v_head_999_, v_g_995_);
                lean_dec(v_head_999_);
                if v_isShared_1003_ == 0 {
                    lean_ctor_set(v___x_1002_, 1, v_a_997_);
                    lean_ctor_set(v___x_1002_, 0, v___x_1004_);
                    v___x_1006_ = v___x_1002_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1008_, 0, v___x_1004_);
                    lean_ctor_set(v_reuseFailAlloc_1008_, 1, v_a_997_);
                    v___x_1006_ = v_reuseFailAlloc_1008_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_996_ = v_tail_1000_;
                v_a_997_ = v___x_1006_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(
    mut v_g_1010_: *mut LeanObject,
    mut v_a_1011_: *mut LeanObject,
    mut v_a_1012_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1013_: *mut LeanObject = core::ptr::null_mut();
    v_res_1013_ =
        l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_1010_, v_a_1011_, v_a_1012_);
    lean_dec(v_g_1010_);
    return v_res_1013_;
}
pub unsafe fn l_Lean_Omega_IntList_sdiv(
    mut v_xs_1014_: *mut LeanObject,
    mut v_g_1015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
    v___x_1016_ = lean_box(0);
    v___x_1017_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(
        v_g_1015_,
        v_xs_1014_,
        v___x_1016_,
    );
    return v___x_1017_;
}
pub unsafe fn l_Lean_Omega_IntList_sdiv___boxed(
    mut v_xs_1018_: *mut LeanObject,
    mut v_g_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
    v_res_1020_ = l_Lean_Omega_IntList_sdiv(v_xs_1018_, v_g_1019_);
    lean_dec(v_g_1019_);
    return v_res_1020_;
}
pub unsafe fn l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(
    mut v_init_1021_: *mut LeanObject,
    mut v_x_1022_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1022_) == 0 {
        lean_inc(v_init_1021_);
        return v_init_1021_;
    } else {
        let mut v_head_1023_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1024_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
        v_head_1023_ = lean_ctor_get(v_x_1022_, 0);
        v_tail_1024_ = lean_ctor_get(v_x_1022_, 1);
        v___x_1025_ =
            l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_1021_, v_tail_1024_);
        v___x_1026_ = lean_nat_abs(v_head_1023_);
        v___x_1027_ = lean_nat_gcd(v___x_1026_, v___x_1025_);
        lean_dec(v___x_1025_);
        lean_dec(v___x_1026_);
        return v___x_1027_;
    }
}
pub unsafe fn l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0___boxed(
    mut v_init_1028_: *mut LeanObject,
    mut v_x_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1030_: *mut LeanObject = core::ptr::null_mut();
    v_res_1030_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_1028_, v_x_1029_);
    lean_dec(v_x_1029_);
    lean_dec(v_init_1028_);
    return v_res_1030_;
}
pub unsafe fn l_Lean_Omega_IntList_gcd(mut v_xs_1031_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = lean_unsigned_to_nat(0);
    v___x_1033_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v___x_1032_, v_xs_1031_);
    return v___x_1033_;
}
pub unsafe fn l_Lean_Omega_IntList_gcd___boxed(mut v_xs_1034_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1035_: *mut LeanObject = core::ptr::null_mut();
    v_res_1035_ = l_Lean_Omega_IntList_gcd(v_xs_1034_);
    lean_dec(v_xs_1034_);
    return v_res_1035_;
}
pub unsafe fn l_Lean_Omega_IntList_bmod___lam__0(
    mut v_m_1036_: *mut LeanObject,
    mut v_x_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1038_: *mut LeanObject = core::ptr::null_mut();
    v___x_1038_ = l_Int_bmod(v_x_1037_, v_m_1036_);
    return v___x_1038_;
}
pub unsafe fn l_Lean_Omega_IntList_bmod___lam__0___boxed(
    mut v_m_1039_: *mut LeanObject,
    mut v_x_1040_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1041_: *mut LeanObject = core::ptr::null_mut();
    v_res_1041_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_1039_, v_x_1040_);
    lean_dec(v_x_1040_);
    return v_res_1041_;
}
pub unsafe fn l_Lean_Omega_IntList_bmod(
    mut v_x_1042_: *mut LeanObject,
    mut v_m_1043_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___f_1044_ = lean_alloc_closure(
        l_Lean_Omega_IntList_bmod___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1044_, 0, v_m_1043_);
    v___x_1045_ = lean_box(0);
    v___x_1046_ = l_List_mapTR_loop___redArg(v___f_1044_, v_x_1042_, v___x_1045_);
    return v___x_1046_;
}
pub unsafe fn l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(
    mut v_m_1047_: *mut LeanObject,
    mut v_a_1048_: *mut LeanObject,
    mut v_b_1049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_m_1047_);
    v___f_1050_ = lean_alloc_closure(
        l_Lean_Omega_IntList_bmod___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1050_, 0, v_m_1047_);
    lean_inc(v_b_1049_);
    v___x_1051_ = l_Lean_Omega_IntList_dot(v_a_1048_, v_b_1049_);
    v___x_1052_ = l_Int_bmod(v___x_1051_, v_m_1047_);
    lean_dec(v___x_1051_);
    v___x_1053_ = lean_box(0);
    v___x_1054_ = l_List_mapTR_loop___redArg(v___f_1050_, v_a_1048_, v___x_1053_);
    v___x_1055_ = l_Lean_Omega_IntList_dot(v___x_1054_, v_b_1049_);
    lean_dec(v___x_1054_);
    v___x_1056_ = lean_int_sub(v___x_1052_, v___x_1055_);
    lean_dec(v___x_1055_);
    lean_dec(v___x_1052_);
    return v___x_1056_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Omega_IntList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Omega_IntList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Omega_IntList(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega_IntList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Omega_IntList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Omega_IntList(builtin);
}

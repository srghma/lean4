// Lean compiler output
// Module: Init.Data.Dyadic.Basic
// Imports: Init.Data.Int.Bitwise.Lemmas Init.Data.Int.Bitwise.Basic Init.Data.Order.Classes Init.Data.Rat.Basic Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Bitwise.Lemmas Init.Data.Option.Lemmas Init.Data.Rat.Lemmas Init.Omega
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_ediv, lean_int_emod,
    lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs, lean_nat_add, lean_nat_dec_eq,
    lean_nat_pow, lean_nat_shiftl, lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::Basic::l_Int_pow;
use crate::r#gen::Init::Data::Int::Bitwise::Basic::{
    initialize_Init_Data_Int_Bitwise_Basic, l_Int_shiftLeft, l_Int_shiftRight,
    runtime_initialize_Init_Data_Int_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Int::Bitwise::Lemmas::{
    initialize_Init_Data_Int_Bitwise_Lemmas, runtime_initialize_Init_Data_Int_Bitwise_Lemmas,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Lemmas::{
    initialize_Init_Data_Nat_Bitwise_Lemmas, runtime_initialize_Init_Data_Nat_Bitwise_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Order::Classes::{
    initialize_Init_Data_Order_Classes, runtime_initialize_Init_Data_Order_Classes,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    initialize_Init_Data_Rat_Basic, l_Rat_ofInt, runtime_initialize_Init_Data_Rat_Basic,
};
use crate::r#gen::Init::Data::Rat::Lemmas::{
    initialize_Init_Data_Rat_Lemmas, runtime_initialize_Init_Data_Rat_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
static mut l_Int_trailingZeros_aux___redArg___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_trailingZeros_aux___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_trailingZeros_aux___redArg___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_trailingZeros_aux___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Dyadic_instIntCast___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_ofInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instIntCast___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instIntCast: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instNatCast___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instNatCast___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instNatCast___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instNatCast: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instAdd___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instAdd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instAdd: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instMul___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instMul___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instMul: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut leanh::LeanObject;
static mut l_Dyadic_pow___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Dyadic_instPowNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_pow as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instPowNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instPowNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instNeg___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instNeg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instNeg: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instSub___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instSub___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut leanh::LeanObject;
pub static mut l_Dyadic_instSub: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut leanh::LeanObject;
pub static l_Dyadic_instHShiftLeftInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftLeftInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Dyadic_instHShiftLeftInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Dyadic_instHShiftRightInt___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightInt___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Dyadic_instHShiftRightInt: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Dyadic_instHShiftLeftNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instHShiftLeftNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftLeftNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Dyadic_instHShiftLeftNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Dyadic_instHShiftRightNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instHShiftRightNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Dyadic_instHShiftRightNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Dyadic_toRat___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Dyadic_toRat___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLT: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLE: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = leanh::lean_unsigned_to_nat(2);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__1() -> *mut leanh::LeanObject
{
    let mut v_zero_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zero_679_ = leanh::lean_unsigned_to_nat(0);
    v___x_680_ = lean_nat_to_int(v_zero_679_);
    return v___x_680_;
}
pub unsafe fn l_Int_trailingZeros_aux___redArg(
    mut v_k_681_: *mut leanh::LeanObject,
    mut v_i_682_: *mut leanh::LeanObject,
    mut v_acc_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_685_: u8 = 0;
    let mut v___x_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v_one_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_684_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_685_ = lean_nat_dec_eq(v_k_681_, v_zero_684_);
                v___x_686_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__0,
                );
                v___x_687_ = lean_int_emod(v_i_682_, v___x_686_);
                v___x_688_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v___x_689_ = lean_int_dec_eq(v___x_687_, v___x_688_);
                leanh::lean_dec(v___x_687_);
                if v___x_689_ == 0 {
                    leanh::lean_dec(v_i_682_);
                    leanh::lean_dec(v_k_681_);
                    return v_acc_683_;
                } else {
                    v_one_690_ = leanh::lean_unsigned_to_nat(1);
                    v_n_691_ = lean_nat_sub(v_k_681_, v_one_690_);
                    leanh::lean_dec(v_k_681_);
                    v___x_692_ = lean_int_ediv(v_i_682_, v___x_686_);
                    leanh::lean_dec(v_i_682_);
                    v___x_693_ = lean_nat_add(v_acc_683_, v_one_690_);
                    leanh::lean_dec(v_acc_683_);
                    v_k_681_ = v_n_691_;
                    v_i_682_ = v___x_692_;
                    v_acc_683_ = v___x_693_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_trailingZeros_aux(
    mut v_k_695_: *mut leanh::LeanObject,
    mut v_i_696_: *mut leanh::LeanObject,
    mut v_hi_697_: *mut leanh::LeanObject,
    mut v_hk_698_: *mut leanh::LeanObject,
    mut v_acc_699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Int_trailingZeros_aux___redArg(v_k_695_, v_i_696_, v_acc_699_);
    return v___x_700_;
}
pub unsafe fn l_Int_trailingZeros(
    mut v_i_701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    v___x_702_ = leanh::lean_unsigned_to_nat(0);
    v___x_703_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_704_ = lean_int_dec_eq(v_i_701_, v___x_703_);
    if v___x_704_ == 0 {
        let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_705_ = lean_nat_abs(v_i_701_);
        v___x_706_ = l_Int_trailingZeros_aux___redArg(v___x_705_, v_i_701_, v___x_702_);
        return v___x_706_;
    } else {
        leanh::lean_dec(v_i_701_);
        return v___x_702_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
    mut v_k_707_: *mut leanh::LeanObject,
    mut v_h__1_708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_710_: u8 = 0;
    let mut v_one_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zero_709_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_710_ = lean_nat_dec_eq(v_k_707_, v_zero_709_);
    v_one_711_ = leanh::lean_unsigned_to_nat(1);
    v_n_712_ = lean_nat_sub(v_k_707_, v_one_711_);
    v___x_713_ = leanh::lean_apply_3(
        v_h__1_708_,
        v_n_712_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_713_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg___boxed(
    mut v_k_714_: *mut leanh::LeanObject,
    mut v_h__1_715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
            v_k_714_,
            v_h__1_715_,
        );
    leanh::lean_dec(v_k_714_);
    return v_res_716_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
    mut v_i_717_: *mut leanh::LeanObject,
    mut v_motive_718_: *mut leanh::LeanObject,
    mut v_k_719_: *mut leanh::LeanObject,
    mut v_x_720_: *mut leanh::LeanObject,
    mut v_hk_721_: *mut leanh::LeanObject,
    mut v_h__1_722_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_724_: u8 = 0;
    let mut v_one_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_zero_723_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_724_ = lean_nat_dec_eq(v_k_719_, v_zero_723_);
    v_one_725_ = leanh::lean_unsigned_to_nat(1);
    v_n_726_ = lean_nat_sub(v_k_719_, v_one_725_);
    v___x_727_ = leanh::lean_apply_3(
        v_h__1_722_,
        v_n_726_,
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_727_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(
    mut v_i_728_: *mut leanh::LeanObject,
    mut v_motive_729_: *mut leanh::LeanObject,
    mut v_k_730_: *mut leanh::LeanObject,
    mut v_x_731_: *mut leanh::LeanObject,
    mut v_hk_732_: *mut leanh::LeanObject,
    mut v_h__1_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
        v_i_728_,
        v_motive_729_,
        v_k_730_,
        v_x_731_,
        v_hk_732_,
        v_h__1_733_,
    );
    leanh::lean_dec(v_k_730_);
    leanh::lean_dec(v_i_728_);
    return v_res_734_;
}
pub unsafe fn l_Dyadic_ctorIdx(
    mut v_x_735_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_735_) == 0 {
        let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_736_ = leanh::lean_unsigned_to_nat(0);
        return v___x_736_;
    } else {
        let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_737_ = leanh::lean_unsigned_to_nat(1);
        return v___x_737_;
    }
}
pub unsafe fn l_Dyadic_ctorIdx___boxed(
    mut v_x_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Dyadic_ctorIdx(v_x_738_);
    leanh::lean_dec(v_x_738_);
    return v_res_739_;
}
pub unsafe fn l_Dyadic_ctorElim___redArg(
    mut v_t_740_: *mut leanh::LeanObject,
    mut v_k_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_740_) == 0 {
        return v_k_741_;
    } else {
        let mut v_n_742_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_743_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_n_742_ = leanh::lean_ctor_get(v_t_740_, 0);
        leanh::lean_inc(v_n_742_);
        v_k_743_ = leanh::lean_ctor_get(v_t_740_, 1);
        leanh::lean_inc(v_k_743_);
        leanh::lean_dec_ref_known(v_t_740_, 2);
        v___x_744_ =
            leanh::lean_apply_3(v_k_741_, v_n_742_, v_k_743_, leanh::lean_box(0));
        return v___x_744_;
    }
}
pub unsafe fn l_Dyadic_ctorElim(
    mut v_motive_745_: *mut leanh::LeanObject,
    mut v_ctorIdx_746_: *mut leanh::LeanObject,
    mut v_t_747_: *mut leanh::LeanObject,
    mut v_h_748_: *mut leanh::LeanObject,
    mut v_k_749_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Dyadic_ctorElim___redArg(v_t_747_, v_k_749_);
    return v___x_750_;
}
pub unsafe fn l_Dyadic_ctorElim___boxed(
    mut v_motive_751_: *mut leanh::LeanObject,
    mut v_ctorIdx_752_: *mut leanh::LeanObject,
    mut v_t_753_: *mut leanh::LeanObject,
    mut v_h_754_: *mut leanh::LeanObject,
    mut v_k_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Dyadic_ctorElim(v_motive_751_, v_ctorIdx_752_, v_t_753_, v_h_754_, v_k_755_);
    leanh::lean_dec(v_ctorIdx_752_);
    return v_res_756_;
}
pub unsafe fn l_Dyadic_zero_elim___redArg(
    mut v_t_757_: *mut leanh::LeanObject,
    mut v_zero_758_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Dyadic_ctorElim___redArg(v_t_757_, v_zero_758_);
    return v___x_759_;
}
pub unsafe fn l_Dyadic_zero_elim(
    mut v_motive_760_: *mut leanh::LeanObject,
    mut v_t_761_: *mut leanh::LeanObject,
    mut v_h_762_: *mut leanh::LeanObject,
    mut v_zero_763_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_764_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Dyadic_ctorElim___redArg(v_t_761_, v_zero_763_);
    return v___x_764_;
}
pub unsafe fn l_Dyadic_ofOdd_elim___redArg(
    mut v_t_765_: *mut leanh::LeanObject,
    mut v_ofOdd_766_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_767_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = l_Dyadic_ctorElim___redArg(v_t_765_, v_ofOdd_766_);
    return v___x_767_;
}
pub unsafe fn l_Dyadic_ofOdd_elim(
    mut v_motive_768_: *mut leanh::LeanObject,
    mut v_t_769_: *mut leanh::LeanObject,
    mut v_h_770_: *mut leanh::LeanObject,
    mut v_ofOdd_771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Dyadic_ctorElim___redArg(v_t_769_, v_ofOdd_771_);
    return v___x_772_;
}
pub unsafe fn l_instDecidableEqDyadic_decEq(
    mut v_x_773_: *mut leanh::LeanObject,
    mut v_x_774_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_773_) == 0 {
        if leanh::lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_775_: u8 = 0;
            v___x_775_ = 1;
            return v___x_775_;
        } else {
            let mut v___x_776_: u8 = 0;
            v___x_776_ = 0;
            return v___x_776_;
        }
    } else {
        if leanh::lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_777_: u8 = 0;
            v___x_777_ = 0;
            return v___x_777_;
        } else {
            let mut v_n_778_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_779_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_780_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_781_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: u8 = 0;
            v_n_778_ = leanh::lean_ctor_get(v_x_773_, 0);
            v_k_779_ = leanh::lean_ctor_get(v_x_773_, 1);
            v_n_780_ = leanh::lean_ctor_get(v_x_774_, 0);
            v_k_781_ = leanh::lean_ctor_get(v_x_774_, 1);
            v___x_782_ = lean_int_dec_eq(v_n_778_, v_n_780_);
            if v___x_782_ == 0 {
                return v___x_782_;
            } else {
                let mut v___x_783_: u8 = 0;
                v___x_783_ = lean_int_dec_eq(v_k_779_, v_k_781_);
                return v___x_783_;
            }
        }
    }
}
pub unsafe fn l_instDecidableEqDyadic_decEq___boxed(
    mut v_x_784_: *mut leanh::LeanObject,
    mut v_x_785_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_instDecidableEqDyadic_decEq(v_x_784_, v_x_785_);
    leanh::lean_dec(v_x_785_);
    leanh::lean_dec(v_x_784_);
    v_r_787_ = leanh::lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_instDecidableEqDyadic(
    mut v_x_788_: *mut leanh::LeanObject,
    mut v_x_789_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_790_: u8 = 0;
    v___x_790_ = l_instDecidableEqDyadic_decEq(v_x_788_, v_x_789_);
    return v___x_790_;
}
pub unsafe fn l_instDecidableEqDyadic___boxed(
    mut v_x_791_: *mut leanh::LeanObject,
    mut v_x_792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_793_ = l_instDecidableEqDyadic(v_x_791_, v_x_792_);
    leanh::lean_dec(v_x_792_);
    leanh::lean_dec(v_x_791_);
    v_r_794_ = leanh::lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(
    mut v_a_795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_796_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = lean_nat_to_int(v_a_795_);
    return v___x_796_;
}
pub unsafe fn l_Dyadic_ofIntWithPrec(
    mut v_i_797_: *mut leanh::LeanObject,
    mut v_prec_798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u8 = 0;
    v___x_799_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_800_ = lean_int_dec_eq(v_i_797_, v___x_799_);
    if v___x_800_ == 0 {
        let mut v___x_801_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v_i_797_);
        v___x_801_ = l_Int_trailingZeros(v_i_797_);
        v___x_802_ = l_Int_shiftRight(v_i_797_, v___x_801_);
        leanh::lean_dec(v_i_797_);
        v___x_803_ = lean_nat_to_int(v___x_801_);
        v___x_804_ = lean_int_sub(v_prec_798_, v___x_803_);
        leanh::lean_dec(v___x_803_);
        v___x_805_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
        leanh::lean_ctor_set(v___x_805_, 0, v___x_802_);
        leanh::lean_ctor_set(v___x_805_, 1, v___x_804_);
        return v___x_805_;
    } else {
        let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_i_797_);
        v___x_806_ = leanh::lean_box(0);
        return v___x_806_;
    }
}
pub unsafe fn l_Dyadic_ofIntWithPrec___boxed(
    mut v_i_807_: *mut leanh::LeanObject,
    mut v_prec_808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Dyadic_ofIntWithPrec(v_i_807_, v_prec_808_);
    leanh::lean_dec(v_prec_808_);
    return v_res_809_;
}
pub unsafe fn l_Dyadic_ofInt(
    mut v_i_810_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_812_ = l_Dyadic_ofIntWithPrec(v_i_810_, v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Dyadic_instOfNat(
    mut v_n_813_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = lean_nat_to_int(v_n_813_);
    v___x_815_ = l_Dyadic_ofInt(v___x_814_);
    return v___x_815_;
}
pub unsafe fn l_Dyadic_instNatCast___lam__0(
    mut v_x_818_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = lean_nat_to_int(v_x_818_);
    v___x_820_ = l_Dyadic_ofInt(v___x_819_);
    return v___x_820_;
}
pub unsafe fn l_Dyadic_add(
    mut v_x_823_: *mut leanh::LeanObject,
    mut v_y_824_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_829_: u8 = 0;
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v_n_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_840_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_844_: u8 = 0;
    let mut v_a_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_846_: u8 = 0;
    let mut v___x_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_823_) == 0 {
                    return v_y_824_;
                } else {
                    if leanh::lean_obj_tag(v_y_824_) == 0 {
                        v_n_825_ = leanh::lean_ctor_get(v_x_823_, 0);
                        v_k_826_ = leanh::lean_ctor_get(v_x_823_, 1);
                        v_isSharedCheck_833_ = (!leanh::lean_is_exclusive(v_x_823_)) as u8;
                        if v_isSharedCheck_833_ == 0 {
                            v___x_828_ = v_x_823_;
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_826_);
                            leanh::lean_inc(v_n_825_);
                            leanh::lean_dec(v_x_823_);
                            v___x_828_ = leanh::lean_box(0);
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_n_834_ = leanh::lean_ctor_get(v_x_823_, 0);
                        leanh::lean_inc(v_n_834_);
                        v_k_835_ = leanh::lean_ctor_get(v_x_823_, 1);
                        leanh::lean_inc(v_k_835_);
                        leanh::lean_dec_ref_known(v_x_823_, 2);
                        v_n_836_ = leanh::lean_ctor_get(v_y_824_, 0);
                        v_k_837_ = leanh::lean_ctor_get(v_y_824_, 1);
                        v_isSharedCheck_863_ = (!leanh::lean_is_exclusive(v_y_824_)) as u8;
                        if v_isSharedCheck_863_ == 0 {
                            v___x_839_ = v_y_824_;
                            v_isShared_840_ = v_isSharedCheck_863_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_837_);
                            leanh::lean_inc(v_n_836_);
                            leanh::lean_dec(v_y_824_);
                            v___x_839_ = leanh::lean_box(0);
                            v_isShared_840_ = v_isSharedCheck_863_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_829_ == 0 {
                    v___x_831_ = v___x_828_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_832_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v_n_825_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_826_);
                    v___x_831_ = v_reuseFailAlloc_832_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_831_;
            }
            3 => {
                v___x_841_ = lean_int_sub(v_k_835_, v_k_837_);
                v_natZero_842_ = leanh::lean_unsigned_to_nat(0);
                v_intZero_843_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_844_ = lean_int_dec_lt(v___x_841_, v_intZero_843_);
                if v_isNeg_844_ == 0 {
                    leanh::lean_dec(v_k_837_);
                    v_a_845_ = lean_nat_abs(v___x_841_);
                    leanh::lean_dec(v___x_841_);
                    v_isZero_846_ = lean_nat_dec_eq(v_a_845_, v_natZero_842_);
                    if v_isZero_846_ == 1 {
                        leanh::lean_dec(v_a_845_);
                        leanh::lean_del_object(v___x_839_);
                        v___x_847_ = lean_int_add(v_n_834_, v_n_836_);
                        leanh::lean_dec(v_n_836_);
                        leanh::lean_dec(v_n_834_);
                        v___x_848_ = l_Dyadic_ofIntWithPrec(v___x_847_, v_k_835_);
                        leanh::lean_dec(v_k_835_);
                        return v___x_848_;
                    } else {
                        v___x_849_ = l_Int_shiftLeft(v_n_836_, v_a_845_);
                        leanh::lean_dec(v_a_845_);
                        leanh::lean_dec(v_n_836_);
                        v___x_850_ = lean_int_add(v_n_834_, v___x_849_);
                        leanh::lean_dec(v___x_849_);
                        leanh::lean_dec(v_n_834_);
                        if v_isShared_840_ == 0 {
                            leanh::lean_ctor_set(v___x_839_, 1, v_k_835_);
                            leanh::lean_ctor_set(v___x_839_, 0, v___x_850_);
                            v___x_852_ = v___x_839_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_853_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_853_, 1, v_k_835_);
                            v___x_852_ = v_reuseFailAlloc_853_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_k_835_);
                    v_abs_854_ = lean_nat_abs(v___x_841_);
                    leanh::lean_dec(v___x_841_);
                    v_one_855_ = leanh::lean_unsigned_to_nat(1);
                    v_a_856_ = lean_nat_sub(v_abs_854_, v_one_855_);
                    leanh::lean_dec(v_abs_854_);
                    v___x_857_ = lean_nat_add(v_a_856_, v_one_855_);
                    leanh::lean_dec(v_a_856_);
                    v___x_858_ = l_Int_shiftLeft(v_n_834_, v___x_857_);
                    leanh::lean_dec(v___x_857_);
                    leanh::lean_dec(v_n_834_);
                    v___x_859_ = lean_int_add(v___x_858_, v_n_836_);
                    leanh::lean_dec(v_n_836_);
                    leanh::lean_dec(v___x_858_);
                    if v_isShared_840_ == 0 {
                        leanh::lean_ctor_set(v___x_839_, 0, v___x_859_);
                        v___x_861_ = v___x_839_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_837_);
                        v___x_861_ = v_reuseFailAlloc_862_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_852_;
            }
            5 => {
                return v___x_861_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_mul(
    mut v_x_866_: *mut leanh::LeanObject,
    mut v_y_867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_866_) == 0 {
                    leanh::lean_dec(v_y_867_);
                    return v_x_866_;
                } else {
                    if leanh::lean_obj_tag(v_y_867_) == 0 {
                        return v_y_867_;
                    } else {
                        v_n_868_ = leanh::lean_ctor_get(v_x_866_, 0);
                        v_k_869_ = leanh::lean_ctor_get(v_x_866_, 1);
                        v_n_870_ = leanh::lean_ctor_get(v_y_867_, 0);
                        v_k_871_ = leanh::lean_ctor_get(v_y_867_, 1);
                        v_isSharedCheck_880_ = (!leanh::lean_is_exclusive(v_y_867_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_873_ = v_y_867_;
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_871_);
                            leanh::lean_inc(v_n_870_);
                            leanh::lean_dec(v_y_867_);
                            v___x_873_ = leanh::lean_box(0);
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_875_ = lean_int_mul(v_n_868_, v_n_870_);
                leanh::lean_dec(v_n_870_);
                v___x_876_ = lean_int_add(v_k_869_, v_k_871_);
                leanh::lean_dec(v_k_871_);
                if v_isShared_874_ == 0 {
                    leanh::lean_ctor_set(v___x_873_, 1, v___x_876_);
                    leanh::lean_ctor_set(v___x_873_, 0, v___x_875_);
                    v___x_878_ = v___x_873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
                    v___x_878_ = v_reuseFailAlloc_879_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_878_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_mul___boxed(
    mut v_x_881_: *mut leanh::LeanObject,
    mut v_y_882_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Dyadic_mul(v_x_881_, v_y_882_);
    leanh::lean_dec(v_x_881_);
    return v_res_883_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_887_ = l_Dyadic_ofInt(v___x_886_);
    return v___x_887_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__1() -> *mut leanh::LeanObject {
    let mut v___x_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = leanh::lean_unsigned_to_nat(1);
    v___x_889_ = lean_nat_to_int(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__2() -> *mut leanh::LeanObject {
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1),
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1_once),
        _init_l_Dyadic_pow___closed__1,
    );
    v___x_891_ = l_Dyadic_ofInt(v___x_890_);
    return v___x_891_;
}
pub unsafe fn l_Dyadic_pow(
    mut v_x_892_: *mut leanh::LeanObject,
    mut v_i_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_902_: u8 = 0;
    let mut v___x_903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_892_) == 0 {
                    v___x_894_ = leanh::lean_unsigned_to_nat(0);
                    v___x_895_ = lean_nat_dec_eq(v_i_893_, v___x_894_);
                    leanh::lean_dec(v_i_893_);
                    if v___x_895_ == 0 {
                        v___x_896_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0_once),
                            _init_l_Dyadic_pow___closed__0,
                        );
                        return v___x_896_;
                    } else {
                        v___x_897_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2_once),
                            _init_l_Dyadic_pow___closed__2,
                        );
                        return v___x_897_;
                    }
                } else {
                    v_n_898_ = leanh::lean_ctor_get(v_x_892_, 0);
                    v_k_899_ = leanh::lean_ctor_get(v_x_892_, 1);
                    v_isSharedCheck_909_ = (!leanh::lean_is_exclusive(v_x_892_)) as u8;
                    if v_isSharedCheck_909_ == 0 {
                        v___x_901_ = v_x_892_;
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_899_);
                        leanh::lean_inc(v_n_898_);
                        leanh::lean_dec(v_x_892_);
                        v___x_901_ = leanh::lean_box(0);
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_903_ = l_Int_pow(v_n_898_, v_i_893_);
                leanh::lean_dec(v_n_898_);
                v___x_904_ = lean_nat_to_int(v_i_893_);
                v___x_905_ = lean_int_mul(v_k_899_, v___x_904_);
                leanh::lean_dec(v___x_904_);
                leanh::lean_dec(v_k_899_);
                if v_isShared_902_ == 0 {
                    leanh::lean_ctor_set(v___x_901_, 1, v___x_905_);
                    leanh::lean_ctor_set(v___x_901_, 0, v___x_903_);
                    v___x_907_ = v___x_901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_903_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
                    v___x_907_ = v_reuseFailAlloc_908_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_neg(
    mut v_x_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_917_: u8 = 0;
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_912_) == 0 {
                    return v_x_912_;
                } else {
                    v_n_913_ = leanh::lean_ctor_get(v_x_912_, 0);
                    v_k_914_ = leanh::lean_ctor_get(v_x_912_, 1);
                    v_isSharedCheck_922_ = (!leanh::lean_is_exclusive(v_x_912_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_916_ = v_x_912_;
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_914_);
                        leanh::lean_inc(v_n_913_);
                        leanh::lean_dec(v_x_912_);
                        v___x_916_ = leanh::lean_box(0);
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_918_ = lean_int_neg(v_n_913_);
                leanh::lean_dec(v_n_913_);
                if v_isShared_917_ == 0 {
                    leanh::lean_ctor_set(v___x_916_, 0, v___x_918_);
                    v___x_920_ = v___x_916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_914_);
                    v___x_920_ = v_reuseFailAlloc_921_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_920_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_sub(
    mut v_x_925_: *mut leanh::LeanObject,
    mut v_y_926_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Dyadic_neg(v_y_926_);
    v___x_928_ = l_Dyadic_add(v_x_925_, v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_Dyadic_shiftLeft(
    mut v_x_931_: *mut leanh::LeanObject,
    mut v_i_932_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_931_) == 0 {
                    return v_x_931_;
                } else {
                    v_n_933_ = leanh::lean_ctor_get(v_x_931_, 0);
                    v_k_934_ = leanh::lean_ctor_get(v_x_931_, 1);
                    v_isSharedCheck_942_ = (!leanh::lean_is_exclusive(v_x_931_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v___x_936_ = v_x_931_;
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_934_);
                        leanh::lean_inc(v_n_933_);
                        leanh::lean_dec(v_x_931_);
                        v___x_936_ = leanh::lean_box(0);
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_938_ = lean_int_sub(v_k_934_, v_i_932_);
                leanh::lean_dec(v_k_934_);
                if v_isShared_937_ == 0 {
                    leanh::lean_ctor_set(v___x_936_, 1, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v_n_933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
                    v___x_940_ = v_reuseFailAlloc_941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_shiftLeft___boxed(
    mut v_x_943_: *mut leanh::LeanObject,
    mut v_i_944_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_945_ = l_Dyadic_shiftLeft(v_x_943_, v_i_944_);
    leanh::lean_dec(v_i_944_);
    return v_res_945_;
}
pub unsafe fn l_Dyadic_shiftRight(
    mut v_x_946_: *mut leanh::LeanObject,
    mut v_i_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_946_) == 0 {
                    return v_x_946_;
                } else {
                    v_n_948_ = leanh::lean_ctor_get(v_x_946_, 0);
                    v_k_949_ = leanh::lean_ctor_get(v_x_946_, 1);
                    v_isSharedCheck_957_ = (!leanh::lean_is_exclusive(v_x_946_)) as u8;
                    if v_isSharedCheck_957_ == 0 {
                        v___x_951_ = v_x_946_;
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_949_);
                        leanh::lean_inc(v_n_948_);
                        leanh::lean_dec(v_x_946_);
                        v___x_951_ = leanh::lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_953_ = lean_int_add(v_k_949_, v_i_947_);
                leanh::lean_dec(v_k_949_);
                if v_isShared_952_ == 0 {
                    leanh::lean_ctor_set(v___x_951_, 1, v___x_953_);
                    v___x_955_ = v___x_951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_n_948_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
                    v___x_955_ = v_reuseFailAlloc_956_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Dyadic_shiftRight___boxed(
    mut v_x_958_: *mut leanh::LeanObject,
    mut v_i_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Dyadic_shiftRight(v_x_958_, v_i_959_);
    leanh::lean_dec(v_i_959_);
    return v_res_960_;
}
pub unsafe fn l_Dyadic_instHShiftLeftNat___lam__0(
    mut v_x_965_: *mut leanh::LeanObject,
    mut v_y_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = lean_nat_to_int(v_y_966_);
    v___x_968_ = l_Dyadic_shiftLeft(v_x_965_, v___x_967_);
    leanh::lean_dec(v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Dyadic_instHShiftRightNat___lam__0(
    mut v_x_971_: *mut leanh::LeanObject,
    mut v_y_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_nat_to_int(v_y_972_);
    v___x_974_ = l_Dyadic_shiftRight(v_x_971_, v___x_973_);
    leanh::lean_dec(v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Int_cast___at___00Dyadic_toRat_spec__1(
    mut v_a_977_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l_Rat_ofInt(v_a_977_);
    return v___x_978_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_toRat_spec__0(
    mut v_a_979_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = lean_nat_to_int(v_a_979_);
    v___x_981_ = l_Rat_ofInt(v___x_980_);
    return v___x_981_;
}
pub unsafe fn _init_l_Dyadic_toRat___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = leanh::lean_unsigned_to_nat(0);
    v___x_983_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_982_);
    return v___x_983_;
}
pub unsafe fn l_Dyadic_toRat(
    mut v_x_984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v_intZero_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_992_: u8 = 0;
    let mut v_a_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_984_) == 0 {
                    v___x_985_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0),
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0_once),
                        _init_l_Dyadic_toRat___closed__0,
                    );
                    return v___x_985_;
                } else {
                    v_n_986_ = leanh::lean_ctor_get(v_x_984_, 0);
                    v_k_987_ = leanh::lean_ctor_get(v_x_984_, 1);
                    v_isSharedCheck_1008_ = (!leanh::lean_is_exclusive(v_x_984_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_989_ = v_x_984_;
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_k_987_);
                        leanh::lean_inc(v_n_986_);
                        leanh::lean_dec(v_x_984_);
                        v___x_989_ = leanh::lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_intZero_991_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_992_ = lean_int_dec_lt(v_k_987_, v_intZero_991_);
                if v_isNeg_992_ == 0 {
                    v_a_993_ = lean_nat_abs(v_k_987_);
                    leanh::lean_dec(v_k_987_);
                    v___x_994_ = leanh::lean_unsigned_to_nat(2);
                    v___x_995_ = lean_nat_pow(v___x_994_, v_a_993_);
                    leanh::lean_dec(v_a_993_);
                    if v_isShared_990_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_989_, 0);
                        leanh::lean_ctor_set(v___x_989_, 1, v___x_995_);
                        v___x_997_ = v___x_989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_998_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_998_, 0, v_n_986_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
                        v___x_997_ = v_reuseFailAlloc_998_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_989_);
                    v_abs_999_ = lean_nat_abs(v_k_987_);
                    leanh::lean_dec(v_k_987_);
                    v_one_1000_ = leanh::lean_unsigned_to_nat(1);
                    v_a_1001_ = lean_nat_sub(v_abs_999_, v_one_1000_);
                    leanh::lean_dec(v_abs_999_);
                    v___x_1002_ = leanh::lean_unsigned_to_nat(2);
                    v___x_1003_ = lean_nat_add(v_a_1001_, v_one_1000_);
                    leanh::lean_dec(v_a_1001_);
                    v___x_1004_ = lean_nat_pow(v___x_1002_, v___x_1003_);
                    leanh::lean_dec(v___x_1003_);
                    v___x_1005_ = lean_nat_to_int(v___x_1004_);
                    v___x_1006_ = lean_int_mul(v_n_986_, v___x_1005_);
                    leanh::lean_dec(v___x_1005_);
                    leanh::lean_dec(v_n_986_);
                    v___x_1007_ = l_Rat_ofInt(v___x_1006_);
                    return v___x_1007_;
                }
            }
            2 => {
                return v___x_997_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter___redArg(
    mut v_x_1009_: *mut leanh::LeanObject,
    mut v_h__1_1010_: *mut leanh::LeanObject,
    mut v_h__2_1011_: *mut leanh::LeanObject,
    mut v_h__3_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1009_) == 0 {
        let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1012_);
        leanh::lean_dec(v_h__2_1011_);
        v___x_1013_ = leanh::lean_box(0);
        v___x_1014_ = leanh::lean_apply_1(v_h__1_1010_, v___x_1013_);
        return v___x_1014_;
    } else {
        let mut v_n_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1018_: u8 = 0;
        leanh::lean_dec(v_h__1_1010_);
        v_n_1015_ = leanh::lean_ctor_get(v_x_1009_, 0);
        leanh::lean_inc(v_n_1015_);
        v_k_1016_ = leanh::lean_ctor_get(v_x_1009_, 1);
        leanh::lean_inc(v_k_1016_);
        leanh::lean_dec_ref_known(v_x_1009_, 2);
        v_intZero_1017_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1018_ = lean_int_dec_lt(v_k_1016_, v_intZero_1017_);
        if v_isNeg_1018_ == 0 {
            let mut v_a_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1012_);
            v_a_1019_ = lean_nat_abs(v_k_1016_);
            leanh::lean_dec(v_k_1016_);
            v___x_1020_ = leanh::lean_apply_3(
                v_h__2_1011_,
                v_n_1015_,
                v_a_1019_,
                leanh::lean_box(0),
            );
            return v___x_1020_;
        } else {
            let mut v_abs_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1011_);
            v_abs_1021_ = lean_nat_abs(v_k_1016_);
            leanh::lean_dec(v_k_1016_);
            v_one_1022_ = leanh::lean_unsigned_to_nat(1);
            v_a_1023_ = lean_nat_sub(v_abs_1021_, v_one_1022_);
            leanh::lean_dec(v_abs_1021_);
            v___x_1024_ = leanh::lean_apply_3(
                v_h__3_1012_,
                v_n_1015_,
                v_a_1023_,
                leanh::lean_box(0),
            );
            return v___x_1024_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(
    mut v_motive_1025_: *mut leanh::LeanObject,
    mut v_x_1026_: *mut leanh::LeanObject,
    mut v_h__1_1027_: *mut leanh::LeanObject,
    mut v_h__2_1028_: *mut leanh::LeanObject,
    mut v_h__3_1029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1026_) == 0 {
        let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__3_1029_);
        leanh::lean_dec(v_h__2_1028_);
        v___x_1030_ = leanh::lean_box(0);
        v___x_1031_ = leanh::lean_apply_1(v_h__1_1027_, v___x_1030_);
        return v___x_1031_;
    } else {
        let mut v_n_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1035_: u8 = 0;
        leanh::lean_dec(v_h__1_1027_);
        v_n_1032_ = leanh::lean_ctor_get(v_x_1026_, 0);
        leanh::lean_inc(v_n_1032_);
        v_k_1033_ = leanh::lean_ctor_get(v_x_1026_, 1);
        leanh::lean_inc(v_k_1033_);
        leanh::lean_dec_ref_known(v_x_1026_, 2);
        v_intZero_1034_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1035_ = lean_int_dec_lt(v_k_1033_, v_intZero_1034_);
        if v_isNeg_1035_ == 0 {
            let mut v_a_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1029_);
            v_a_1036_ = lean_nat_abs(v_k_1033_);
            leanh::lean_dec(v_k_1033_);
            v___x_1037_ = leanh::lean_apply_3(
                v_h__2_1028_,
                v_n_1032_,
                v_a_1036_,
                leanh::lean_box(0),
            );
            return v___x_1037_;
        } else {
            let mut v_abs_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1028_);
            v_abs_1038_ = lean_nat_abs(v_k_1033_);
            leanh::lean_dec(v_k_1033_);
            v_one_1039_ = leanh::lean_unsigned_to_nat(1);
            v_a_1040_ = lean_nat_sub(v_abs_1038_, v_one_1039_);
            leanh::lean_dec(v_abs_1038_);
            v___x_1041_ = leanh::lean_apply_3(
                v_h__3_1029_,
                v_n_1032_,
                v_a_1040_,
                leanh::lean_box(0),
            );
            return v___x_1041_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(
    mut v_x_1042_: *mut leanh::LeanObject,
    mut v_y_1043_: *mut leanh::LeanObject,
    mut v_h__1_1044_: *mut leanh::LeanObject,
    mut v_h__2_1045_: *mut leanh::LeanObject,
    mut v_h__3_1046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut v_n_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1042_) == 0 {
                    leanh::lean_dec(v_h__3_1046_);
                    leanh::lean_dec(v_h__2_1045_);
                    v___x_1047_ = leanh::lean_apply_1(v_h__1_1044_, v_y_1043_);
                    return v___x_1047_;
                } else {
                    leanh::lean_dec(v_h__1_1044_);
                    if leanh::lean_obj_tag(v_y_1043_) == 0 {
                        leanh::lean_dec(v_h__3_1046_);
                        v_n_1048_ = leanh::lean_ctor_get(v_x_1042_, 0);
                        v_k_1049_ = leanh::lean_ctor_get(v_x_1042_, 1);
                        v_isSharedCheck_1057_ = (!leanh::lean_is_exclusive(v_x_1042_)) as u8;
                        if v_isSharedCheck_1057_ == 0 {
                            v___x_1051_ = v_x_1042_;
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_1049_);
                            leanh::lean_inc(v_n_1048_);
                            leanh::lean_dec(v_x_1042_);
                            v___x_1051_ = leanh::lean_box(0);
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_h__2_1045_);
                        v_n_1058_ = leanh::lean_ctor_get(v_x_1042_, 0);
                        leanh::lean_inc(v_n_1058_);
                        v_k_1059_ = leanh::lean_ctor_get(v_x_1042_, 1);
                        leanh::lean_inc(v_k_1059_);
                        leanh::lean_dec_ref_known(v_x_1042_, 2);
                        v_n_1060_ = leanh::lean_ctor_get(v_y_1043_, 0);
                        leanh::lean_inc(v_n_1060_);
                        v_k_1061_ = leanh::lean_ctor_get(v_y_1043_, 1);
                        leanh::lean_inc(v_k_1061_);
                        leanh::lean_dec_ref_known(v_y_1043_, 2);
                        v___x_1062_ = leanh::lean_apply_6(
                            v_h__3_1046_,
                            v_n_1058_,
                            v_k_1059_,
                            leanh::lean_box(0),
                            v_n_1060_,
                            v_k_1061_,
                            leanh::lean_box(0),
                        );
                        return v___x_1062_;
                    }
                }
            }
            1 => {
                if v_isShared_1052_ == 0 {
                    v___x_1054_ = v___x_1051_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1056_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_n_1048_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1055_ = leanh::lean_apply_2(
                    v_h__2_1045_,
                    v___x_1054_,
                    leanh::lean_box(0),
                );
                return v___x_1055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(
    mut v_motive_1063_: *mut leanh::LeanObject,
    mut v_x_1064_: *mut leanh::LeanObject,
    mut v_y_1065_: *mut leanh::LeanObject,
    mut v_h__1_1066_: *mut leanh::LeanObject,
    mut v_h__2_1067_: *mut leanh::LeanObject,
    mut v_h__3_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_n_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1064_) == 0 {
                    leanh::lean_dec(v_h__3_1068_);
                    leanh::lean_dec(v_h__2_1067_);
                    v___x_1069_ = leanh::lean_apply_1(v_h__1_1066_, v_y_1065_);
                    return v___x_1069_;
                } else {
                    leanh::lean_dec(v_h__1_1066_);
                    if leanh::lean_obj_tag(v_y_1065_) == 0 {
                        leanh::lean_dec(v_h__3_1068_);
                        v_n_1070_ = leanh::lean_ctor_get(v_x_1064_, 0);
                        v_k_1071_ = leanh::lean_ctor_get(v_x_1064_, 1);
                        v_isSharedCheck_1079_ = (!leanh::lean_is_exclusive(v_x_1064_)) as u8;
                        if v_isSharedCheck_1079_ == 0 {
                            v___x_1073_ = v_x_1064_;
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_k_1071_);
                            leanh::lean_inc(v_n_1070_);
                            leanh::lean_dec(v_x_1064_);
                            v___x_1073_ = leanh::lean_box(0);
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_h__2_1067_);
                        v_n_1080_ = leanh::lean_ctor_get(v_x_1064_, 0);
                        leanh::lean_inc(v_n_1080_);
                        v_k_1081_ = leanh::lean_ctor_get(v_x_1064_, 1);
                        leanh::lean_inc(v_k_1081_);
                        leanh::lean_dec_ref_known(v_x_1064_, 2);
                        v_n_1082_ = leanh::lean_ctor_get(v_y_1065_, 0);
                        leanh::lean_inc(v_n_1082_);
                        v_k_1083_ = leanh::lean_ctor_get(v_y_1065_, 1);
                        leanh::lean_inc(v_k_1083_);
                        leanh::lean_dec_ref_known(v_y_1065_, 2);
                        v___x_1084_ = leanh::lean_apply_6(
                            v_h__3_1068_,
                            v_n_1080_,
                            v_k_1081_,
                            leanh::lean_box(0),
                            v_n_1082_,
                            v_k_1083_,
                            leanh::lean_box(0),
                        );
                        return v___x_1084_;
                    }
                }
            }
            1 => {
                if v_isShared_1074_ == 0 {
                    v___x_1076_ = v___x_1073_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1078_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_n_1070_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1077_ = leanh::lean_apply_2(
                    v_h__2_1067_,
                    v___x_1076_,
                    leanh::lean_box(0),
                );
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
    mut v_x_1085_: *mut leanh::LeanObject,
    mut v_h__1_1086_: *mut leanh::LeanObject,
    mut v_h__2_1087_: *mut leanh::LeanObject,
    mut v_h__3_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1091_: u8 = 0;
    v_natZero_1089_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_1090_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1091_ = lean_int_dec_lt(v_x_1085_, v_intZero_1090_);
    if v_isNeg_1091_ == 0 {
        let mut v_a_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1093_: u8 = 0;
        leanh::lean_dec(v_h__3_1088_);
        v_a_1092_ = lean_nat_abs(v_x_1085_);
        v_isZero_1093_ = lean_nat_dec_eq(v_a_1092_, v_natZero_1089_);
        if v_isZero_1093_ == 1 {
            let mut v___x_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_1092_);
            leanh::lean_dec(v_h__2_1087_);
            v___x_1094_ = leanh::lean_box(0);
            v___x_1095_ = leanh::lean_apply_1(v_h__1_1086_, v___x_1094_);
            return v___x_1095_;
        } else {
            let mut v_one_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1086_);
            v_one_1096_ = leanh::lean_unsigned_to_nat(1);
            v_n_1097_ = lean_nat_sub(v_a_1092_, v_one_1096_);
            leanh::lean_dec(v_a_1092_);
            v___x_1098_ = leanh::lean_apply_1(v_h__2_1087_, v_n_1097_);
            return v___x_1098_;
        }
    } else {
        let mut v_abs_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1087_);
        leanh::lean_dec(v_h__1_1086_);
        v_abs_1099_ = lean_nat_abs(v_x_1085_);
        v_one_1100_ = leanh::lean_unsigned_to_nat(1);
        v_a_1101_ = lean_nat_sub(v_abs_1099_, v_one_1100_);
        leanh::lean_dec(v_abs_1099_);
        v___x_1102_ = leanh::lean_apply_1(v_h__3_1088_, v_a_1101_);
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(
    mut v_x_1103_: *mut leanh::LeanObject,
    mut v_h__1_1104_: *mut leanh::LeanObject,
    mut v_h__2_1105_: *mut leanh::LeanObject,
    mut v_h__3_1106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
        v_x_1103_,
        v_h__1_1104_,
        v_h__2_1105_,
        v_h__3_1106_,
    );
    leanh::lean_dec(v_x_1103_);
    return v_res_1107_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
    mut v_motive_1108_: *mut leanh::LeanObject,
    mut v_x_1109_: *mut leanh::LeanObject,
    mut v_h__1_1110_: *mut leanh::LeanObject,
    mut v_h__2_1111_: *mut leanh::LeanObject,
    mut v_h__3_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1115_: u8 = 0;
    v_natZero_1113_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_1114_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1115_ = lean_int_dec_lt(v_x_1109_, v_intZero_1114_);
    if v_isNeg_1115_ == 0 {
        let mut v_a_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1117_: u8 = 0;
        leanh::lean_dec(v_h__3_1112_);
        v_a_1116_ = lean_nat_abs(v_x_1109_);
        v_isZero_1117_ = lean_nat_dec_eq(v_a_1116_, v_natZero_1113_);
        if v_isZero_1117_ == 1 {
            let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_a_1116_);
            leanh::lean_dec(v_h__2_1111_);
            v___x_1118_ = leanh::lean_box(0);
            v___x_1119_ = leanh::lean_apply_1(v_h__1_1110_, v___x_1118_);
            return v___x_1119_;
        } else {
            let mut v_one_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1110_);
            v_one_1120_ = leanh::lean_unsigned_to_nat(1);
            v_n_1121_ = lean_nat_sub(v_a_1116_, v_one_1120_);
            leanh::lean_dec(v_a_1116_);
            v___x_1122_ = leanh::lean_apply_1(v_h__2_1111_, v_n_1121_);
            return v___x_1122_;
        }
    } else {
        let mut v_abs_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1111_);
        leanh::lean_dec(v_h__1_1110_);
        v_abs_1123_ = lean_nat_abs(v_x_1109_);
        v_one_1124_ = leanh::lean_unsigned_to_nat(1);
        v_a_1125_ = lean_nat_sub(v_abs_1123_, v_one_1124_);
        leanh::lean_dec(v_abs_1123_);
        v___x_1126_ = leanh::lean_apply_1(v_h__3_1112_, v_a_1125_);
        return v___x_1126_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(
    mut v_motive_1127_: *mut leanh::LeanObject,
    mut v_x_1128_: *mut leanh::LeanObject,
    mut v_h__1_1129_: *mut leanh::LeanObject,
    mut v_h__2_1130_: *mut leanh::LeanObject,
    mut v_h__3_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
        v_motive_1127_,
        v_x_1128_,
        v_h__1_1129_,
        v_h__2_1130_,
        v_h__3_1131_,
    );
    leanh::lean_dec(v_x_1128_);
    return v_res_1132_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(
    mut v_x_1133_: *mut leanh::LeanObject,
    mut v_h__1_1134_: *mut leanh::LeanObject,
    mut v_h__2_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1133_) == 0 {
        let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1135_);
        v___x_1136_ = leanh::lean_box(0);
        v___x_1137_ = leanh::lean_apply_1(v_h__1_1134_, v___x_1136_);
        return v___x_1137_;
    } else {
        let mut v_n_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1134_);
        v_n_1138_ = leanh::lean_ctor_get(v_x_1133_, 0);
        leanh::lean_inc(v_n_1138_);
        v_k_1139_ = leanh::lean_ctor_get(v_x_1133_, 1);
        leanh::lean_inc(v_k_1139_);
        leanh::lean_dec_ref_known(v_x_1133_, 2);
        v___x_1140_ = leanh::lean_apply_3(
            v_h__2_1135_,
            v_n_1138_,
            v_k_1139_,
            leanh::lean_box(0),
        );
        return v___x_1140_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(
    mut v_motive_1141_: *mut leanh::LeanObject,
    mut v_x_1142_: *mut leanh::LeanObject,
    mut v_h__1_1143_: *mut leanh::LeanObject,
    mut v_h__2_1144_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1142_) == 0 {
        let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1144_);
        v___x_1145_ = leanh::lean_box(0);
        v___x_1146_ = leanh::lean_apply_1(v_h__1_1143_, v___x_1145_);
        return v___x_1146_;
    } else {
        let mut v_n_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1148_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1143_);
        v_n_1147_ = leanh::lean_ctor_get(v_x_1142_, 0);
        leanh::lean_inc(v_n_1147_);
        v_k_1148_ = leanh::lean_ctor_get(v_x_1142_, 1);
        leanh::lean_inc(v_k_1148_);
        leanh::lean_dec_ref_known(v_x_1142_, 2);
        v___x_1149_ = leanh::lean_apply_3(
            v_h__2_1144_,
            v_n_1147_,
            v_k_1148_,
            leanh::lean_box(0),
        );
        return v___x_1149_;
    }
}
pub unsafe fn l_Dyadic_precision(
    mut v_x_1150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1150_) == 0 {
        let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1151_ = leanh::lean_box(0);
        return v___x_1151_;
    } else {
        let mut v_k_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_k_1152_ = leanh::lean_ctor_get(v_x_1150_, 1);
        leanh::lean_inc(v_k_1152_);
        v___x_1153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1153_, 0, v_k_1152_);
        return v___x_1153_;
    }
}
pub unsafe fn l_Dyadic_precision___boxed(
    mut v_x_1154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Dyadic_precision(v_x_1154_);
    leanh::lean_dec(v_x_1154_);
    return v_res_1155_;
}
pub unsafe fn l_Rat_toDyadic(
    mut v_x_1156_: *mut leanh::LeanObject,
    mut v_prec_1157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1159_: u8 = 0;
    v_intZero_1158_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1159_ = lean_int_dec_lt(v_prec_1157_, v_intZero_1158_);
    if v_isNeg_1159_ == 0 {
        let mut v_num_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_den_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_num_1160_ = leanh::lean_ctor_get(v_x_1156_, 0);
        leanh::lean_inc(v_num_1160_);
        v_den_1161_ = leanh::lean_ctor_get(v_x_1156_, 1);
        leanh::lean_inc(v_den_1161_);
        leanh::lean_dec_ref(v_x_1156_);
        v_a_1162_ = lean_nat_abs(v_prec_1157_);
        v___x_1163_ = l_Int_shiftLeft(v_num_1160_, v_a_1162_);
        leanh::lean_dec(v_a_1162_);
        leanh::lean_dec(v_num_1160_);
        v___x_1164_ = lean_nat_to_int(v_den_1161_);
        v___x_1165_ = lean_int_ediv(v___x_1163_, v___x_1164_);
        leanh::lean_dec(v___x_1164_);
        leanh::lean_dec(v___x_1163_);
        v___x_1166_ = l_Dyadic_ofIntWithPrec(v___x_1165_, v_prec_1157_);
        return v___x_1166_;
    } else {
        let mut v_num_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_den_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_abs_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_num_1167_ = leanh::lean_ctor_get(v_x_1156_, 0);
        leanh::lean_inc(v_num_1167_);
        v_den_1168_ = leanh::lean_ctor_get(v_x_1156_, 1);
        leanh::lean_inc(v_den_1168_);
        leanh::lean_dec_ref(v_x_1156_);
        v_abs_1169_ = lean_nat_abs(v_prec_1157_);
        v_one_1170_ = leanh::lean_unsigned_to_nat(1);
        v_a_1171_ = lean_nat_sub(v_abs_1169_, v_one_1170_);
        leanh::lean_dec(v_abs_1169_);
        v___x_1172_ = lean_nat_add(v_a_1171_, v_one_1170_);
        leanh::lean_dec(v_a_1171_);
        v___x_1173_ = lean_nat_shiftl(v_den_1168_, v___x_1172_);
        leanh::lean_dec(v___x_1172_);
        leanh::lean_dec(v_den_1168_);
        v___x_1174_ = lean_nat_to_int(v___x_1173_);
        v___x_1175_ = lean_int_ediv(v_num_1167_, v___x_1174_);
        leanh::lean_dec(v___x_1174_);
        leanh::lean_dec(v_num_1167_);
        v___x_1176_ = l_Dyadic_ofIntWithPrec(v___x_1175_, v_prec_1157_);
        return v___x_1176_;
    }
}
pub unsafe fn l_Rat_toDyadic___boxed(
    mut v_x_1177_: *mut leanh::LeanObject,
    mut v_prec_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Rat_toDyadic(v_x_1177_, v_prec_1178_);
    leanh::lean_dec(v_prec_1178_);
    return v_res_1179_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
    mut v_prec_1180_: *mut leanh::LeanObject,
    mut v_h__1_1181_: *mut leanh::LeanObject,
    mut v_h__2_1182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1184_: u8 = 0;
    v_intZero_1183_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1184_ = lean_int_dec_lt(v_prec_1180_, v_intZero_1183_);
    if v_isNeg_1184_ == 0 {
        let mut v_a_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1182_);
        v_a_1185_ = lean_nat_abs(v_prec_1180_);
        v___x_1186_ = leanh::lean_apply_1(v_h__1_1181_, v_a_1185_);
        return v___x_1186_;
    } else {
        let mut v_abs_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1181_);
        v_abs_1187_ = lean_nat_abs(v_prec_1180_);
        v_one_1188_ = leanh::lean_unsigned_to_nat(1);
        v_a_1189_ = lean_nat_sub(v_abs_1187_, v_one_1188_);
        leanh::lean_dec(v_abs_1187_);
        v___x_1190_ = leanh::lean_apply_1(v_h__2_1182_, v_a_1189_);
        return v___x_1190_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(
    mut v_prec_1191_: *mut leanh::LeanObject,
    mut v_h__1_1192_: *mut leanh::LeanObject,
    mut v_h__2_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
        v_prec_1191_,
        v_h__1_1192_,
        v_h__2_1193_,
    );
    leanh::lean_dec(v_prec_1191_);
    return v_res_1194_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
    mut v_motive_1195_: *mut leanh::LeanObject,
    mut v_prec_1196_: *mut leanh::LeanObject,
    mut v_h__1_1197_: *mut leanh::LeanObject,
    mut v_h__2_1198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1200_: u8 = 0;
    v_intZero_1199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1200_ = lean_int_dec_lt(v_prec_1196_, v_intZero_1199_);
    if v_isNeg_1200_ == 0 {
        let mut v_a_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1198_);
        v_a_1201_ = lean_nat_abs(v_prec_1196_);
        v___x_1202_ = leanh::lean_apply_1(v_h__1_1197_, v_a_1201_);
        return v___x_1202_;
    } else {
        let mut v_abs_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1197_);
        v_abs_1203_ = lean_nat_abs(v_prec_1196_);
        v_one_1204_ = leanh::lean_unsigned_to_nat(1);
        v_a_1205_ = lean_nat_sub(v_abs_1203_, v_one_1204_);
        leanh::lean_dec(v_abs_1203_);
        v___x_1206_ = leanh::lean_apply_1(v_h__2_1198_, v_a_1205_);
        return v___x_1206_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(
    mut v_motive_1207_: *mut leanh::LeanObject,
    mut v_prec_1208_: *mut leanh::LeanObject,
    mut v_h__1_1209_: *mut leanh::LeanObject,
    mut v_h__2_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
        v_motive_1207_,
        v_prec_1208_,
        v_h__1_1209_,
        v_h__2_1210_,
    );
    leanh::lean_dec(v_prec_1208_);
    return v_res_1211_;
}
pub unsafe fn l_Dyadic_roundDown(
    mut v_x_1212_: *mut leanh::LeanObject,
    mut v_prec_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1212_) == 0 {
        return v_x_1212_;
    } else {
        let mut v_n_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1218_: u8 = 0;
        v_n_1214_ = leanh::lean_ctor_get(v_x_1212_, 0);
        v_k_1215_ = leanh::lean_ctor_get(v_x_1212_, 1);
        v___x_1216_ = lean_int_sub(v_k_1215_, v_prec_1213_);
        v_intZero_1217_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1218_ = lean_int_dec_lt(v___x_1216_, v_intZero_1217_);
        if v_isNeg_1218_ == 0 {
            let mut v_a_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1219_ = lean_nat_abs(v___x_1216_);
            leanh::lean_dec(v___x_1216_);
            v___x_1220_ = l_Int_shiftRight(v_n_1214_, v_a_1219_);
            leanh::lean_dec(v_a_1219_);
            v___x_1221_ = l_Dyadic_ofIntWithPrec(v___x_1220_, v_prec_1213_);
            return v___x_1221_;
        } else {
            leanh::lean_dec(v___x_1216_);
            leanh::lean_inc_ref(v_x_1212_);
            return v_x_1212_;
        }
    }
}
pub unsafe fn l_Dyadic_roundDown___boxed(
    mut v_x_1222_: *mut leanh::LeanObject,
    mut v_prec_1223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Dyadic_roundDown(v_x_1222_, v_prec_1223_);
    leanh::lean_dec(v_prec_1223_);
    leanh::lean_dec(v_x_1222_);
    return v_res_1224_;
}
pub unsafe fn l_Dyadic_blt(
    mut v_x_1225_: *mut leanh::LeanObject,
    mut v_y_1226_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1225_) == 0 {
        if leanh::lean_obj_tag(v_y_1226_) == 0 {
            let mut v___x_1227_: u8 = 0;
            v___x_1227_ = 0;
            return v___x_1227_;
        } else {
            let mut v_n_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1230_: u8 = 0;
            v_n_1228_ = leanh::lean_ctor_get(v_y_1226_, 0);
            v___x_1229_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1230_ = lean_int_dec_lt(v___x_1229_, v_n_1228_);
            return v___x_1230_;
        }
    } else {
        if leanh::lean_obj_tag(v_y_1226_) == 0 {
            let mut v_n_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: u8 = 0;
            v_n_1231_ = leanh::lean_ctor_get(v_x_1225_, 0);
            v___x_1232_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1233_ = lean_int_dec_lt(v_n_1231_, v___x_1232_);
            return v___x_1233_;
        } else {
            let mut v_n_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_intZero_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1240_: u8 = 0;
            v_n_1234_ = leanh::lean_ctor_get(v_x_1225_, 0);
            v_k_1235_ = leanh::lean_ctor_get(v_x_1225_, 1);
            v_n_1236_ = leanh::lean_ctor_get(v_y_1226_, 0);
            v_k_1237_ = leanh::lean_ctor_get(v_y_1226_, 1);
            v___x_1238_ = lean_int_sub(v_k_1237_, v_k_1235_);
            v_intZero_1239_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1240_ = lean_int_dec_lt(v___x_1238_, v_intZero_1239_);
            if v_isNeg_1240_ == 0 {
                let mut v_a_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1243_: u8 = 0;
                v_a_1241_ = lean_nat_abs(v___x_1238_);
                leanh::lean_dec(v___x_1238_);
                v___x_1242_ = l_Int_shiftLeft(v_n_1234_, v_a_1241_);
                leanh::lean_dec(v_a_1241_);
                v___x_1243_ = lean_int_dec_lt(v___x_1242_, v_n_1236_);
                leanh::lean_dec(v___x_1242_);
                return v___x_1243_;
            } else {
                let mut v_abs_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1249_: u8 = 0;
                v_abs_1244_ = lean_nat_abs(v___x_1238_);
                leanh::lean_dec(v___x_1238_);
                v_one_1245_ = leanh::lean_unsigned_to_nat(1);
                v_a_1246_ = lean_nat_sub(v_abs_1244_, v_one_1245_);
                leanh::lean_dec(v_abs_1244_);
                v___x_1247_ = lean_nat_add(v_a_1246_, v_one_1245_);
                leanh::lean_dec(v_a_1246_);
                v___x_1248_ = l_Int_shiftLeft(v_n_1236_, v___x_1247_);
                leanh::lean_dec(v___x_1247_);
                v___x_1249_ = lean_int_dec_lt(v_n_1234_, v___x_1248_);
                leanh::lean_dec(v___x_1248_);
                return v___x_1249_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_blt___boxed(
    mut v_x_1250_: *mut leanh::LeanObject,
    mut v_y_1251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1252_: u8 = 0;
    let mut v_r_1253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ = l_Dyadic_blt(v_x_1250_, v_y_1251_);
    leanh::lean_dec(v_y_1251_);
    leanh::lean_dec(v_x_1250_);
    v_r_1253_ = leanh::lean_box((v_res_1252_) as usize);
    return v_r_1253_;
}
pub unsafe fn l_Dyadic_ble(
    mut v_x_1254_: *mut leanh::LeanObject,
    mut v_y_1255_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_x_1254_) == 0 {
        if leanh::lean_obj_tag(v_y_1255_) == 0 {
            let mut v___x_1256_: u8 = 0;
            v___x_1256_ = 1;
            return v___x_1256_;
        } else {
            let mut v_n_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1259_: u8 = 0;
            v_n_1257_ = leanh::lean_ctor_get(v_y_1255_, 0);
            v___x_1258_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1259_ = lean_int_dec_le(v___x_1258_, v_n_1257_);
            return v___x_1259_;
        }
    } else {
        if leanh::lean_obj_tag(v_y_1255_) == 0 {
            let mut v_n_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: u8 = 0;
            v_n_1260_ = leanh::lean_ctor_get(v_x_1254_, 0);
            v___x_1261_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1262_ = lean_int_dec_le(v_n_1260_, v___x_1261_);
            return v___x_1262_;
        } else {
            let mut v_n_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_intZero_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1269_: u8 = 0;
            v_n_1263_ = leanh::lean_ctor_get(v_x_1254_, 0);
            v_k_1264_ = leanh::lean_ctor_get(v_x_1254_, 1);
            v_n_1265_ = leanh::lean_ctor_get(v_y_1255_, 0);
            v_k_1266_ = leanh::lean_ctor_get(v_y_1255_, 1);
            v___x_1267_ = lean_int_sub(v_k_1266_, v_k_1264_);
            v_intZero_1268_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1269_ = lean_int_dec_lt(v___x_1267_, v_intZero_1268_);
            if v_isNeg_1269_ == 0 {
                let mut v_a_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1272_: u8 = 0;
                v_a_1270_ = lean_nat_abs(v___x_1267_);
                leanh::lean_dec(v___x_1267_);
                v___x_1271_ = l_Int_shiftLeft(v_n_1263_, v_a_1270_);
                leanh::lean_dec(v_a_1270_);
                v___x_1272_ = lean_int_dec_le(v___x_1271_, v_n_1265_);
                leanh::lean_dec(v___x_1271_);
                return v___x_1272_;
            } else {
                let mut v_abs_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1278_: u8 = 0;
                v_abs_1273_ = lean_nat_abs(v___x_1267_);
                leanh::lean_dec(v___x_1267_);
                v_one_1274_ = leanh::lean_unsigned_to_nat(1);
                v_a_1275_ = lean_nat_sub(v_abs_1273_, v_one_1274_);
                leanh::lean_dec(v_abs_1273_);
                v___x_1276_ = lean_nat_add(v_a_1275_, v_one_1274_);
                leanh::lean_dec(v_a_1275_);
                v___x_1277_ = l_Int_shiftLeft(v_n_1265_, v___x_1276_);
                leanh::lean_dec(v___x_1276_);
                v___x_1278_ = lean_int_dec_le(v_n_1263_, v___x_1277_);
                leanh::lean_dec(v___x_1277_);
                return v___x_1278_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_ble___boxed(
    mut v_x_1279_: *mut leanh::LeanObject,
    mut v_y_1280_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1281_: u8 = 0;
    let mut v_r_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Dyadic_ble(v_x_1279_, v_y_1280_);
    leanh::lean_dec(v_y_1280_);
    leanh::lean_dec(v_x_1279_);
    v_r_1282_ = leanh::lean_box((v_res_1281_) as usize);
    return v_r_1282_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(
    mut v_x_1283_: *mut leanh::LeanObject,
    mut v_x_1284_: *mut leanh::LeanObject,
    mut v_h__1_1285_: *mut leanh::LeanObject,
    mut v_h__2_1286_: *mut leanh::LeanObject,
    mut v_h__3_1287_: *mut leanh::LeanObject,
    mut v_h__4_1288_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1283_) == 0 {
        leanh::lean_dec(v_h__4_1288_);
        leanh::lean_dec(v_h__3_1287_);
        if leanh::lean_obj_tag(v_x_1284_) == 0 {
            let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1286_);
            v___x_1289_ = leanh::lean_box(0);
            v___x_1290_ = leanh::lean_apply_1(v_h__1_1285_, v___x_1289_);
            return v___x_1290_;
        } else {
            let mut v_n_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1285_);
            v_n_1291_ = leanh::lean_ctor_get(v_x_1284_, 0);
            leanh::lean_inc(v_n_1291_);
            v_k_1292_ = leanh::lean_ctor_get(v_x_1284_, 1);
            leanh::lean_inc(v_k_1292_);
            leanh::lean_dec_ref_known(v_x_1284_, 2);
            v___x_1293_ = leanh::lean_apply_3(
                v_h__2_1286_,
                v_n_1291_,
                v_k_1292_,
                leanh::lean_box(0),
            );
            return v___x_1293_;
        }
    } else {
        leanh::lean_dec(v_h__2_1286_);
        leanh::lean_dec(v_h__1_1285_);
        if leanh::lean_obj_tag(v_x_1284_) == 0 {
            let mut v_n_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1288_);
            v_n_1294_ = leanh::lean_ctor_get(v_x_1283_, 0);
            leanh::lean_inc(v_n_1294_);
            v_k_1295_ = leanh::lean_ctor_get(v_x_1283_, 1);
            leanh::lean_inc(v_k_1295_);
            leanh::lean_dec_ref_known(v_x_1283_, 2);
            v___x_1296_ = leanh::lean_apply_3(
                v_h__3_1287_,
                v_n_1294_,
                v_k_1295_,
                leanh::lean_box(0),
            );
            return v___x_1296_;
        } else {
            let mut v_n_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1287_);
            v_n_1297_ = leanh::lean_ctor_get(v_x_1283_, 0);
            leanh::lean_inc(v_n_1297_);
            v_k_1298_ = leanh::lean_ctor_get(v_x_1283_, 1);
            leanh::lean_inc(v_k_1298_);
            leanh::lean_dec_ref_known(v_x_1283_, 2);
            v_n_1299_ = leanh::lean_ctor_get(v_x_1284_, 0);
            leanh::lean_inc(v_n_1299_);
            v_k_1300_ = leanh::lean_ctor_get(v_x_1284_, 1);
            leanh::lean_inc(v_k_1300_);
            leanh::lean_dec_ref_known(v_x_1284_, 2);
            v___x_1301_ = leanh::lean_apply_6(
                v_h__4_1288_,
                v_n_1297_,
                v_k_1298_,
                leanh::lean_box(0),
                v_n_1299_,
                v_k_1300_,
                leanh::lean_box(0),
            );
            return v___x_1301_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(
    mut v_motive_1302_: *mut leanh::LeanObject,
    mut v_x_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: *mut leanh::LeanObject,
    mut v_h__1_1305_: *mut leanh::LeanObject,
    mut v_h__2_1306_: *mut leanh::LeanObject,
    mut v_h__3_1307_: *mut leanh::LeanObject,
    mut v_h__4_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1303_) == 0 {
        leanh::lean_dec(v_h__4_1308_);
        leanh::lean_dec(v_h__3_1307_);
        if leanh::lean_obj_tag(v_x_1304_) == 0 {
            let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1306_);
            v___x_1309_ = leanh::lean_box(0);
            v___x_1310_ = leanh::lean_apply_1(v_h__1_1305_, v___x_1309_);
            return v___x_1310_;
        } else {
            let mut v_n_1311_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1305_);
            v_n_1311_ = leanh::lean_ctor_get(v_x_1304_, 0);
            leanh::lean_inc(v_n_1311_);
            v_k_1312_ = leanh::lean_ctor_get(v_x_1304_, 1);
            leanh::lean_inc(v_k_1312_);
            leanh::lean_dec_ref_known(v_x_1304_, 2);
            v___x_1313_ = leanh::lean_apply_3(
                v_h__2_1306_,
                v_n_1311_,
                v_k_1312_,
                leanh::lean_box(0),
            );
            return v___x_1313_;
        }
    } else {
        leanh::lean_dec(v_h__2_1306_);
        leanh::lean_dec(v_h__1_1305_);
        if leanh::lean_obj_tag(v_x_1304_) == 0 {
            let mut v_n_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1308_);
            v_n_1314_ = leanh::lean_ctor_get(v_x_1303_, 0);
            leanh::lean_inc(v_n_1314_);
            v_k_1315_ = leanh::lean_ctor_get(v_x_1303_, 1);
            leanh::lean_inc(v_k_1315_);
            leanh::lean_dec_ref_known(v_x_1303_, 2);
            v___x_1316_ = leanh::lean_apply_3(
                v_h__3_1307_,
                v_n_1314_,
                v_k_1315_,
                leanh::lean_box(0),
            );
            return v___x_1316_;
        } else {
            let mut v_n_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1307_);
            v_n_1317_ = leanh::lean_ctor_get(v_x_1303_, 0);
            leanh::lean_inc(v_n_1317_);
            v_k_1318_ = leanh::lean_ctor_get(v_x_1303_, 1);
            leanh::lean_inc(v_k_1318_);
            leanh::lean_dec_ref_known(v_x_1303_, 2);
            v_n_1319_ = leanh::lean_ctor_get(v_x_1304_, 0);
            leanh::lean_inc(v_n_1319_);
            v_k_1320_ = leanh::lean_ctor_get(v_x_1304_, 1);
            leanh::lean_inc(v_k_1320_);
            leanh::lean_dec_ref_known(v_x_1304_, 2);
            v___x_1321_ = leanh::lean_apply_6(
                v_h__4_1308_,
                v_n_1317_,
                v_k_1318_,
                leanh::lean_box(0),
                v_n_1319_,
                v_k_1320_,
                leanh::lean_box(0),
            );
            return v___x_1321_;
        }
    }
}
pub unsafe fn _init_l_Dyadic_instLT() -> *mut leanh::LeanObject {
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = leanh::lean_box(0);
    return v___x_1322_;
}
pub unsafe fn _init_l_Dyadic_instLE() -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = leanh::lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_Dyadic_instDecidableLT(
    mut v_x_1324_: *mut leanh::LeanObject,
    mut v_x_1325_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1326_: u8 = 0;
    v___x_1326_ = l_Dyadic_blt(v_x_1324_, v_x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Dyadic_instDecidableLT___boxed(
    mut v_x_1327_: *mut leanh::LeanObject,
    mut v_x_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1329_: u8 = 0;
    let mut v_r_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1329_ = l_Dyadic_instDecidableLT(v_x_1327_, v_x_1328_);
    leanh::lean_dec(v_x_1328_);
    leanh::lean_dec(v_x_1327_);
    v_r_1330_ = leanh::lean_box((v_res_1329_) as usize);
    return v_r_1330_;
}
pub unsafe fn l_Dyadic_instDecidableLE(
    mut v_x_1331_: *mut leanh::LeanObject,
    mut v_x_1332_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    v___x_1333_ = l_Dyadic_ble(v_x_1331_, v_x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Dyadic_instDecidableLE___boxed(
    mut v_x_1334_: *mut leanh::LeanObject,
    mut v_x_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Dyadic_instDecidableLE(v_x_1334_, v_x_1335_);
    leanh::lean_dec(v_x_1335_);
    leanh::lean_dec(v_x_1334_);
    v_r_1337_ = leanh::lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Dyadic_roundUp(
    mut v_x_1338_: *mut leanh::LeanObject,
    mut v_prec_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1338_) == 0 {
        return v_x_1338_;
    } else {
        let mut v_n_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1344_: u8 = 0;
        v_n_1340_ = leanh::lean_ctor_get(v_x_1338_, 0);
        v_k_1341_ = leanh::lean_ctor_get(v_x_1338_, 1);
        v___x_1342_ = lean_int_sub(v_k_1341_, v_prec_1339_);
        v_intZero_1343_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1344_ = lean_int_dec_lt(v___x_1342_, v_intZero_1343_);
        if v_isNeg_1344_ == 0 {
            let mut v_a_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_a_1345_ = lean_nat_abs(v___x_1342_);
            leanh::lean_dec(v___x_1342_);
            v___x_1346_ = lean_int_neg(v_n_1340_);
            v___x_1347_ = l_Int_shiftRight(v___x_1346_, v_a_1345_);
            leanh::lean_dec(v_a_1345_);
            leanh::lean_dec(v___x_1346_);
            v___x_1348_ = lean_int_neg(v___x_1347_);
            leanh::lean_dec(v___x_1347_);
            v___x_1349_ = l_Dyadic_ofIntWithPrec(v___x_1348_, v_prec_1339_);
            return v___x_1349_;
        } else {
            leanh::lean_dec(v___x_1342_);
            leanh::lean_inc_ref(v_x_1338_);
            return v_x_1338_;
        }
    }
}
pub unsafe fn l_Dyadic_roundUp___boxed(
    mut v_x_1350_: *mut leanh::LeanObject,
    mut v_prec_1351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1352_ = l_Dyadic_roundUp(v_x_1350_, v_prec_1351_);
    leanh::lean_dec(v_prec_1351_);
    leanh::lean_dec(v_x_1350_);
    return v_res_1352_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Dyadic_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Dyadic_instLT = _init_l_Dyadic_instLT();
    leanh::lean_mark_persistent(l_Dyadic_instLT);
    l_Dyadic_instLE = _init_l_Dyadic_instLE();
    leanh::lean_mark_persistent(l_Dyadic_instLE);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Dyadic_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Dyadic_Basic(builtin);
}
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
static mut l_Int_trailingZeros_aux___redArg___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_trailingZeros_aux___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Int_trailingZeros_aux___redArg___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Int_trailingZeros_aux___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Dyadic_instIntCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_ofInt as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instIntCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instIntCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instNatCast___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instNatCast___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instNatCast___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instNatCast: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instAdd___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_add as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instAdd___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instAdd: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instMul___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_mul___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instMul___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instMul: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_Dyadic_pow___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Dyadic_instPowNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_pow as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instPowNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instPowNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instNeg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_neg as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instNeg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instNeg: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instSub___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_sub as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instSub___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instSub: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instHShiftLeftInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_shiftLeft___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftLeftInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instHShiftLeftInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instHShiftRightInt___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightInt___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instHShiftRightInt: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instHShiftLeftNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instHShiftLeftNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftLeftNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instHShiftLeftNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Dyadic_instHShiftRightNat___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instHShiftRightNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightNat___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Dyadic_instHShiftRightNat: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Dyadic_toRat___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Dyadic_toRat___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLT: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLE: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__0() -> *mut crate::leanh::LeanObject
{
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_677_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__1() -> *mut crate::leanh::LeanObject
{
    let mut v_zero_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_679_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_680_ = lean_nat_to_int(v_zero_679_);
    return v___x_680_;
}
pub unsafe fn l_Int_trailingZeros_aux___redArg(
    mut v_k_681_: *mut crate::leanh::LeanObject,
    mut v_i_682_: *mut crate::leanh::LeanObject,
    mut v_acc_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_685_: u8 = 0;
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v_one_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_684_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_685_ = lean_nat_dec_eq(v_k_681_, v_zero_684_);
                v___x_686_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__0,
                );
                v___x_687_ = lean_int_emod(v_i_682_, v___x_686_);
                v___x_688_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v___x_689_ = lean_int_dec_eq(v___x_687_, v___x_688_);
                crate::leanh::lean_dec(v___x_687_);
                if v___x_689_ == 0 {
                    crate::leanh::lean_dec(v_i_682_);
                    crate::leanh::lean_dec(v_k_681_);
                    return v_acc_683_;
                } else {
                    v_one_690_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_691_ = lean_nat_sub(v_k_681_, v_one_690_);
                    crate::leanh::lean_dec(v_k_681_);
                    v___x_692_ = lean_int_ediv(v_i_682_, v___x_686_);
                    crate::leanh::lean_dec(v_i_682_);
                    v___x_693_ = lean_nat_add(v_acc_683_, v_one_690_);
                    crate::leanh::lean_dec(v_acc_683_);
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
    mut v_k_695_: *mut crate::leanh::LeanObject,
    mut v_i_696_: *mut crate::leanh::LeanObject,
    mut v_hi_697_: *mut crate::leanh::LeanObject,
    mut v_hk_698_: *mut crate::leanh::LeanObject,
    mut v_acc_699_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Int_trailingZeros_aux___redArg(v_k_695_, v_i_696_, v_acc_699_);
    return v___x_700_;
}
pub unsafe fn l_Int_trailingZeros(
    mut v_i_701_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    v___x_702_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_703_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_704_ = lean_int_dec_eq(v_i_701_, v___x_703_);
    if v___x_704_ == 0 {
        let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_705_ = lean_nat_abs(v_i_701_);
        v___x_706_ = l_Int_trailingZeros_aux___redArg(v___x_705_, v_i_701_, v___x_702_);
        return v___x_706_;
    } else {
        crate::leanh::lean_dec(v_i_701_);
        return v___x_702_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
    mut v_k_707_: *mut crate::leanh::LeanObject,
    mut v_h__1_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_710_: u8 = 0;
    let mut v_one_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_709_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_710_ = lean_nat_dec_eq(v_k_707_, v_zero_709_);
    v_one_711_ = crate::leanh::lean_unsigned_to_nat(1);
    v_n_712_ = lean_nat_sub(v_k_707_, v_one_711_);
    v___x_713_ = crate::leanh::lean_apply_3(
        v_h__1_708_,
        v_n_712_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_713_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg___boxed(
    mut v_k_714_: *mut crate::leanh::LeanObject,
    mut v_h__1_715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
            v_k_714_,
            v_h__1_715_,
        );
    crate::leanh::lean_dec(v_k_714_);
    return v_res_716_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
    mut v_i_717_: *mut crate::leanh::LeanObject,
    mut v_motive_718_: *mut crate::leanh::LeanObject,
    mut v_k_719_: *mut crate::leanh::LeanObject,
    mut v_x_720_: *mut crate::leanh::LeanObject,
    mut v_hk_721_: *mut crate::leanh::LeanObject,
    mut v_h__1_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_724_: u8 = 0;
    let mut v_one_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_zero_723_ = crate::leanh::lean_unsigned_to_nat(0);
    v_isZero_724_ = lean_nat_dec_eq(v_k_719_, v_zero_723_);
    v_one_725_ = crate::leanh::lean_unsigned_to_nat(1);
    v_n_726_ = lean_nat_sub(v_k_719_, v_one_725_);
    v___x_727_ = crate::leanh::lean_apply_3(
        v_h__1_722_,
        v_n_726_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_727_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(
    mut v_i_728_: *mut crate::leanh::LeanObject,
    mut v_motive_729_: *mut crate::leanh::LeanObject,
    mut v_k_730_: *mut crate::leanh::LeanObject,
    mut v_x_731_: *mut crate::leanh::LeanObject,
    mut v_hk_732_: *mut crate::leanh::LeanObject,
    mut v_h__1_733_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
        v_i_728_,
        v_motive_729_,
        v_k_730_,
        v_x_731_,
        v_hk_732_,
        v_h__1_733_,
    );
    crate::leanh::lean_dec(v_k_730_);
    crate::leanh::lean_dec(v_i_728_);
    return v_res_734_;
}
pub unsafe fn l_Dyadic_ctorIdx(
    mut v_x_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_735_) == 0 {
        let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_736_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_736_;
    } else {
        let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_737_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_737_;
    }
}
pub unsafe fn l_Dyadic_ctorIdx___boxed(
    mut v_x_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Dyadic_ctorIdx(v_x_738_);
    crate::leanh::lean_dec(v_x_738_);
    return v_res_739_;
}
pub unsafe fn l_Dyadic_ctorElim___redArg(
    mut v_t_740_: *mut crate::leanh::LeanObject,
    mut v_k_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_t_740_) == 0 {
        return v_k_741_;
    } else {
        let mut v_n_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_n_742_ = crate::leanh::lean_ctor_get(v_t_740_, 0);
        crate::leanh::lean_inc(v_n_742_);
        v_k_743_ = crate::leanh::lean_ctor_get(v_t_740_, 1);
        crate::leanh::lean_inc(v_k_743_);
        crate::leanh::lean_dec_ref_known(v_t_740_, 2);
        v___x_744_ =
            crate::leanh::lean_apply_3(v_k_741_, v_n_742_, v_k_743_, crate::leanh::lean_box(0));
        return v___x_744_;
    }
}
pub unsafe fn l_Dyadic_ctorElim(
    mut v_motive_745_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_746_: *mut crate::leanh::LeanObject,
    mut v_t_747_: *mut crate::leanh::LeanObject,
    mut v_h_748_: *mut crate::leanh::LeanObject,
    mut v_k_749_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Dyadic_ctorElim___redArg(v_t_747_, v_k_749_);
    return v___x_750_;
}
pub unsafe fn l_Dyadic_ctorElim___boxed(
    mut v_motive_751_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_752_: *mut crate::leanh::LeanObject,
    mut v_t_753_: *mut crate::leanh::LeanObject,
    mut v_h_754_: *mut crate::leanh::LeanObject,
    mut v_k_755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Dyadic_ctorElim(v_motive_751_, v_ctorIdx_752_, v_t_753_, v_h_754_, v_k_755_);
    crate::leanh::lean_dec(v_ctorIdx_752_);
    return v_res_756_;
}
pub unsafe fn l_Dyadic_zero_elim___redArg(
    mut v_t_757_: *mut crate::leanh::LeanObject,
    mut v_zero_758_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Dyadic_ctorElim___redArg(v_t_757_, v_zero_758_);
    return v___x_759_;
}
pub unsafe fn l_Dyadic_zero_elim(
    mut v_motive_760_: *mut crate::leanh::LeanObject,
    mut v_t_761_: *mut crate::leanh::LeanObject,
    mut v_h_762_: *mut crate::leanh::LeanObject,
    mut v_zero_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Dyadic_ctorElim___redArg(v_t_761_, v_zero_763_);
    return v___x_764_;
}
pub unsafe fn l_Dyadic_ofOdd_elim___redArg(
    mut v_t_765_: *mut crate::leanh::LeanObject,
    mut v_ofOdd_766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_767_ = l_Dyadic_ctorElim___redArg(v_t_765_, v_ofOdd_766_);
    return v___x_767_;
}
pub unsafe fn l_Dyadic_ofOdd_elim(
    mut v_motive_768_: *mut crate::leanh::LeanObject,
    mut v_t_769_: *mut crate::leanh::LeanObject,
    mut v_h_770_: *mut crate::leanh::LeanObject,
    mut v_ofOdd_771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Dyadic_ctorElim___redArg(v_t_769_, v_ofOdd_771_);
    return v___x_772_;
}
pub unsafe fn l_instDecidableEqDyadic_decEq(
    mut v_x_773_: *mut crate::leanh::LeanObject,
    mut v_x_774_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_773_) == 0 {
        if crate::leanh::lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_775_: u8 = 0;
            v___x_775_ = 1;
            return v___x_775_;
        } else {
            let mut v___x_776_: u8 = 0;
            v___x_776_ = 0;
            return v___x_776_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_777_: u8 = 0;
            v___x_777_ = 0;
            return v___x_777_;
        } else {
            let mut v_n_778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_782_: u8 = 0;
            v_n_778_ = crate::leanh::lean_ctor_get(v_x_773_, 0);
            v_k_779_ = crate::leanh::lean_ctor_get(v_x_773_, 1);
            v_n_780_ = crate::leanh::lean_ctor_get(v_x_774_, 0);
            v_k_781_ = crate::leanh::lean_ctor_get(v_x_774_, 1);
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
    mut v_x_784_: *mut crate::leanh::LeanObject,
    mut v_x_785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_786_ = l_instDecidableEqDyadic_decEq(v_x_784_, v_x_785_);
    crate::leanh::lean_dec(v_x_785_);
    crate::leanh::lean_dec(v_x_784_);
    v_r_787_ = crate::leanh::lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_instDecidableEqDyadic(
    mut v_x_788_: *mut crate::leanh::LeanObject,
    mut v_x_789_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_790_: u8 = 0;
    v___x_790_ = l_instDecidableEqDyadic_decEq(v_x_788_, v_x_789_);
    return v___x_790_;
}
pub unsafe fn l_instDecidableEqDyadic___boxed(
    mut v_x_791_: *mut crate::leanh::LeanObject,
    mut v_x_792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_793_ = l_instDecidableEqDyadic(v_x_791_, v_x_792_);
    crate::leanh::lean_dec(v_x_792_);
    crate::leanh::lean_dec(v_x_791_);
    v_r_794_ = crate::leanh::lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(
    mut v_a_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_796_ = lean_nat_to_int(v_a_795_);
    return v___x_796_;
}
pub unsafe fn l_Dyadic_ofIntWithPrec(
    mut v_i_797_: *mut crate::leanh::LeanObject,
    mut v_prec_798_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u8 = 0;
    v___x_799_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_800_ = lean_int_dec_eq(v_i_797_, v___x_799_);
    if v___x_800_ == 0 {
        let mut v___x_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_inc(v_i_797_);
        v___x_801_ = l_Int_trailingZeros(v_i_797_);
        v___x_802_ = l_Int_shiftRight(v_i_797_, v___x_801_);
        crate::leanh::lean_dec(v_i_797_);
        v___x_803_ = lean_nat_to_int(v___x_801_);
        v___x_804_ = lean_int_sub(v_prec_798_, v___x_803_);
        crate::leanh::lean_dec(v___x_803_);
        v___x_805_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_805_, 0, v___x_802_);
        crate::leanh::lean_ctor_set(v___x_805_, 1, v___x_804_);
        return v___x_805_;
    } else {
        let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_797_);
        v___x_806_ = crate::leanh::lean_box(0);
        return v___x_806_;
    }
}
pub unsafe fn l_Dyadic_ofIntWithPrec___boxed(
    mut v_i_807_: *mut crate::leanh::LeanObject,
    mut v_prec_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Dyadic_ofIntWithPrec(v_i_807_, v_prec_808_);
    crate::leanh::lean_dec(v_prec_808_);
    return v_res_809_;
}
pub unsafe fn l_Dyadic_ofInt(
    mut v_i_810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_811_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_812_ = l_Dyadic_ofIntWithPrec(v_i_810_, v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Dyadic_instOfNat(
    mut v_n_813_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_814_ = lean_nat_to_int(v_n_813_);
    v___x_815_ = l_Dyadic_ofInt(v___x_814_);
    return v___x_815_;
}
pub unsafe fn l_Dyadic_instNatCast___lam__0(
    mut v_x_818_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = lean_nat_to_int(v_x_818_);
    v___x_820_ = l_Dyadic_ofInt(v___x_819_);
    return v___x_820_;
}
pub unsafe fn l_Dyadic_add(
    mut v_x_823_: *mut crate::leanh::LeanObject,
    mut v_y_824_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_829_: u8 = 0;
    let mut v___x_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v_n_834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_840_: u8 = 0;
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natZero_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_844_: u8 = 0;
    let mut v_a_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_846_: u8 = 0;
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_823_) == 0 {
                    return v_y_824_;
                } else {
                    if crate::leanh::lean_obj_tag(v_y_824_) == 0 {
                        v_n_825_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        v_k_826_ = crate::leanh::lean_ctor_get(v_x_823_, 1);
                        v_isSharedCheck_833_ = (!crate::leanh::lean_is_exclusive(v_x_823_)) as u8;
                        if v_isSharedCheck_833_ == 0 {
                            v___x_828_ = v_x_823_;
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_826_);
                            crate::leanh::lean_inc(v_n_825_);
                            crate::leanh::lean_dec(v_x_823_);
                            v___x_828_ = crate::leanh::lean_box(0);
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_n_834_ = crate::leanh::lean_ctor_get(v_x_823_, 0);
                        crate::leanh::lean_inc(v_n_834_);
                        v_k_835_ = crate::leanh::lean_ctor_get(v_x_823_, 1);
                        crate::leanh::lean_inc(v_k_835_);
                        crate::leanh::lean_dec_ref_known(v_x_823_, 2);
                        v_n_836_ = crate::leanh::lean_ctor_get(v_y_824_, 0);
                        v_k_837_ = crate::leanh::lean_ctor_get(v_y_824_, 1);
                        v_isSharedCheck_863_ = (!crate::leanh::lean_is_exclusive(v_y_824_)) as u8;
                        if v_isSharedCheck_863_ == 0 {
                            v___x_839_ = v_y_824_;
                            v_isShared_840_ = v_isSharedCheck_863_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_837_);
                            crate::leanh::lean_inc(v_n_836_);
                            crate::leanh::lean_dec(v_y_824_);
                            v___x_839_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_832_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 0, v_n_825_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_826_);
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
                v_natZero_842_ = crate::leanh::lean_unsigned_to_nat(0);
                v_intZero_843_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_844_ = lean_int_dec_lt(v___x_841_, v_intZero_843_);
                if v_isNeg_844_ == 0 {
                    crate::leanh::lean_dec(v_k_837_);
                    v_a_845_ = lean_nat_abs(v___x_841_);
                    crate::leanh::lean_dec(v___x_841_);
                    v_isZero_846_ = lean_nat_dec_eq(v_a_845_, v_natZero_842_);
                    if v_isZero_846_ == 1 {
                        crate::leanh::lean_dec(v_a_845_);
                        crate::leanh::lean_del_object(v___x_839_);
                        v___x_847_ = lean_int_add(v_n_834_, v_n_836_);
                        crate::leanh::lean_dec(v_n_836_);
                        crate::leanh::lean_dec(v_n_834_);
                        v___x_848_ = l_Dyadic_ofIntWithPrec(v___x_847_, v_k_835_);
                        crate::leanh::lean_dec(v_k_835_);
                        return v___x_848_;
                    } else {
                        v___x_849_ = l_Int_shiftLeft(v_n_836_, v_a_845_);
                        crate::leanh::lean_dec(v_a_845_);
                        crate::leanh::lean_dec(v_n_836_);
                        v___x_850_ = lean_int_add(v_n_834_, v___x_849_);
                        crate::leanh::lean_dec(v___x_849_);
                        crate::leanh::lean_dec(v_n_834_);
                        if v_isShared_840_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_839_, 1, v_k_835_);
                            crate::leanh::lean_ctor_set(v___x_839_, 0, v___x_850_);
                            v___x_852_ = v___x_839_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_853_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_853_, 1, v_k_835_);
                            v___x_852_ = v_reuseFailAlloc_853_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_k_835_);
                    v_abs_854_ = lean_nat_abs(v___x_841_);
                    crate::leanh::lean_dec(v___x_841_);
                    v_one_855_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_856_ = lean_nat_sub(v_abs_854_, v_one_855_);
                    crate::leanh::lean_dec(v_abs_854_);
                    v___x_857_ = lean_nat_add(v_a_856_, v_one_855_);
                    crate::leanh::lean_dec(v_a_856_);
                    v___x_858_ = l_Int_shiftLeft(v_n_834_, v___x_857_);
                    crate::leanh::lean_dec(v___x_857_);
                    crate::leanh::lean_dec(v_n_834_);
                    v___x_859_ = lean_int_add(v___x_858_, v_n_836_);
                    crate::leanh::lean_dec(v_n_836_);
                    crate::leanh::lean_dec(v___x_858_);
                    if v_isShared_840_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_839_, 0, v___x_859_);
                        v___x_861_ = v___x_839_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_837_);
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
    mut v_x_866_: *mut crate::leanh::LeanObject,
    mut v_y_867_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_866_) == 0 {
                    crate::leanh::lean_dec(v_y_867_);
                    return v_x_866_;
                } else {
                    if crate::leanh::lean_obj_tag(v_y_867_) == 0 {
                        return v_y_867_;
                    } else {
                        v_n_868_ = crate::leanh::lean_ctor_get(v_x_866_, 0);
                        v_k_869_ = crate::leanh::lean_ctor_get(v_x_866_, 1);
                        v_n_870_ = crate::leanh::lean_ctor_get(v_y_867_, 0);
                        v_k_871_ = crate::leanh::lean_ctor_get(v_y_867_, 1);
                        v_isSharedCheck_880_ = (!crate::leanh::lean_is_exclusive(v_y_867_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_873_ = v_y_867_;
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_871_);
                            crate::leanh::lean_inc(v_n_870_);
                            crate::leanh::lean_dec(v_y_867_);
                            v___x_873_ = crate::leanh::lean_box(0);
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_875_ = lean_int_mul(v_n_868_, v_n_870_);
                crate::leanh::lean_dec(v_n_870_);
                v___x_876_ = lean_int_add(v_k_869_, v_k_871_);
                crate::leanh::lean_dec(v_k_871_);
                if v_isShared_874_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_873_, 1, v___x_876_);
                    crate::leanh::lean_ctor_set(v___x_873_, 0, v___x_875_);
                    v___x_878_ = v___x_873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
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
    mut v_x_881_: *mut crate::leanh::LeanObject,
    mut v_y_882_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Dyadic_mul(v_x_881_, v_y_882_);
    crate::leanh::lean_dec(v_x_881_);
    return v_res_883_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_886_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_887_ = l_Dyadic_ofInt(v___x_886_);
    return v___x_887_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_888_ = crate::leanh::lean_unsigned_to_nat(1);
    v___x_889_ = lean_nat_to_int(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_890_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1),
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1_once),
        _init_l_Dyadic_pow___closed__1,
    );
    v___x_891_ = l_Dyadic_ofInt(v___x_890_);
    return v___x_891_;
}
pub unsafe fn l_Dyadic_pow(
    mut v_x_892_: *mut crate::leanh::LeanObject,
    mut v_i_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_902_: u8 = 0;
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_892_) == 0 {
                    v___x_894_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_895_ = lean_nat_dec_eq(v_i_893_, v___x_894_);
                    crate::leanh::lean_dec(v_i_893_);
                    if v___x_895_ == 0 {
                        v___x_896_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0_once),
                            _init_l_Dyadic_pow___closed__0,
                        );
                        return v___x_896_;
                    } else {
                        v___x_897_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2_once),
                            _init_l_Dyadic_pow___closed__2,
                        );
                        return v___x_897_;
                    }
                } else {
                    v_n_898_ = crate::leanh::lean_ctor_get(v_x_892_, 0);
                    v_k_899_ = crate::leanh::lean_ctor_get(v_x_892_, 1);
                    v_isSharedCheck_909_ = (!crate::leanh::lean_is_exclusive(v_x_892_)) as u8;
                    if v_isSharedCheck_909_ == 0 {
                        v___x_901_ = v_x_892_;
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_899_);
                        crate::leanh::lean_inc(v_n_898_);
                        crate::leanh::lean_dec(v_x_892_);
                        v___x_901_ = crate::leanh::lean_box(0);
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_903_ = l_Int_pow(v_n_898_, v_i_893_);
                crate::leanh::lean_dec(v_n_898_);
                v___x_904_ = lean_nat_to_int(v_i_893_);
                v___x_905_ = lean_int_mul(v_k_899_, v___x_904_);
                crate::leanh::lean_dec(v___x_904_);
                crate::leanh::lean_dec(v_k_899_);
                if v_isShared_902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_901_, 1, v___x_905_);
                    crate::leanh::lean_ctor_set(v___x_901_, 0, v___x_903_);
                    v___x_907_ = v___x_901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
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
    mut v_x_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_917_: u8 = 0;
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_912_) == 0 {
                    return v_x_912_;
                } else {
                    v_n_913_ = crate::leanh::lean_ctor_get(v_x_912_, 0);
                    v_k_914_ = crate::leanh::lean_ctor_get(v_x_912_, 1);
                    v_isSharedCheck_922_ = (!crate::leanh::lean_is_exclusive(v_x_912_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_916_ = v_x_912_;
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_914_);
                        crate::leanh::lean_inc(v_n_913_);
                        crate::leanh::lean_dec(v_x_912_);
                        v___x_916_ = crate::leanh::lean_box(0);
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_918_ = lean_int_neg(v_n_913_);
                crate::leanh::lean_dec(v_n_913_);
                if v_isShared_917_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_916_, 0, v___x_918_);
                    v___x_920_ = v___x_916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_914_);
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
    mut v_x_925_: *mut crate::leanh::LeanObject,
    mut v_y_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Dyadic_neg(v_y_926_);
    v___x_928_ = l_Dyadic_add(v_x_925_, v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_Dyadic_shiftLeft(
    mut v_x_931_: *mut crate::leanh::LeanObject,
    mut v_i_932_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_931_) == 0 {
                    return v_x_931_;
                } else {
                    v_n_933_ = crate::leanh::lean_ctor_get(v_x_931_, 0);
                    v_k_934_ = crate::leanh::lean_ctor_get(v_x_931_, 1);
                    v_isSharedCheck_942_ = (!crate::leanh::lean_is_exclusive(v_x_931_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v___x_936_ = v_x_931_;
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_934_);
                        crate::leanh::lean_inc(v_n_933_);
                        crate::leanh::lean_dec(v_x_931_);
                        v___x_936_ = crate::leanh::lean_box(0);
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_938_ = lean_int_sub(v_k_934_, v_i_932_);
                crate::leanh::lean_dec(v_k_934_);
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_936_, 1, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 0, v_n_933_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
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
    mut v_x_943_: *mut crate::leanh::LeanObject,
    mut v_i_944_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_945_ = l_Dyadic_shiftLeft(v_x_943_, v_i_944_);
    crate::leanh::lean_dec(v_i_944_);
    return v_res_945_;
}
pub unsafe fn l_Dyadic_shiftRight(
    mut v_x_946_: *mut crate::leanh::LeanObject,
    mut v_i_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_n_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_946_) == 0 {
                    return v_x_946_;
                } else {
                    v_n_948_ = crate::leanh::lean_ctor_get(v_x_946_, 0);
                    v_k_949_ = crate::leanh::lean_ctor_get(v_x_946_, 1);
                    v_isSharedCheck_957_ = (!crate::leanh::lean_is_exclusive(v_x_946_)) as u8;
                    if v_isSharedCheck_957_ == 0 {
                        v___x_951_ = v_x_946_;
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_949_);
                        crate::leanh::lean_inc(v_n_948_);
                        crate::leanh::lean_dec(v_x_946_);
                        v___x_951_ = crate::leanh::lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_953_ = lean_int_add(v_k_949_, v_i_947_);
                crate::leanh::lean_dec(v_k_949_);
                if v_isShared_952_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_953_);
                    v___x_955_ = v___x_951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_n_948_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
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
    mut v_x_958_: *mut crate::leanh::LeanObject,
    mut v_i_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Dyadic_shiftRight(v_x_958_, v_i_959_);
    crate::leanh::lean_dec(v_i_959_);
    return v_res_960_;
}
pub unsafe fn l_Dyadic_instHShiftLeftNat___lam__0(
    mut v_x_965_: *mut crate::leanh::LeanObject,
    mut v_y_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_967_ = lean_nat_to_int(v_y_966_);
    v___x_968_ = l_Dyadic_shiftLeft(v_x_965_, v___x_967_);
    crate::leanh::lean_dec(v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Dyadic_instHShiftRightNat___lam__0(
    mut v_x_971_: *mut crate::leanh::LeanObject,
    mut v_y_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_nat_to_int(v_y_972_);
    v___x_974_ = l_Dyadic_shiftRight(v_x_971_, v___x_973_);
    crate::leanh::lean_dec(v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Int_cast___at___00Dyadic_toRat_spec__1(
    mut v_a_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_978_ = l_Rat_ofInt(v_a_977_);
    return v___x_978_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_toRat_spec__0(
    mut v_a_979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_980_ = lean_nat_to_int(v_a_979_);
    v___x_981_ = l_Rat_ofInt(v___x_980_);
    return v___x_981_;
}
pub unsafe fn _init_l_Dyadic_toRat___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_983_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_982_);
    return v___x_983_;
}
pub unsafe fn l_Dyadic_toRat(
    mut v_x_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v_intZero_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_992_: u8 = 0;
    let mut v_a_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_abs_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_984_) == 0 {
                    v___x_985_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0),
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0_once),
                        _init_l_Dyadic_toRat___closed__0,
                    );
                    return v___x_985_;
                } else {
                    v_n_986_ = crate::leanh::lean_ctor_get(v_x_984_, 0);
                    v_k_987_ = crate::leanh::lean_ctor_get(v_x_984_, 1);
                    v_isSharedCheck_1008_ = (!crate::leanh::lean_is_exclusive(v_x_984_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_989_ = v_x_984_;
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_k_987_);
                        crate::leanh::lean_inc(v_n_986_);
                        crate::leanh::lean_dec(v_x_984_);
                        v___x_989_ = crate::leanh::lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_intZero_991_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_992_ = lean_int_dec_lt(v_k_987_, v_intZero_991_);
                if v_isNeg_992_ == 0 {
                    v_a_993_ = lean_nat_abs(v_k_987_);
                    crate::leanh::lean_dec(v_k_987_);
                    v___x_994_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_995_ = lean_nat_pow(v___x_994_, v_a_993_);
                    crate::leanh::lean_dec(v_a_993_);
                    if v_isShared_990_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_989_, 0);
                        crate::leanh::lean_ctor_set(v___x_989_, 1, v___x_995_);
                        v___x_997_ = v___x_989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_998_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_998_, 0, v_n_986_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
                        v___x_997_ = v_reuseFailAlloc_998_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_989_);
                    v_abs_999_ = lean_nat_abs(v_k_987_);
                    crate::leanh::lean_dec(v_k_987_);
                    v_one_1000_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_a_1001_ = lean_nat_sub(v_abs_999_, v_one_1000_);
                    crate::leanh::lean_dec(v_abs_999_);
                    v___x_1002_ = crate::leanh::lean_unsigned_to_nat(2);
                    v___x_1003_ = lean_nat_add(v_a_1001_, v_one_1000_);
                    crate::leanh::lean_dec(v_a_1001_);
                    v___x_1004_ = lean_nat_pow(v___x_1002_, v___x_1003_);
                    crate::leanh::lean_dec(v___x_1003_);
                    v___x_1005_ = lean_nat_to_int(v___x_1004_);
                    v___x_1006_ = lean_int_mul(v_n_986_, v___x_1005_);
                    crate::leanh::lean_dec(v___x_1005_);
                    crate::leanh::lean_dec(v_n_986_);
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
    mut v_x_1009_: *mut crate::leanh::LeanObject,
    mut v_h__1_1010_: *mut crate::leanh::LeanObject,
    mut v_h__2_1011_: *mut crate::leanh::LeanObject,
    mut v_h__3_1012_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1009_) == 0 {
        let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1012_);
        crate::leanh::lean_dec(v_h__2_1011_);
        v___x_1013_ = crate::leanh::lean_box(0);
        v___x_1014_ = crate::leanh::lean_apply_1(v_h__1_1010_, v___x_1013_);
        return v___x_1014_;
    } else {
        let mut v_n_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1018_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1010_);
        v_n_1015_ = crate::leanh::lean_ctor_get(v_x_1009_, 0);
        crate::leanh::lean_inc(v_n_1015_);
        v_k_1016_ = crate::leanh::lean_ctor_get(v_x_1009_, 1);
        crate::leanh::lean_inc(v_k_1016_);
        crate::leanh::lean_dec_ref_known(v_x_1009_, 2);
        v_intZero_1017_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1018_ = lean_int_dec_lt(v_k_1016_, v_intZero_1017_);
        if v_isNeg_1018_ == 0 {
            let mut v_a_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1012_);
            v_a_1019_ = lean_nat_abs(v_k_1016_);
            crate::leanh::lean_dec(v_k_1016_);
            v___x_1020_ = crate::leanh::lean_apply_3(
                v_h__2_1011_,
                v_n_1015_,
                v_a_1019_,
                crate::leanh::lean_box(0),
            );
            return v___x_1020_;
        } else {
            let mut v_abs_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1011_);
            v_abs_1021_ = lean_nat_abs(v_k_1016_);
            crate::leanh::lean_dec(v_k_1016_);
            v_one_1022_ = crate::leanh::lean_unsigned_to_nat(1);
            v_a_1023_ = lean_nat_sub(v_abs_1021_, v_one_1022_);
            crate::leanh::lean_dec(v_abs_1021_);
            v___x_1024_ = crate::leanh::lean_apply_3(
                v_h__3_1012_,
                v_n_1015_,
                v_a_1023_,
                crate::leanh::lean_box(0),
            );
            return v___x_1024_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(
    mut v_motive_1025_: *mut crate::leanh::LeanObject,
    mut v_x_1026_: *mut crate::leanh::LeanObject,
    mut v_h__1_1027_: *mut crate::leanh::LeanObject,
    mut v_h__2_1028_: *mut crate::leanh::LeanObject,
    mut v_h__3_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1026_) == 0 {
        let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__3_1029_);
        crate::leanh::lean_dec(v_h__2_1028_);
        v___x_1030_ = crate::leanh::lean_box(0);
        v___x_1031_ = crate::leanh::lean_apply_1(v_h__1_1027_, v___x_1030_);
        return v___x_1031_;
    } else {
        let mut v_n_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1035_: u8 = 0;
        crate::leanh::lean_dec(v_h__1_1027_);
        v_n_1032_ = crate::leanh::lean_ctor_get(v_x_1026_, 0);
        crate::leanh::lean_inc(v_n_1032_);
        v_k_1033_ = crate::leanh::lean_ctor_get(v_x_1026_, 1);
        crate::leanh::lean_inc(v_k_1033_);
        crate::leanh::lean_dec_ref_known(v_x_1026_, 2);
        v_intZero_1034_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1035_ = lean_int_dec_lt(v_k_1033_, v_intZero_1034_);
        if v_isNeg_1035_ == 0 {
            let mut v_a_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1029_);
            v_a_1036_ = lean_nat_abs(v_k_1033_);
            crate::leanh::lean_dec(v_k_1033_);
            v___x_1037_ = crate::leanh::lean_apply_3(
                v_h__2_1028_,
                v_n_1032_,
                v_a_1036_,
                crate::leanh::lean_box(0),
            );
            return v___x_1037_;
        } else {
            let mut v_abs_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1028_);
            v_abs_1038_ = lean_nat_abs(v_k_1033_);
            crate::leanh::lean_dec(v_k_1033_);
            v_one_1039_ = crate::leanh::lean_unsigned_to_nat(1);
            v_a_1040_ = lean_nat_sub(v_abs_1038_, v_one_1039_);
            crate::leanh::lean_dec(v_abs_1038_);
            v___x_1041_ = crate::leanh::lean_apply_3(
                v_h__3_1029_,
                v_n_1032_,
                v_a_1040_,
                crate::leanh::lean_box(0),
            );
            return v___x_1041_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(
    mut v_x_1042_: *mut crate::leanh::LeanObject,
    mut v_y_1043_: *mut crate::leanh::LeanObject,
    mut v_h__1_1044_: *mut crate::leanh::LeanObject,
    mut v_h__2_1045_: *mut crate::leanh::LeanObject,
    mut v_h__3_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut v_n_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1042_) == 0 {
                    crate::leanh::lean_dec(v_h__3_1046_);
                    crate::leanh::lean_dec(v_h__2_1045_);
                    v___x_1047_ = crate::leanh::lean_apply_1(v_h__1_1044_, v_y_1043_);
                    return v___x_1047_;
                } else {
                    crate::leanh::lean_dec(v_h__1_1044_);
                    if crate::leanh::lean_obj_tag(v_y_1043_) == 0 {
                        crate::leanh::lean_dec(v_h__3_1046_);
                        v_n_1048_ = crate::leanh::lean_ctor_get(v_x_1042_, 0);
                        v_k_1049_ = crate::leanh::lean_ctor_get(v_x_1042_, 1);
                        v_isSharedCheck_1057_ = (!crate::leanh::lean_is_exclusive(v_x_1042_)) as u8;
                        if v_isSharedCheck_1057_ == 0 {
                            v___x_1051_ = v_x_1042_;
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_1049_);
                            crate::leanh::lean_inc(v_n_1048_);
                            crate::leanh::lean_dec(v_x_1042_);
                            v___x_1051_ = crate::leanh::lean_box(0);
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_h__2_1045_);
                        v_n_1058_ = crate::leanh::lean_ctor_get(v_x_1042_, 0);
                        crate::leanh::lean_inc(v_n_1058_);
                        v_k_1059_ = crate::leanh::lean_ctor_get(v_x_1042_, 1);
                        crate::leanh::lean_inc(v_k_1059_);
                        crate::leanh::lean_dec_ref_known(v_x_1042_, 2);
                        v_n_1060_ = crate::leanh::lean_ctor_get(v_y_1043_, 0);
                        crate::leanh::lean_inc(v_n_1060_);
                        v_k_1061_ = crate::leanh::lean_ctor_get(v_y_1043_, 1);
                        crate::leanh::lean_inc(v_k_1061_);
                        crate::leanh::lean_dec_ref_known(v_y_1043_, 2);
                        v___x_1062_ = crate::leanh::lean_apply_6(
                            v_h__3_1046_,
                            v_n_1058_,
                            v_k_1059_,
                            crate::leanh::lean_box(0),
                            v_n_1060_,
                            v_k_1061_,
                            crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_1056_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_n_1048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1055_ = crate::leanh::lean_apply_2(
                    v_h__2_1045_,
                    v___x_1054_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(
    mut v_motive_1063_: *mut crate::leanh::LeanObject,
    mut v_x_1064_: *mut crate::leanh::LeanObject,
    mut v_y_1065_: *mut crate::leanh::LeanObject,
    mut v_h__1_1066_: *mut crate::leanh::LeanObject,
    mut v_h__2_1067_: *mut crate::leanh::LeanObject,
    mut v_h__3_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_n_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1064_) == 0 {
                    crate::leanh::lean_dec(v_h__3_1068_);
                    crate::leanh::lean_dec(v_h__2_1067_);
                    v___x_1069_ = crate::leanh::lean_apply_1(v_h__1_1066_, v_y_1065_);
                    return v___x_1069_;
                } else {
                    crate::leanh::lean_dec(v_h__1_1066_);
                    if crate::leanh::lean_obj_tag(v_y_1065_) == 0 {
                        crate::leanh::lean_dec(v_h__3_1068_);
                        v_n_1070_ = crate::leanh::lean_ctor_get(v_x_1064_, 0);
                        v_k_1071_ = crate::leanh::lean_ctor_get(v_x_1064_, 1);
                        v_isSharedCheck_1079_ = (!crate::leanh::lean_is_exclusive(v_x_1064_)) as u8;
                        if v_isSharedCheck_1079_ == 0 {
                            v___x_1073_ = v_x_1064_;
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_k_1071_);
                            crate::leanh::lean_inc(v_n_1070_);
                            crate::leanh::lean_dec(v_x_1064_);
                            v___x_1073_ = crate::leanh::lean_box(0);
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_h__2_1067_);
                        v_n_1080_ = crate::leanh::lean_ctor_get(v_x_1064_, 0);
                        crate::leanh::lean_inc(v_n_1080_);
                        v_k_1081_ = crate::leanh::lean_ctor_get(v_x_1064_, 1);
                        crate::leanh::lean_inc(v_k_1081_);
                        crate::leanh::lean_dec_ref_known(v_x_1064_, 2);
                        v_n_1082_ = crate::leanh::lean_ctor_get(v_y_1065_, 0);
                        crate::leanh::lean_inc(v_n_1082_);
                        v_k_1083_ = crate::leanh::lean_ctor_get(v_y_1065_, 1);
                        crate::leanh::lean_inc(v_k_1083_);
                        crate::leanh::lean_dec_ref_known(v_y_1065_, 2);
                        v___x_1084_ = crate::leanh::lean_apply_6(
                            v_h__3_1068_,
                            v_n_1080_,
                            v_k_1081_,
                            crate::leanh::lean_box(0),
                            v_n_1082_,
                            v_k_1083_,
                            crate::leanh::lean_box(0),
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
                    v_reuseFailAlloc_1078_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_n_1070_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1077_ = crate::leanh::lean_apply_2(
                    v_h__2_1067_,
                    v___x_1076_,
                    crate::leanh::lean_box(0),
                );
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
    mut v_x_1085_: *mut crate::leanh::LeanObject,
    mut v_h__1_1086_: *mut crate::leanh::LeanObject,
    mut v_h__2_1087_: *mut crate::leanh::LeanObject,
    mut v_h__3_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1091_: u8 = 0;
    v_natZero_1089_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_1090_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1091_ = lean_int_dec_lt(v_x_1085_, v_intZero_1090_);
    if v_isNeg_1091_ == 0 {
        let mut v_a_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1093_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_1088_);
        v_a_1092_ = lean_nat_abs(v_x_1085_);
        v_isZero_1093_ = lean_nat_dec_eq(v_a_1092_, v_natZero_1089_);
        if v_isZero_1093_ == 1 {
            let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_1092_);
            crate::leanh::lean_dec(v_h__2_1087_);
            v___x_1094_ = crate::leanh::lean_box(0);
            v___x_1095_ = crate::leanh::lean_apply_1(v_h__1_1086_, v___x_1094_);
            return v___x_1095_;
        } else {
            let mut v_one_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1086_);
            v_one_1096_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1097_ = lean_nat_sub(v_a_1092_, v_one_1096_);
            crate::leanh::lean_dec(v_a_1092_);
            v___x_1098_ = crate::leanh::lean_apply_1(v_h__2_1087_, v_n_1097_);
            return v___x_1098_;
        }
    } else {
        let mut v_abs_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1087_);
        crate::leanh::lean_dec(v_h__1_1086_);
        v_abs_1099_ = lean_nat_abs(v_x_1085_);
        v_one_1100_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_1101_ = lean_nat_sub(v_abs_1099_, v_one_1100_);
        crate::leanh::lean_dec(v_abs_1099_);
        v___x_1102_ = crate::leanh::lean_apply_1(v_h__3_1088_, v_a_1101_);
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(
    mut v_x_1103_: *mut crate::leanh::LeanObject,
    mut v_h__1_1104_: *mut crate::leanh::LeanObject,
    mut v_h__2_1105_: *mut crate::leanh::LeanObject,
    mut v_h__3_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1107_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
        v_x_1103_,
        v_h__1_1104_,
        v_h__2_1105_,
        v_h__3_1106_,
    );
    crate::leanh::lean_dec(v_x_1103_);
    return v_res_1107_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
    mut v_motive_1108_: *mut crate::leanh::LeanObject,
    mut v_x_1109_: *mut crate::leanh::LeanObject,
    mut v_h__1_1110_: *mut crate::leanh::LeanObject,
    mut v_h__2_1111_: *mut crate::leanh::LeanObject,
    mut v_h__3_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_natZero_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1115_: u8 = 0;
    v_natZero_1113_ = crate::leanh::lean_unsigned_to_nat(0);
    v_intZero_1114_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1115_ = lean_int_dec_lt(v_x_1109_, v_intZero_1114_);
    if v_isNeg_1115_ == 0 {
        let mut v_a_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isZero_1117_: u8 = 0;
        crate::leanh::lean_dec(v_h__3_1112_);
        v_a_1116_ = lean_nat_abs(v_x_1109_);
        v_isZero_1117_ = lean_nat_dec_eq(v_a_1116_, v_natZero_1113_);
        if v_isZero_1117_ == 1 {
            let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_1116_);
            crate::leanh::lean_dec(v_h__2_1111_);
            v___x_1118_ = crate::leanh::lean_box(0);
            v___x_1119_ = crate::leanh::lean_apply_1(v_h__1_1110_, v___x_1118_);
            return v___x_1119_;
        } else {
            let mut v_one_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1110_);
            v_one_1120_ = crate::leanh::lean_unsigned_to_nat(1);
            v_n_1121_ = lean_nat_sub(v_a_1116_, v_one_1120_);
            crate::leanh::lean_dec(v_a_1116_);
            v___x_1122_ = crate::leanh::lean_apply_1(v_h__2_1111_, v_n_1121_);
            return v___x_1122_;
        }
    } else {
        let mut v_abs_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1111_);
        crate::leanh::lean_dec(v_h__1_1110_);
        v_abs_1123_ = lean_nat_abs(v_x_1109_);
        v_one_1124_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_1125_ = lean_nat_sub(v_abs_1123_, v_one_1124_);
        crate::leanh::lean_dec(v_abs_1123_);
        v___x_1126_ = crate::leanh::lean_apply_1(v_h__3_1112_, v_a_1125_);
        return v___x_1126_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(
    mut v_motive_1127_: *mut crate::leanh::LeanObject,
    mut v_x_1128_: *mut crate::leanh::LeanObject,
    mut v_h__1_1129_: *mut crate::leanh::LeanObject,
    mut v_h__2_1130_: *mut crate::leanh::LeanObject,
    mut v_h__3_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1132_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
        v_motive_1127_,
        v_x_1128_,
        v_h__1_1129_,
        v_h__2_1130_,
        v_h__3_1131_,
    );
    crate::leanh::lean_dec(v_x_1128_);
    return v_res_1132_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(
    mut v_x_1133_: *mut crate::leanh::LeanObject,
    mut v_h__1_1134_: *mut crate::leanh::LeanObject,
    mut v_h__2_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1133_) == 0 {
        let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1135_);
        v___x_1136_ = crate::leanh::lean_box(0);
        v___x_1137_ = crate::leanh::lean_apply_1(v_h__1_1134_, v___x_1136_);
        return v___x_1137_;
    } else {
        let mut v_n_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1134_);
        v_n_1138_ = crate::leanh::lean_ctor_get(v_x_1133_, 0);
        crate::leanh::lean_inc(v_n_1138_);
        v_k_1139_ = crate::leanh::lean_ctor_get(v_x_1133_, 1);
        crate::leanh::lean_inc(v_k_1139_);
        crate::leanh::lean_dec_ref_known(v_x_1133_, 2);
        v___x_1140_ = crate::leanh::lean_apply_3(
            v_h__2_1135_,
            v_n_1138_,
            v_k_1139_,
            crate::leanh::lean_box(0),
        );
        return v___x_1140_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(
    mut v_motive_1141_: *mut crate::leanh::LeanObject,
    mut v_x_1142_: *mut crate::leanh::LeanObject,
    mut v_h__1_1143_: *mut crate::leanh::LeanObject,
    mut v_h__2_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1142_) == 0 {
        let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1144_);
        v___x_1145_ = crate::leanh::lean_box(0);
        v___x_1146_ = crate::leanh::lean_apply_1(v_h__1_1143_, v___x_1145_);
        return v___x_1146_;
    } else {
        let mut v_n_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1143_);
        v_n_1147_ = crate::leanh::lean_ctor_get(v_x_1142_, 0);
        crate::leanh::lean_inc(v_n_1147_);
        v_k_1148_ = crate::leanh::lean_ctor_get(v_x_1142_, 1);
        crate::leanh::lean_inc(v_k_1148_);
        crate::leanh::lean_dec_ref_known(v_x_1142_, 2);
        v___x_1149_ = crate::leanh::lean_apply_3(
            v_h__2_1144_,
            v_n_1147_,
            v_k_1148_,
            crate::leanh::lean_box(0),
        );
        return v___x_1149_;
    }
}
pub unsafe fn l_Dyadic_precision(
    mut v_x_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1150_) == 0 {
        let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1151_ = crate::leanh::lean_box(0);
        return v___x_1151_;
    } else {
        let mut v_k_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_k_1152_ = crate::leanh::lean_ctor_get(v_x_1150_, 1);
        crate::leanh::lean_inc(v_k_1152_);
        v___x_1153_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1153_, 0, v_k_1152_);
        return v___x_1153_;
    }
}
pub unsafe fn l_Dyadic_precision___boxed(
    mut v_x_1154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Dyadic_precision(v_x_1154_);
    crate::leanh::lean_dec(v_x_1154_);
    return v_res_1155_;
}
pub unsafe fn l_Rat_toDyadic(
    mut v_x_1156_: *mut crate::leanh::LeanObject,
    mut v_prec_1157_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1159_: u8 = 0;
    v_intZero_1158_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1159_ = lean_int_dec_lt(v_prec_1157_, v_intZero_1158_);
    if v_isNeg_1159_ == 0 {
        let mut v_num_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_den_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_num_1160_ = crate::leanh::lean_ctor_get(v_x_1156_, 0);
        crate::leanh::lean_inc(v_num_1160_);
        v_den_1161_ = crate::leanh::lean_ctor_get(v_x_1156_, 1);
        crate::leanh::lean_inc(v_den_1161_);
        crate::leanh::lean_dec_ref(v_x_1156_);
        v_a_1162_ = lean_nat_abs(v_prec_1157_);
        v___x_1163_ = l_Int_shiftLeft(v_num_1160_, v_a_1162_);
        crate::leanh::lean_dec(v_a_1162_);
        crate::leanh::lean_dec(v_num_1160_);
        v___x_1164_ = lean_nat_to_int(v_den_1161_);
        v___x_1165_ = lean_int_ediv(v___x_1163_, v___x_1164_);
        crate::leanh::lean_dec(v___x_1164_);
        crate::leanh::lean_dec(v___x_1163_);
        v___x_1166_ = l_Dyadic_ofIntWithPrec(v___x_1165_, v_prec_1157_);
        return v___x_1166_;
    } else {
        let mut v_num_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_den_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_abs_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_num_1167_ = crate::leanh::lean_ctor_get(v_x_1156_, 0);
        crate::leanh::lean_inc(v_num_1167_);
        v_den_1168_ = crate::leanh::lean_ctor_get(v_x_1156_, 1);
        crate::leanh::lean_inc(v_den_1168_);
        crate::leanh::lean_dec_ref(v_x_1156_);
        v_abs_1169_ = lean_nat_abs(v_prec_1157_);
        v_one_1170_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_1171_ = lean_nat_sub(v_abs_1169_, v_one_1170_);
        crate::leanh::lean_dec(v_abs_1169_);
        v___x_1172_ = lean_nat_add(v_a_1171_, v_one_1170_);
        crate::leanh::lean_dec(v_a_1171_);
        v___x_1173_ = lean_nat_shiftl(v_den_1168_, v___x_1172_);
        crate::leanh::lean_dec(v___x_1172_);
        crate::leanh::lean_dec(v_den_1168_);
        v___x_1174_ = lean_nat_to_int(v___x_1173_);
        v___x_1175_ = lean_int_ediv(v_num_1167_, v___x_1174_);
        crate::leanh::lean_dec(v___x_1174_);
        crate::leanh::lean_dec(v_num_1167_);
        v___x_1176_ = l_Dyadic_ofIntWithPrec(v___x_1175_, v_prec_1157_);
        return v___x_1176_;
    }
}
pub unsafe fn l_Rat_toDyadic___boxed(
    mut v_x_1177_: *mut crate::leanh::LeanObject,
    mut v_prec_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Rat_toDyadic(v_x_1177_, v_prec_1178_);
    crate::leanh::lean_dec(v_prec_1178_);
    return v_res_1179_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
    mut v_prec_1180_: *mut crate::leanh::LeanObject,
    mut v_h__1_1181_: *mut crate::leanh::LeanObject,
    mut v_h__2_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1184_: u8 = 0;
    v_intZero_1183_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1184_ = lean_int_dec_lt(v_prec_1180_, v_intZero_1183_);
    if v_isNeg_1184_ == 0 {
        let mut v_a_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1182_);
        v_a_1185_ = lean_nat_abs(v_prec_1180_);
        v___x_1186_ = crate::leanh::lean_apply_1(v_h__1_1181_, v_a_1185_);
        return v___x_1186_;
    } else {
        let mut v_abs_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1181_);
        v_abs_1187_ = lean_nat_abs(v_prec_1180_);
        v_one_1188_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_1189_ = lean_nat_sub(v_abs_1187_, v_one_1188_);
        crate::leanh::lean_dec(v_abs_1187_);
        v___x_1190_ = crate::leanh::lean_apply_1(v_h__2_1182_, v_a_1189_);
        return v___x_1190_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(
    mut v_prec_1191_: *mut crate::leanh::LeanObject,
    mut v_h__1_1192_: *mut crate::leanh::LeanObject,
    mut v_h__2_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
        v_prec_1191_,
        v_h__1_1192_,
        v_h__2_1193_,
    );
    crate::leanh::lean_dec(v_prec_1191_);
    return v_res_1194_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
    mut v_motive_1195_: *mut crate::leanh::LeanObject,
    mut v_prec_1196_: *mut crate::leanh::LeanObject,
    mut v_h__1_1197_: *mut crate::leanh::LeanObject,
    mut v_h__2_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_intZero_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1200_: u8 = 0;
    v_intZero_1199_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1200_ = lean_int_dec_lt(v_prec_1196_, v_intZero_1199_);
    if v_isNeg_1200_ == 0 {
        let mut v_a_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1198_);
        v_a_1201_ = lean_nat_abs(v_prec_1196_);
        v___x_1202_ = crate::leanh::lean_apply_1(v_h__1_1197_, v_a_1201_);
        return v___x_1202_;
    } else {
        let mut v_abs_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1197_);
        v_abs_1203_ = lean_nat_abs(v_prec_1196_);
        v_one_1204_ = crate::leanh::lean_unsigned_to_nat(1);
        v_a_1205_ = lean_nat_sub(v_abs_1203_, v_one_1204_);
        crate::leanh::lean_dec(v_abs_1203_);
        v___x_1206_ = crate::leanh::lean_apply_1(v_h__2_1198_, v_a_1205_);
        return v___x_1206_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(
    mut v_motive_1207_: *mut crate::leanh::LeanObject,
    mut v_prec_1208_: *mut crate::leanh::LeanObject,
    mut v_h__1_1209_: *mut crate::leanh::LeanObject,
    mut v_h__2_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
        v_motive_1207_,
        v_prec_1208_,
        v_h__1_1209_,
        v_h__2_1210_,
    );
    crate::leanh::lean_dec(v_prec_1208_);
    return v_res_1211_;
}
pub unsafe fn l_Dyadic_roundDown(
    mut v_x_1212_: *mut crate::leanh::LeanObject,
    mut v_prec_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1212_) == 0 {
        return v_x_1212_;
    } else {
        let mut v_n_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1218_: u8 = 0;
        v_n_1214_ = crate::leanh::lean_ctor_get(v_x_1212_, 0);
        v_k_1215_ = crate::leanh::lean_ctor_get(v_x_1212_, 1);
        v___x_1216_ = lean_int_sub(v_k_1215_, v_prec_1213_);
        v_intZero_1217_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1218_ = lean_int_dec_lt(v___x_1216_, v_intZero_1217_);
        if v_isNeg_1218_ == 0 {
            let mut v_a_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1219_ = lean_nat_abs(v___x_1216_);
            crate::leanh::lean_dec(v___x_1216_);
            v___x_1220_ = l_Int_shiftRight(v_n_1214_, v_a_1219_);
            crate::leanh::lean_dec(v_a_1219_);
            v___x_1221_ = l_Dyadic_ofIntWithPrec(v___x_1220_, v_prec_1213_);
            return v___x_1221_;
        } else {
            crate::leanh::lean_dec(v___x_1216_);
            crate::leanh::lean_inc_ref(v_x_1212_);
            return v_x_1212_;
        }
    }
}
pub unsafe fn l_Dyadic_roundDown___boxed(
    mut v_x_1222_: *mut crate::leanh::LeanObject,
    mut v_prec_1223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Dyadic_roundDown(v_x_1222_, v_prec_1223_);
    crate::leanh::lean_dec(v_prec_1223_);
    crate::leanh::lean_dec(v_x_1222_);
    return v_res_1224_;
}
pub unsafe fn l_Dyadic_blt(
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v_y_1226_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1225_) == 0 {
        if crate::leanh::lean_obj_tag(v_y_1226_) == 0 {
            let mut v___x_1227_: u8 = 0;
            v___x_1227_ = 0;
            return v___x_1227_;
        } else {
            let mut v_n_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1230_: u8 = 0;
            v_n_1228_ = crate::leanh::lean_ctor_get(v_y_1226_, 0);
            v___x_1229_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1230_ = lean_int_dec_lt(v___x_1229_, v_n_1228_);
            return v___x_1230_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_y_1226_) == 0 {
            let mut v_n_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: u8 = 0;
            v_n_1231_ = crate::leanh::lean_ctor_get(v_x_1225_, 0);
            v___x_1232_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1233_ = lean_int_dec_lt(v_n_1231_, v___x_1232_);
            return v___x_1233_;
        } else {
            let mut v_n_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_intZero_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1240_: u8 = 0;
            v_n_1234_ = crate::leanh::lean_ctor_get(v_x_1225_, 0);
            v_k_1235_ = crate::leanh::lean_ctor_get(v_x_1225_, 1);
            v_n_1236_ = crate::leanh::lean_ctor_get(v_y_1226_, 0);
            v_k_1237_ = crate::leanh::lean_ctor_get(v_y_1226_, 1);
            v___x_1238_ = lean_int_sub(v_k_1237_, v_k_1235_);
            v_intZero_1239_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1240_ = lean_int_dec_lt(v___x_1238_, v_intZero_1239_);
            if v_isNeg_1240_ == 0 {
                let mut v_a_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1243_: u8 = 0;
                v_a_1241_ = lean_nat_abs(v___x_1238_);
                crate::leanh::lean_dec(v___x_1238_);
                v___x_1242_ = l_Int_shiftLeft(v_n_1234_, v_a_1241_);
                crate::leanh::lean_dec(v_a_1241_);
                v___x_1243_ = lean_int_dec_lt(v___x_1242_, v_n_1236_);
                crate::leanh::lean_dec(v___x_1242_);
                return v___x_1243_;
            } else {
                let mut v_abs_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1249_: u8 = 0;
                v_abs_1244_ = lean_nat_abs(v___x_1238_);
                crate::leanh::lean_dec(v___x_1238_);
                v_one_1245_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_1246_ = lean_nat_sub(v_abs_1244_, v_one_1245_);
                crate::leanh::lean_dec(v_abs_1244_);
                v___x_1247_ = lean_nat_add(v_a_1246_, v_one_1245_);
                crate::leanh::lean_dec(v_a_1246_);
                v___x_1248_ = l_Int_shiftLeft(v_n_1236_, v___x_1247_);
                crate::leanh::lean_dec(v___x_1247_);
                v___x_1249_ = lean_int_dec_lt(v_n_1234_, v___x_1248_);
                crate::leanh::lean_dec(v___x_1248_);
                return v___x_1249_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_blt___boxed(
    mut v_x_1250_: *mut crate::leanh::LeanObject,
    mut v_y_1251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1252_: u8 = 0;
    let mut v_r_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1252_ = l_Dyadic_blt(v_x_1250_, v_y_1251_);
    crate::leanh::lean_dec(v_y_1251_);
    crate::leanh::lean_dec(v_x_1250_);
    v_r_1253_ = crate::leanh::lean_box((v_res_1252_) as usize);
    return v_r_1253_;
}
pub unsafe fn l_Dyadic_ble(
    mut v_x_1254_: *mut crate::leanh::LeanObject,
    mut v_y_1255_: *mut crate::leanh::LeanObject,
) -> u8 {
    if crate::leanh::lean_obj_tag(v_x_1254_) == 0 {
        if crate::leanh::lean_obj_tag(v_y_1255_) == 0 {
            let mut v___x_1256_: u8 = 0;
            v___x_1256_ = 1;
            return v___x_1256_;
        } else {
            let mut v_n_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1259_: u8 = 0;
            v_n_1257_ = crate::leanh::lean_ctor_get(v_y_1255_, 0);
            v___x_1258_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1259_ = lean_int_dec_le(v___x_1258_, v_n_1257_);
            return v___x_1259_;
        }
    } else {
        if crate::leanh::lean_obj_tag(v_y_1255_) == 0 {
            let mut v_n_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: u8 = 0;
            v_n_1260_ = crate::leanh::lean_ctor_get(v_x_1254_, 0);
            v___x_1261_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1262_ = lean_int_dec_le(v_n_1260_, v___x_1261_);
            return v___x_1262_;
        } else {
            let mut v_n_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_intZero_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1269_: u8 = 0;
            v_n_1263_ = crate::leanh::lean_ctor_get(v_x_1254_, 0);
            v_k_1264_ = crate::leanh::lean_ctor_get(v_x_1254_, 1);
            v_n_1265_ = crate::leanh::lean_ctor_get(v_y_1255_, 0);
            v_k_1266_ = crate::leanh::lean_ctor_get(v_y_1255_, 1);
            v___x_1267_ = lean_int_sub(v_k_1266_, v_k_1264_);
            v_intZero_1268_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1269_ = lean_int_dec_lt(v___x_1267_, v_intZero_1268_);
            if v_isNeg_1269_ == 0 {
                let mut v_a_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1272_: u8 = 0;
                v_a_1270_ = lean_nat_abs(v___x_1267_);
                crate::leanh::lean_dec(v___x_1267_);
                v___x_1271_ = l_Int_shiftLeft(v_n_1263_, v_a_1270_);
                crate::leanh::lean_dec(v_a_1270_);
                v___x_1272_ = lean_int_dec_le(v___x_1271_, v_n_1265_);
                crate::leanh::lean_dec(v___x_1271_);
                return v___x_1272_;
            } else {
                let mut v_abs_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_one_1274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v_a_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1278_: u8 = 0;
                v_abs_1273_ = lean_nat_abs(v___x_1267_);
                crate::leanh::lean_dec(v___x_1267_);
                v_one_1274_ = crate::leanh::lean_unsigned_to_nat(1);
                v_a_1275_ = lean_nat_sub(v_abs_1273_, v_one_1274_);
                crate::leanh::lean_dec(v_abs_1273_);
                v___x_1276_ = lean_nat_add(v_a_1275_, v_one_1274_);
                crate::leanh::lean_dec(v_a_1275_);
                v___x_1277_ = l_Int_shiftLeft(v_n_1265_, v___x_1276_);
                crate::leanh::lean_dec(v___x_1276_);
                v___x_1278_ = lean_int_dec_le(v_n_1263_, v___x_1277_);
                crate::leanh::lean_dec(v___x_1277_);
                return v___x_1278_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_ble___boxed(
    mut v_x_1279_: *mut crate::leanh::LeanObject,
    mut v_y_1280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1281_: u8 = 0;
    let mut v_r_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Dyadic_ble(v_x_1279_, v_y_1280_);
    crate::leanh::lean_dec(v_y_1280_);
    crate::leanh::lean_dec(v_x_1279_);
    v_r_1282_ = crate::leanh::lean_box((v_res_1281_) as usize);
    return v_r_1282_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(
    mut v_x_1283_: *mut crate::leanh::LeanObject,
    mut v_x_1284_: *mut crate::leanh::LeanObject,
    mut v_h__1_1285_: *mut crate::leanh::LeanObject,
    mut v_h__2_1286_: *mut crate::leanh::LeanObject,
    mut v_h__3_1287_: *mut crate::leanh::LeanObject,
    mut v_h__4_1288_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1283_) == 0 {
        crate::leanh::lean_dec(v_h__4_1288_);
        crate::leanh::lean_dec(v_h__3_1287_);
        if crate::leanh::lean_obj_tag(v_x_1284_) == 0 {
            let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1286_);
            v___x_1289_ = crate::leanh::lean_box(0);
            v___x_1290_ = crate::leanh::lean_apply_1(v_h__1_1285_, v___x_1289_);
            return v___x_1290_;
        } else {
            let mut v_n_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1285_);
            v_n_1291_ = crate::leanh::lean_ctor_get(v_x_1284_, 0);
            crate::leanh::lean_inc(v_n_1291_);
            v_k_1292_ = crate::leanh::lean_ctor_get(v_x_1284_, 1);
            crate::leanh::lean_inc(v_k_1292_);
            crate::leanh::lean_dec_ref_known(v_x_1284_, 2);
            v___x_1293_ = crate::leanh::lean_apply_3(
                v_h__2_1286_,
                v_n_1291_,
                v_k_1292_,
                crate::leanh::lean_box(0),
            );
            return v___x_1293_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1286_);
        crate::leanh::lean_dec(v_h__1_1285_);
        if crate::leanh::lean_obj_tag(v_x_1284_) == 0 {
            let mut v_n_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1288_);
            v_n_1294_ = crate::leanh::lean_ctor_get(v_x_1283_, 0);
            crate::leanh::lean_inc(v_n_1294_);
            v_k_1295_ = crate::leanh::lean_ctor_get(v_x_1283_, 1);
            crate::leanh::lean_inc(v_k_1295_);
            crate::leanh::lean_dec_ref_known(v_x_1283_, 2);
            v___x_1296_ = crate::leanh::lean_apply_3(
                v_h__3_1287_,
                v_n_1294_,
                v_k_1295_,
                crate::leanh::lean_box(0),
            );
            return v___x_1296_;
        } else {
            let mut v_n_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1287_);
            v_n_1297_ = crate::leanh::lean_ctor_get(v_x_1283_, 0);
            crate::leanh::lean_inc(v_n_1297_);
            v_k_1298_ = crate::leanh::lean_ctor_get(v_x_1283_, 1);
            crate::leanh::lean_inc(v_k_1298_);
            crate::leanh::lean_dec_ref_known(v_x_1283_, 2);
            v_n_1299_ = crate::leanh::lean_ctor_get(v_x_1284_, 0);
            crate::leanh::lean_inc(v_n_1299_);
            v_k_1300_ = crate::leanh::lean_ctor_get(v_x_1284_, 1);
            crate::leanh::lean_inc(v_k_1300_);
            crate::leanh::lean_dec_ref_known(v_x_1284_, 2);
            v___x_1301_ = crate::leanh::lean_apply_6(
                v_h__4_1288_,
                v_n_1297_,
                v_k_1298_,
                crate::leanh::lean_box(0),
                v_n_1299_,
                v_k_1300_,
                crate::leanh::lean_box(0),
            );
            return v___x_1301_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(
    mut v_motive_1302_: *mut crate::leanh::LeanObject,
    mut v_x_1303_: *mut crate::leanh::LeanObject,
    mut v_x_1304_: *mut crate::leanh::LeanObject,
    mut v_h__1_1305_: *mut crate::leanh::LeanObject,
    mut v_h__2_1306_: *mut crate::leanh::LeanObject,
    mut v_h__3_1307_: *mut crate::leanh::LeanObject,
    mut v_h__4_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1303_) == 0 {
        crate::leanh::lean_dec(v_h__4_1308_);
        crate::leanh::lean_dec(v_h__3_1307_);
        if crate::leanh::lean_obj_tag(v_x_1304_) == 0 {
            let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1306_);
            v___x_1309_ = crate::leanh::lean_box(0);
            v___x_1310_ = crate::leanh::lean_apply_1(v_h__1_1305_, v___x_1309_);
            return v___x_1310_;
        } else {
            let mut v_n_1311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__1_1305_);
            v_n_1311_ = crate::leanh::lean_ctor_get(v_x_1304_, 0);
            crate::leanh::lean_inc(v_n_1311_);
            v_k_1312_ = crate::leanh::lean_ctor_get(v_x_1304_, 1);
            crate::leanh::lean_inc(v_k_1312_);
            crate::leanh::lean_dec_ref_known(v_x_1304_, 2);
            v___x_1313_ = crate::leanh::lean_apply_3(
                v_h__2_1306_,
                v_n_1311_,
                v_k_1312_,
                crate::leanh::lean_box(0),
            );
            return v___x_1313_;
        }
    } else {
        crate::leanh::lean_dec(v_h__2_1306_);
        crate::leanh::lean_dec(v_h__1_1305_);
        if crate::leanh::lean_obj_tag(v_x_1304_) == 0 {
            let mut v_n_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1308_);
            v_n_1314_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
            crate::leanh::lean_inc(v_n_1314_);
            v_k_1315_ = crate::leanh::lean_ctor_get(v_x_1303_, 1);
            crate::leanh::lean_inc(v_k_1315_);
            crate::leanh::lean_dec_ref_known(v_x_1303_, 2);
            v___x_1316_ = crate::leanh::lean_apply_3(
                v_h__3_1307_,
                v_n_1314_,
                v_k_1315_,
                crate::leanh::lean_box(0),
            );
            return v___x_1316_;
        } else {
            let mut v_n_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_n_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_k_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1307_);
            v_n_1317_ = crate::leanh::lean_ctor_get(v_x_1303_, 0);
            crate::leanh::lean_inc(v_n_1317_);
            v_k_1318_ = crate::leanh::lean_ctor_get(v_x_1303_, 1);
            crate::leanh::lean_inc(v_k_1318_);
            crate::leanh::lean_dec_ref_known(v_x_1303_, 2);
            v_n_1319_ = crate::leanh::lean_ctor_get(v_x_1304_, 0);
            crate::leanh::lean_inc(v_n_1319_);
            v_k_1320_ = crate::leanh::lean_ctor_get(v_x_1304_, 1);
            crate::leanh::lean_inc(v_k_1320_);
            crate::leanh::lean_dec_ref_known(v_x_1304_, 2);
            v___x_1321_ = crate::leanh::lean_apply_6(
                v_h__4_1308_,
                v_n_1317_,
                v_k_1318_,
                crate::leanh::lean_box(0),
                v_n_1319_,
                v_k_1320_,
                crate::leanh::lean_box(0),
            );
            return v___x_1321_;
        }
    }
}
pub unsafe fn _init_l_Dyadic_instLT() -> *mut crate::leanh::LeanObject {
    let mut v___x_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1322_ = crate::leanh::lean_box(0);
    return v___x_1322_;
}
pub unsafe fn _init_l_Dyadic_instLE() -> *mut crate::leanh::LeanObject {
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = crate::leanh::lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_Dyadic_instDecidableLT(
    mut v_x_1324_: *mut crate::leanh::LeanObject,
    mut v_x_1325_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1326_: u8 = 0;
    v___x_1326_ = l_Dyadic_blt(v_x_1324_, v_x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Dyadic_instDecidableLT___boxed(
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_x_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1329_: u8 = 0;
    let mut v_r_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1329_ = l_Dyadic_instDecidableLT(v_x_1327_, v_x_1328_);
    crate::leanh::lean_dec(v_x_1328_);
    crate::leanh::lean_dec(v_x_1327_);
    v_r_1330_ = crate::leanh::lean_box((v_res_1329_) as usize);
    return v_r_1330_;
}
pub unsafe fn l_Dyadic_instDecidableLE(
    mut v_x_1331_: *mut crate::leanh::LeanObject,
    mut v_x_1332_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    v___x_1333_ = l_Dyadic_ble(v_x_1331_, v_x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Dyadic_instDecidableLE___boxed(
    mut v_x_1334_: *mut crate::leanh::LeanObject,
    mut v_x_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Dyadic_instDecidableLE(v_x_1334_, v_x_1335_);
    crate::leanh::lean_dec(v_x_1335_);
    crate::leanh::lean_dec(v_x_1334_);
    v_r_1337_ = crate::leanh::lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Dyadic_roundUp(
    mut v_x_1338_: *mut crate::leanh::LeanObject,
    mut v_prec_1339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1338_) == 0 {
        return v_x_1338_;
    } else {
        let mut v_n_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_intZero_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1344_: u8 = 0;
        v_n_1340_ = crate::leanh::lean_ctor_get(v_x_1338_, 0);
        v_k_1341_ = crate::leanh::lean_ctor_get(v_x_1338_, 1);
        v___x_1342_ = lean_int_sub(v_k_1341_, v_prec_1339_);
        v_intZero_1343_ = crate::leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1344_ = lean_int_dec_lt(v___x_1342_, v_intZero_1343_);
        if v_isNeg_1344_ == 0 {
            let mut v_a_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1345_ = lean_nat_abs(v___x_1342_);
            crate::leanh::lean_dec(v___x_1342_);
            v___x_1346_ = lean_int_neg(v_n_1340_);
            v___x_1347_ = l_Int_shiftRight(v___x_1346_, v_a_1345_);
            crate::leanh::lean_dec(v_a_1345_);
            crate::leanh::lean_dec(v___x_1346_);
            v___x_1348_ = lean_int_neg(v___x_1347_);
            crate::leanh::lean_dec(v___x_1347_);
            v___x_1349_ = l_Dyadic_ofIntWithPrec(v___x_1348_, v_prec_1339_);
            return v___x_1349_;
        } else {
            crate::leanh::lean_dec(v___x_1342_);
            crate::leanh::lean_inc_ref(v_x_1338_);
            return v_x_1338_;
        }
    }
}
pub unsafe fn l_Dyadic_roundUp___boxed(
    mut v_x_1350_: *mut crate::leanh::LeanObject,
    mut v_prec_1351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1352_ = l_Dyadic_roundUp(v_x_1350_, v_prec_1351_);
    crate::leanh::lean_dec(v_prec_1351_);
    crate::leanh::lean_dec(v_x_1350_);
    return v_res_1352_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Dyadic_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Dyadic_instLT = _init_l_Dyadic_instLT();
    crate::leanh::lean_mark_persistent(l_Dyadic_instLT);
    l_Dyadic_instLE = _init_l_Dyadic_instLE();
    crate::leanh::lean_mark_persistent(l_Dyadic_instLE);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Dyadic_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Dyadic_Basic(builtin);
}

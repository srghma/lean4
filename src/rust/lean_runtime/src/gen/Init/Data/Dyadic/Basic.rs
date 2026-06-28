// Lean compiler output
// Module: Init.Data.Dyadic.Basic
// Imports: Init.Data.Int.Bitwise.Lemmas Init.Data.Int.Bitwise.Basic Init.Data.Order.Classes Init.Data.Rat.Basic Init.ByCases Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Bitwise.Lemmas Init.Data.Option.Lemmas Init.Data.Rat.Lemmas Init.Omega
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_mul, lean_int_neg,
    lean_int_sub, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Int::DivMod::Basic::{lean_int_ediv, lean_int_emod};
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftl;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_pow, lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_6, lean_box, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec,
    lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Int_trailingZeros_aux___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_trailingZeros_aux___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Int_trailingZeros_aux___redArg___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_trailingZeros_aux___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Dyadic_instIntCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_ofInt as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instIntCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instIntCast: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instIntCast___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instNatCast___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_instNatCast___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instNatCast___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instNatCast: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNatCast___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instAdd___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_add as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instAdd___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instAdd: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instAdd___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instMul___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_mul___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instMul___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instMul: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instMul___closed__0_value) as *mut LeanObject;
static mut l_Dyadic_pow___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Dyadic_pow___closed__2_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_pow___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l_Dyadic_instPowNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_pow as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instPowNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instPowNat: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instPowNat___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instNeg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_neg as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instNeg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instNeg: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instNeg___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instSub___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_sub as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instSub___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instSub: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instSub___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instHShiftLeftInt___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_shiftLeft___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instHShiftLeftInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instHShiftLeftInt: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftInt___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instHShiftRightInt___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Dyadic_shiftRight___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightInt___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instHShiftRightInt: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightInt___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instHShiftLeftNat___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Dyadic_instHShiftLeftNat___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Dyadic_instHShiftLeftNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instHShiftLeftNat: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftLeftNat___closed__0_value) as *mut LeanObject;
pub static l_Dyadic_instHShiftRightNat___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Dyadic_instHShiftRightNat___lam__0 as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Dyadic_instHShiftRightNat___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value) as *mut LeanObject;
pub static mut l_Dyadic_instHShiftRightNat: *mut LeanObject =
    core::ptr::addr_of!(l_Dyadic_instHShiftRightNat___closed__0_value) as *mut LeanObject;
static mut l_Dyadic_toRat___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Dyadic_toRat___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLT: *mut LeanObject = core::ptr::null_mut();
pub static mut l_Dyadic_instLE: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut LeanObject = core::ptr::null_mut();
    v___x_677_ = lean_unsigned_to_nat(2);
    v___x_678_ = lean_nat_to_int(v___x_677_);
    return v___x_678_;
}
pub unsafe fn _init_l_Int_trailingZeros_aux___redArg___closed__1() -> *mut LeanObject {
    let mut v_zero_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_680_: *mut LeanObject = core::ptr::null_mut();
    v_zero_679_ = lean_unsigned_to_nat(0);
    v___x_680_ = lean_nat_to_int(v_zero_679_);
    return v___x_680_;
}
pub unsafe fn l_Int_trailingZeros_aux___redArg(
    mut v_k_681_: *mut LeanObject,
    mut v_i_682_: *mut LeanObject,
    mut v_acc_683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_685_: u8 = 0;
    let mut v___x_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_689_: u8 = 0;
    let mut v_one_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_684_ = lean_unsigned_to_nat(0);
                v_isZero_685_ = lean_nat_dec_eq(v_k_681_, v_zero_684_);
                v___x_686_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__0_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__0,
                );
                v___x_687_ = lean_int_emod(v_i_682_, v___x_686_);
                v___x_688_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v___x_689_ = lean_int_dec_eq(v___x_687_, v___x_688_);
                lean_dec(v___x_687_);
                if v___x_689_ == 0 {
                    lean_dec(v_i_682_);
                    lean_dec(v_k_681_);
                    return v_acc_683_;
                } else {
                    v_one_690_ = lean_unsigned_to_nat(1);
                    v_n_691_ = lean_nat_sub(v_k_681_, v_one_690_);
                    lean_dec(v_k_681_);
                    v___x_692_ = lean_int_ediv(v_i_682_, v___x_686_);
                    lean_dec(v_i_682_);
                    v___x_693_ = lean_nat_add(v_acc_683_, v_one_690_);
                    lean_dec(v_acc_683_);
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
    mut v_k_695_: *mut LeanObject,
    mut v_i_696_: *mut LeanObject,
    mut v_hi_697_: *mut LeanObject,
    mut v_hk_698_: *mut LeanObject,
    mut v_acc_699_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    v___x_700_ = l_Int_trailingZeros_aux___redArg(v_k_695_, v_i_696_, v_acc_699_);
    return v___x_700_;
}
pub unsafe fn l_Int_trailingZeros(mut v_i_701_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: u8 = 0;
    v___x_702_ = lean_unsigned_to_nat(0);
    v___x_703_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_704_ = lean_int_dec_eq(v_i_701_, v___x_703_);
    if v___x_704_ == 0 {
        let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
        v___x_705_ = lean_nat_abs(v_i_701_);
        v___x_706_ = l_Int_trailingZeros_aux___redArg(v___x_705_, v_i_701_, v___x_702_);
        return v___x_706_;
    } else {
        lean_dec(v_i_701_);
        return v___x_702_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
    mut v_k_707_: *mut LeanObject,
    mut v_h__1_708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_710_: u8 = 0;
    let mut v_one_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    v_zero_709_ = lean_unsigned_to_nat(0);
    v_isZero_710_ = lean_nat_dec_eq(v_k_707_, v_zero_709_);
    v_one_711_ = lean_unsigned_to_nat(1);
    v_n_712_ = lean_nat_sub(v_k_707_, v_one_711_);
    v___x_713_ = lean_apply_3(v_h__1_708_, v_n_712_, lean_box(0), lean_box(0));
    return v___x_713_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg___boxed(
    mut v_k_714_: *mut LeanObject,
    mut v_h__1_715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_716_: *mut LeanObject = core::ptr::null_mut();
    v_res_716_ =
        l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___redArg(
            v_k_714_,
            v_h__1_715_,
        );
    lean_dec(v_k_714_);
    return v_res_716_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
    mut v_i_717_: *mut LeanObject,
    mut v_motive_718_: *mut LeanObject,
    mut v_k_719_: *mut LeanObject,
    mut v_x_720_: *mut LeanObject,
    mut v_hk_721_: *mut LeanObject,
    mut v_h__1_722_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_724_: u8 = 0;
    let mut v_one_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    v_zero_723_ = lean_unsigned_to_nat(0);
    v_isZero_724_ = lean_nat_dec_eq(v_k_719_, v_zero_723_);
    v_one_725_ = lean_unsigned_to_nat(1);
    v_n_726_ = lean_nat_sub(v_k_719_, v_one_725_);
    v___x_727_ = lean_apply_3(v_h__1_722_, v_n_726_, lean_box(0), lean_box(0));
    return v___x_727_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter___boxed(
    mut v_i_728_: *mut LeanObject,
    mut v_motive_729_: *mut LeanObject,
    mut v_k_730_: *mut LeanObject,
    mut v_x_731_: *mut LeanObject,
    mut v_hk_732_: *mut LeanObject,
    mut v_h__1_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_734_: *mut LeanObject = core::ptr::null_mut();
    v_res_734_ = l___private_Init_Data_Dyadic_Basic_0__Int_trailingZeros_aux_match__1_splitter(
        v_i_728_,
        v_motive_729_,
        v_k_730_,
        v_x_731_,
        v_hk_732_,
        v_h__1_733_,
    );
    lean_dec(v_k_730_);
    lean_dec(v_i_728_);
    return v_res_734_;
}
pub unsafe fn l_Dyadic_ctorIdx(mut v_x_735_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_735_) == 0 {
        let mut v___x_736_: *mut LeanObject = core::ptr::null_mut();
        v___x_736_ = lean_unsigned_to_nat(0);
        return v___x_736_;
    } else {
        let mut v___x_737_: *mut LeanObject = core::ptr::null_mut();
        v___x_737_ = lean_unsigned_to_nat(1);
        return v___x_737_;
    }
}
pub unsafe fn l_Dyadic_ctorIdx___boxed(mut v_x_738_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_739_: *mut LeanObject = core::ptr::null_mut();
    v_res_739_ = l_Dyadic_ctorIdx(v_x_738_);
    lean_dec(v_x_738_);
    return v_res_739_;
}
pub unsafe fn l_Dyadic_ctorElim___redArg(
    mut v_t_740_: *mut LeanObject,
    mut v_k_741_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_740_) == 0 {
        return v_k_741_;
    } else {
        let mut v_n_742_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_743_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_744_: *mut LeanObject = core::ptr::null_mut();
        v_n_742_ = lean_ctor_get(v_t_740_, 0);
        lean_inc(v_n_742_);
        v_k_743_ = lean_ctor_get(v_t_740_, 1);
        lean_inc(v_k_743_);
        lean_dec_ref_known(v_t_740_, 2);
        v___x_744_ = lean_apply_3(v_k_741_, v_n_742_, v_k_743_, lean_box(0));
        return v___x_744_;
    }
}
pub unsafe fn l_Dyadic_ctorElim(
    mut v_motive_745_: *mut LeanObject,
    mut v_ctorIdx_746_: *mut LeanObject,
    mut v_t_747_: *mut LeanObject,
    mut v_h_748_: *mut LeanObject,
    mut v_k_749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_750_: *mut LeanObject = core::ptr::null_mut();
    v___x_750_ = l_Dyadic_ctorElim___redArg(v_t_747_, v_k_749_);
    return v___x_750_;
}
pub unsafe fn l_Dyadic_ctorElim___boxed(
    mut v_motive_751_: *mut LeanObject,
    mut v_ctorIdx_752_: *mut LeanObject,
    mut v_t_753_: *mut LeanObject,
    mut v_h_754_: *mut LeanObject,
    mut v_k_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_756_: *mut LeanObject = core::ptr::null_mut();
    v_res_756_ = l_Dyadic_ctorElim(v_motive_751_, v_ctorIdx_752_, v_t_753_, v_h_754_, v_k_755_);
    lean_dec(v_ctorIdx_752_);
    return v_res_756_;
}
pub unsafe fn l_Dyadic_zero_elim___redArg(
    mut v_t_757_: *mut LeanObject,
    mut v_zero_758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_759_: *mut LeanObject = core::ptr::null_mut();
    v___x_759_ = l_Dyadic_ctorElim___redArg(v_t_757_, v_zero_758_);
    return v___x_759_;
}
pub unsafe fn l_Dyadic_zero_elim(
    mut v_motive_760_: *mut LeanObject,
    mut v_t_761_: *mut LeanObject,
    mut v_h_762_: *mut LeanObject,
    mut v_zero_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    v___x_764_ = l_Dyadic_ctorElim___redArg(v_t_761_, v_zero_763_);
    return v___x_764_;
}
pub unsafe fn l_Dyadic_ofOdd_elim___redArg(
    mut v_t_765_: *mut LeanObject,
    mut v_ofOdd_766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_767_: *mut LeanObject = core::ptr::null_mut();
    v___x_767_ = l_Dyadic_ctorElim___redArg(v_t_765_, v_ofOdd_766_);
    return v___x_767_;
}
pub unsafe fn l_Dyadic_ofOdd_elim(
    mut v_motive_768_: *mut LeanObject,
    mut v_t_769_: *mut LeanObject,
    mut v_h_770_: *mut LeanObject,
    mut v_ofOdd_771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    v___x_772_ = l_Dyadic_ctorElim___redArg(v_t_769_, v_ofOdd_771_);
    return v___x_772_;
}
pub unsafe fn l_instDecidableEqDyadic_decEq(
    mut v_x_773_: *mut LeanObject,
    mut v_x_774_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_x_773_) == 0 {
        if lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_775_: u8 = 0;
            v___x_775_ = 1;
            return v___x_775_;
        } else {
            let mut v___x_776_: u8 = 0;
            v___x_776_ = 0;
            return v___x_776_;
        }
    } else {
        if lean_obj_tag(v_x_774_) == 0 {
            let mut v___x_777_: u8 = 0;
            v___x_777_ = 0;
            return v___x_777_;
        } else {
            let mut v_n_778_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_779_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_780_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_781_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_782_: u8 = 0;
            v_n_778_ = lean_ctor_get(v_x_773_, 0);
            v_k_779_ = lean_ctor_get(v_x_773_, 1);
            v_n_780_ = lean_ctor_get(v_x_774_, 0);
            v_k_781_ = lean_ctor_get(v_x_774_, 1);
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
    mut v_x_784_: *mut LeanObject,
    mut v_x_785_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_786_: u8 = 0;
    let mut v_r_787_: *mut LeanObject = core::ptr::null_mut();
    v_res_786_ = l_instDecidableEqDyadic_decEq(v_x_784_, v_x_785_);
    lean_dec(v_x_785_);
    lean_dec(v_x_784_);
    v_r_787_ = lean_box((v_res_786_) as usize);
    return v_r_787_;
}
pub unsafe fn l_instDecidableEqDyadic(
    mut v_x_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
) -> u8 {
    let mut v___x_790_: u8 = 0;
    v___x_790_ = l_instDecidableEqDyadic_decEq(v_x_788_, v_x_789_);
    return v___x_790_;
}
pub unsafe fn l_instDecidableEqDyadic___boxed(
    mut v_x_791_: *mut LeanObject,
    mut v_x_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_793_: u8 = 0;
    let mut v_r_794_: *mut LeanObject = core::ptr::null_mut();
    v_res_793_ = l_instDecidableEqDyadic(v_x_791_, v_x_792_);
    lean_dec(v_x_792_);
    lean_dec(v_x_791_);
    v_r_794_ = lean_box((v_res_793_) as usize);
    return v_r_794_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_ofIntWithPrec_spec__0(
    mut v_a_795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    v___x_796_ = lean_nat_to_int(v_a_795_);
    return v___x_796_;
}
pub unsafe fn l_Dyadic_ofIntWithPrec(
    mut v_i_797_: *mut LeanObject,
    mut v_prec_798_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u8 = 0;
    v___x_799_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_800_ = lean_int_dec_eq(v_i_797_, v___x_799_);
    if v___x_800_ == 0 {
        let mut v___x_801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_802_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_804_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
        lean_inc(v_i_797_);
        v___x_801_ = l_Int_trailingZeros(v_i_797_);
        v___x_802_ = l_Int_shiftRight(v_i_797_, v___x_801_);
        lean_dec(v_i_797_);
        v___x_803_ = lean_nat_to_int(v___x_801_);
        v___x_804_ = lean_int_sub(v_prec_798_, v___x_803_);
        lean_dec(v___x_803_);
        v___x_805_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_805_, 0, v___x_802_);
        lean_ctor_set(v___x_805_, 1, v___x_804_);
        return v___x_805_;
    } else {
        let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_797_);
        v___x_806_ = lean_box(0);
        return v___x_806_;
    }
}
pub unsafe fn l_Dyadic_ofIntWithPrec___boxed(
    mut v_i_807_: *mut LeanObject,
    mut v_prec_808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_809_: *mut LeanObject = core::ptr::null_mut();
    v_res_809_ = l_Dyadic_ofIntWithPrec(v_i_807_, v_prec_808_);
    lean_dec(v_prec_808_);
    return v_res_809_;
}
pub unsafe fn l_Dyadic_ofInt(mut v_i_810_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    v___x_811_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_812_ = l_Dyadic_ofIntWithPrec(v_i_810_, v___x_811_);
    return v___x_812_;
}
pub unsafe fn l_Dyadic_instOfNat(mut v_n_813_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    v___x_814_ = lean_nat_to_int(v_n_813_);
    v___x_815_ = l_Dyadic_ofInt(v___x_814_);
    return v___x_815_;
}
pub unsafe fn l_Dyadic_instNatCast___lam__0(mut v_x_818_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    v___x_819_ = lean_nat_to_int(v_x_818_);
    v___x_820_ = l_Dyadic_ofInt(v___x_819_);
    return v___x_820_;
}
pub unsafe fn l_Dyadic_add(
    mut v_x_823_: *mut LeanObject,
    mut v_y_824_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_829_: u8 = 0;
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_833_: u8 = 0;
    let mut v_n_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_840_: u8 = 0;
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natZero_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_844_: u8 = 0;
    let mut v_a_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_846_: u8 = 0;
    let mut v___x_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_863_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_823_) == 0 {
                    return v_y_824_;
                } else {
                    if lean_obj_tag(v_y_824_) == 0 {
                        v_n_825_ = lean_ctor_get(v_x_823_, 0);
                        v_k_826_ = lean_ctor_get(v_x_823_, 1);
                        v_isSharedCheck_833_ = (!lean_is_exclusive(v_x_823_)) as u8;
                        if v_isSharedCheck_833_ == 0 {
                            v___x_828_ = v_x_823_;
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_826_);
                            lean_inc(v_n_825_);
                            lean_dec(v_x_823_);
                            v___x_828_ = lean_box(0);
                            v_isShared_829_ = v_isSharedCheck_833_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_n_834_ = lean_ctor_get(v_x_823_, 0);
                        lean_inc(v_n_834_);
                        v_k_835_ = lean_ctor_get(v_x_823_, 1);
                        lean_inc(v_k_835_);
                        lean_dec_ref_known(v_x_823_, 2);
                        v_n_836_ = lean_ctor_get(v_y_824_, 0);
                        v_k_837_ = lean_ctor_get(v_y_824_, 1);
                        v_isSharedCheck_863_ = (!lean_is_exclusive(v_y_824_)) as u8;
                        if v_isSharedCheck_863_ == 0 {
                            v___x_839_ = v_y_824_;
                            v_isShared_840_ = v_isSharedCheck_863_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_k_837_);
                            lean_inc(v_n_836_);
                            lean_dec(v_y_824_);
                            v___x_839_ = lean_box(0);
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
                    v_reuseFailAlloc_832_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_832_, 0, v_n_825_);
                    lean_ctor_set(v_reuseFailAlloc_832_, 1, v_k_826_);
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
                v_natZero_842_ = lean_unsigned_to_nat(0);
                v_intZero_843_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_844_ = lean_int_dec_lt(v___x_841_, v_intZero_843_);
                if v_isNeg_844_ == 0 {
                    lean_dec(v_k_837_);
                    v_a_845_ = lean_nat_abs(v___x_841_);
                    lean_dec(v___x_841_);
                    v_isZero_846_ = lean_nat_dec_eq(v_a_845_, v_natZero_842_);
                    if v_isZero_846_ == 1 {
                        lean_dec(v_a_845_);
                        lean_del_object(v___x_839_);
                        v___x_847_ = lean_int_add(v_n_834_, v_n_836_);
                        lean_dec(v_n_836_);
                        lean_dec(v_n_834_);
                        v___x_848_ = l_Dyadic_ofIntWithPrec(v___x_847_, v_k_835_);
                        lean_dec(v_k_835_);
                        return v___x_848_;
                    } else {
                        v___x_849_ = l_Int_shiftLeft(v_n_836_, v_a_845_);
                        lean_dec(v_a_845_);
                        lean_dec(v_n_836_);
                        v___x_850_ = lean_int_add(v_n_834_, v___x_849_);
                        lean_dec(v___x_849_);
                        lean_dec(v_n_834_);
                        if v_isShared_840_ == 0 {
                            lean_ctor_set(v___x_839_, 1, v_k_835_);
                            lean_ctor_set(v___x_839_, 0, v___x_850_);
                            v___x_852_ = v___x_839_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
                            lean_ctor_set(v_reuseFailAlloc_853_, 1, v_k_835_);
                            v___x_852_ = v_reuseFailAlloc_853_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_k_835_);
                    v_abs_854_ = lean_nat_abs(v___x_841_);
                    lean_dec(v___x_841_);
                    v_one_855_ = lean_unsigned_to_nat(1);
                    v_a_856_ = lean_nat_sub(v_abs_854_, v_one_855_);
                    lean_dec(v_abs_854_);
                    v___x_857_ = lean_nat_add(v_a_856_, v_one_855_);
                    lean_dec(v_a_856_);
                    v___x_858_ = l_Int_shiftLeft(v_n_834_, v___x_857_);
                    lean_dec(v___x_857_);
                    lean_dec(v_n_834_);
                    v___x_859_ = lean_int_add(v___x_858_, v_n_836_);
                    lean_dec(v_n_836_);
                    lean_dec(v___x_858_);
                    if v_isShared_840_ == 0 {
                        lean_ctor_set(v___x_839_, 0, v___x_859_);
                        v___x_861_ = v___x_839_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_862_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_862_, 0, v___x_859_);
                        lean_ctor_set(v_reuseFailAlloc_862_, 1, v_k_837_);
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
    mut v_x_866_: *mut LeanObject,
    mut v_y_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_874_: u8 = 0;
    let mut v___x_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_880_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_866_) == 0 {
                    lean_dec(v_y_867_);
                    return v_x_866_;
                } else {
                    if lean_obj_tag(v_y_867_) == 0 {
                        return v_y_867_;
                    } else {
                        v_n_868_ = lean_ctor_get(v_x_866_, 0);
                        v_k_869_ = lean_ctor_get(v_x_866_, 1);
                        v_n_870_ = lean_ctor_get(v_y_867_, 0);
                        v_k_871_ = lean_ctor_get(v_y_867_, 1);
                        v_isSharedCheck_880_ = (!lean_is_exclusive(v_y_867_)) as u8;
                        if v_isSharedCheck_880_ == 0 {
                            v___x_873_ = v_y_867_;
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_871_);
                            lean_inc(v_n_870_);
                            lean_dec(v_y_867_);
                            v___x_873_ = lean_box(0);
                            v_isShared_874_ = v_isSharedCheck_880_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_875_ = lean_int_mul(v_n_868_, v_n_870_);
                lean_dec(v_n_870_);
                v___x_876_ = lean_int_add(v_k_869_, v_k_871_);
                lean_dec(v_k_871_);
                if v_isShared_874_ == 0 {
                    lean_ctor_set(v___x_873_, 1, v___x_876_);
                    lean_ctor_set(v___x_873_, 0, v___x_875_);
                    v___x_878_ = v___x_873_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_879_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_879_, 0, v___x_875_);
                    lean_ctor_set(v_reuseFailAlloc_879_, 1, v___x_876_);
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
    mut v_x_881_: *mut LeanObject,
    mut v_y_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_883_: *mut LeanObject = core::ptr::null_mut();
    v_res_883_ = l_Dyadic_mul(v_x_881_, v_y_882_);
    lean_dec(v_x_881_);
    return v_res_883_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__0() -> *mut LeanObject {
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    v___x_886_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v___x_887_ = l_Dyadic_ofInt(v___x_886_);
    return v___x_887_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__1() -> *mut LeanObject {
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut LeanObject = core::ptr::null_mut();
    v___x_888_ = lean_unsigned_to_nat(1);
    v___x_889_ = lean_nat_to_int(v___x_888_);
    return v___x_889_;
}
pub unsafe fn _init_l_Dyadic_pow___closed__2() -> *mut LeanObject {
    let mut v___x_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut LeanObject = core::ptr::null_mut();
    v___x_890_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1),
        core::ptr::addr_of_mut!(l_Dyadic_pow___closed__1_once),
        _init_l_Dyadic_pow___closed__1,
    );
    v___x_891_ = l_Dyadic_ofInt(v___x_890_);
    return v___x_891_;
}
pub unsafe fn l_Dyadic_pow(
    mut v_x_892_: *mut LeanObject,
    mut v_i_893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_902_: u8 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_892_) == 0 {
                    v___x_894_ = lean_unsigned_to_nat(0);
                    v___x_895_ = lean_nat_dec_eq(v_i_893_, v___x_894_);
                    lean_dec(v_i_893_);
                    if v___x_895_ == 0 {
                        v___x_896_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__0_once),
                            _init_l_Dyadic_pow___closed__0,
                        );
                        return v___x_896_;
                    } else {
                        v___x_897_ = lean_obj_once(
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2),
                            core::ptr::addr_of_mut!(l_Dyadic_pow___closed__2_once),
                            _init_l_Dyadic_pow___closed__2,
                        );
                        return v___x_897_;
                    }
                } else {
                    v_n_898_ = lean_ctor_get(v_x_892_, 0);
                    v_k_899_ = lean_ctor_get(v_x_892_, 1);
                    v_isSharedCheck_909_ = (!lean_is_exclusive(v_x_892_)) as u8;
                    if v_isSharedCheck_909_ == 0 {
                        v___x_901_ = v_x_892_;
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_899_);
                        lean_inc(v_n_898_);
                        lean_dec(v_x_892_);
                        v___x_901_ = lean_box(0);
                        v_isShared_902_ = v_isSharedCheck_909_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_903_ = l_Int_pow(v_n_898_, v_i_893_);
                lean_dec(v_n_898_);
                v___x_904_ = lean_nat_to_int(v_i_893_);
                v___x_905_ = lean_int_mul(v_k_899_, v___x_904_);
                lean_dec(v___x_904_);
                lean_dec(v_k_899_);
                if v_isShared_902_ == 0 {
                    lean_ctor_set(v___x_901_, 1, v___x_905_);
                    lean_ctor_set(v___x_901_, 0, v___x_903_);
                    v___x_907_ = v___x_901_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_903_);
                    lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
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
pub unsafe fn l_Dyadic_neg(mut v_x_912_: *mut LeanObject) -> *mut LeanObject {
    let mut v_n_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_917_: u8 = 0;
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_922_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_912_) == 0 {
                    return v_x_912_;
                } else {
                    v_n_913_ = lean_ctor_get(v_x_912_, 0);
                    v_k_914_ = lean_ctor_get(v_x_912_, 1);
                    v_isSharedCheck_922_ = (!lean_is_exclusive(v_x_912_)) as u8;
                    if v_isSharedCheck_922_ == 0 {
                        v___x_916_ = v_x_912_;
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_914_);
                        lean_inc(v_n_913_);
                        lean_dec(v_x_912_);
                        v___x_916_ = lean_box(0);
                        v_isShared_917_ = v_isSharedCheck_922_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_918_ = lean_int_neg(v_n_913_);
                lean_dec(v_n_913_);
                if v_isShared_917_ == 0 {
                    lean_ctor_set(v___x_916_, 0, v___x_918_);
                    v___x_920_ = v___x_916_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_921_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_921_, 0, v___x_918_);
                    lean_ctor_set(v_reuseFailAlloc_921_, 1, v_k_914_);
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
    mut v_x_925_: *mut LeanObject,
    mut v_y_926_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    v___x_927_ = l_Dyadic_neg(v_y_926_);
    v___x_928_ = l_Dyadic_add(v_x_925_, v___x_927_);
    return v___x_928_;
}
pub unsafe fn l_Dyadic_shiftLeft(
    mut v_x_931_: *mut LeanObject,
    mut v_i_932_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_931_) == 0 {
                    return v_x_931_;
                } else {
                    v_n_933_ = lean_ctor_get(v_x_931_, 0);
                    v_k_934_ = lean_ctor_get(v_x_931_, 1);
                    v_isSharedCheck_942_ = (!lean_is_exclusive(v_x_931_)) as u8;
                    if v_isSharedCheck_942_ == 0 {
                        v___x_936_ = v_x_931_;
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_934_);
                        lean_inc(v_n_933_);
                        lean_dec(v_x_931_);
                        v___x_936_ = lean_box(0);
                        v_isShared_937_ = v_isSharedCheck_942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_938_ = lean_int_sub(v_k_934_, v_i_932_);
                lean_dec(v_k_934_);
                if v_isShared_937_ == 0 {
                    lean_ctor_set(v___x_936_, 1, v___x_938_);
                    v___x_940_ = v___x_936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_941_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_941_, 0, v_n_933_);
                    lean_ctor_set(v_reuseFailAlloc_941_, 1, v___x_938_);
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
    mut v_x_943_: *mut LeanObject,
    mut v_i_944_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_945_: *mut LeanObject = core::ptr::null_mut();
    v_res_945_ = l_Dyadic_shiftLeft(v_x_943_, v_i_944_);
    lean_dec(v_i_944_);
    return v_res_945_;
}
pub unsafe fn l_Dyadic_shiftRight(
    mut v_x_946_: *mut LeanObject,
    mut v_i_947_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_n_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_952_: u8 = 0;
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_946_) == 0 {
                    return v_x_946_;
                } else {
                    v_n_948_ = lean_ctor_get(v_x_946_, 0);
                    v_k_949_ = lean_ctor_get(v_x_946_, 1);
                    v_isSharedCheck_957_ = (!lean_is_exclusive(v_x_946_)) as u8;
                    if v_isSharedCheck_957_ == 0 {
                        v___x_951_ = v_x_946_;
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_949_);
                        lean_inc(v_n_948_);
                        lean_dec(v_x_946_);
                        v___x_951_ = lean_box(0);
                        v_isShared_952_ = v_isSharedCheck_957_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_953_ = lean_int_add(v_k_949_, v_i_947_);
                lean_dec(v_k_949_);
                if v_isShared_952_ == 0 {
                    lean_ctor_set(v___x_951_, 1, v___x_953_);
                    v___x_955_ = v___x_951_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_956_, 0, v_n_948_);
                    lean_ctor_set(v_reuseFailAlloc_956_, 1, v___x_953_);
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
    mut v_x_958_: *mut LeanObject,
    mut v_i_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_960_: *mut LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Dyadic_shiftRight(v_x_958_, v_i_959_);
    lean_dec(v_i_959_);
    return v_res_960_;
}
pub unsafe fn l_Dyadic_instHShiftLeftNat___lam__0(
    mut v_x_965_: *mut LeanObject,
    mut v_y_966_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    v___x_967_ = lean_nat_to_int(v_y_966_);
    v___x_968_ = l_Dyadic_shiftLeft(v_x_965_, v___x_967_);
    lean_dec(v___x_967_);
    return v___x_968_;
}
pub unsafe fn l_Dyadic_instHShiftRightNat___lam__0(
    mut v_x_971_: *mut LeanObject,
    mut v_y_972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    v___x_973_ = lean_nat_to_int(v_y_972_);
    v___x_974_ = l_Dyadic_shiftRight(v_x_971_, v___x_973_);
    lean_dec(v___x_973_);
    return v___x_974_;
}
pub unsafe fn l_Int_cast___at___00Dyadic_toRat_spec__1(
    mut v_a_977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    v___x_978_ = l_Rat_ofInt(v_a_977_);
    return v___x_978_;
}
pub unsafe fn l_Nat_cast___at___00Dyadic_toRat_spec__0(
    mut v_a_979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    v___x_980_ = lean_nat_to_int(v_a_979_);
    v___x_981_ = l_Rat_ofInt(v___x_980_);
    return v___x_981_;
}
pub unsafe fn _init_l_Dyadic_toRat___closed__0() -> *mut LeanObject {
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    v___x_982_ = lean_unsigned_to_nat(0);
    v___x_983_ = l_Nat_cast___at___00Dyadic_toRat_spec__0(v___x_982_);
    return v___x_983_;
}
pub unsafe fn l_Dyadic_toRat(mut v_x_984_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v_intZero_991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_992_: u8 = 0;
    let mut v_a_993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abs_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1008_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_984_) == 0 {
                    v___x_985_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0),
                        core::ptr::addr_of_mut!(l_Dyadic_toRat___closed__0_once),
                        _init_l_Dyadic_toRat___closed__0,
                    );
                    return v___x_985_;
                } else {
                    v_n_986_ = lean_ctor_get(v_x_984_, 0);
                    v_k_987_ = lean_ctor_get(v_x_984_, 1);
                    v_isSharedCheck_1008_ = (!lean_is_exclusive(v_x_984_)) as u8;
                    if v_isSharedCheck_1008_ == 0 {
                        v___x_989_ = v_x_984_;
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_987_);
                        lean_inc(v_n_986_);
                        lean_dec(v_x_984_);
                        v___x_989_ = lean_box(0);
                        v_isShared_990_ = v_isSharedCheck_1008_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_intZero_991_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                    core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                    _init_l_Int_trailingZeros_aux___redArg___closed__1,
                );
                v_isNeg_992_ = lean_int_dec_lt(v_k_987_, v_intZero_991_);
                if v_isNeg_992_ == 0 {
                    v_a_993_ = lean_nat_abs(v_k_987_);
                    lean_dec(v_k_987_);
                    v___x_994_ = lean_unsigned_to_nat(2);
                    v___x_995_ = lean_nat_pow(v___x_994_, v_a_993_);
                    lean_dec(v_a_993_);
                    if v_isShared_990_ == 0 {
                        lean_ctor_set_tag(v___x_989_, 0);
                        lean_ctor_set(v___x_989_, 1, v___x_995_);
                        v___x_997_ = v___x_989_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_998_, 0, v_n_986_);
                        lean_ctor_set(v_reuseFailAlloc_998_, 1, v___x_995_);
                        v___x_997_ = v_reuseFailAlloc_998_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_989_);
                    v_abs_999_ = lean_nat_abs(v_k_987_);
                    lean_dec(v_k_987_);
                    v_one_1000_ = lean_unsigned_to_nat(1);
                    v_a_1001_ = lean_nat_sub(v_abs_999_, v_one_1000_);
                    lean_dec(v_abs_999_);
                    v___x_1002_ = lean_unsigned_to_nat(2);
                    v___x_1003_ = lean_nat_add(v_a_1001_, v_one_1000_);
                    lean_dec(v_a_1001_);
                    v___x_1004_ = lean_nat_pow(v___x_1002_, v___x_1003_);
                    lean_dec(v___x_1003_);
                    v___x_1005_ = lean_nat_to_int(v___x_1004_);
                    v___x_1006_ = lean_int_mul(v_n_986_, v___x_1005_);
                    lean_dec(v___x_1005_);
                    lean_dec(v_n_986_);
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
    mut v_x_1009_: *mut LeanObject,
    mut v_h__1_1010_: *mut LeanObject,
    mut v_h__2_1011_: *mut LeanObject,
    mut v_h__3_1012_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1009_) == 0 {
        let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1014_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1012_);
        lean_dec(v_h__2_1011_);
        v___x_1013_ = lean_box(0);
        v___x_1014_ = lean_apply_1(v_h__1_1010_, v___x_1013_);
        return v___x_1014_;
    } else {
        let mut v_n_1015_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1016_: *mut LeanObject = core::ptr::null_mut();
        let mut v_intZero_1017_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1018_: u8 = 0;
        lean_dec(v_h__1_1010_);
        v_n_1015_ = lean_ctor_get(v_x_1009_, 0);
        lean_inc(v_n_1015_);
        v_k_1016_ = lean_ctor_get(v_x_1009_, 1);
        lean_inc(v_k_1016_);
        lean_dec_ref_known(v_x_1009_, 2);
        v_intZero_1017_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1018_ = lean_int_dec_lt(v_k_1016_, v_intZero_1017_);
        if v_isNeg_1018_ == 0 {
            let mut v_a_1019_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1012_);
            v_a_1019_ = lean_nat_abs(v_k_1016_);
            lean_dec(v_k_1016_);
            v___x_1020_ = lean_apply_3(v_h__2_1011_, v_n_1015_, v_a_1019_, lean_box(0));
            return v___x_1020_;
        } else {
            let mut v_abs_1021_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_1022_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1023_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1011_);
            v_abs_1021_ = lean_nat_abs(v_k_1016_);
            lean_dec(v_k_1016_);
            v_one_1022_ = lean_unsigned_to_nat(1);
            v_a_1023_ = lean_nat_sub(v_abs_1021_, v_one_1022_);
            lean_dec(v_abs_1021_);
            v___x_1024_ = lean_apply_3(v_h__3_1012_, v_n_1015_, v_a_1023_, lean_box(0));
            return v___x_1024_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_toRat_match__1_splitter(
    mut v_motive_1025_: *mut LeanObject,
    mut v_x_1026_: *mut LeanObject,
    mut v_h__1_1027_: *mut LeanObject,
    mut v_h__2_1028_: *mut LeanObject,
    mut v_h__3_1029_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1026_) == 0 {
        let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__3_1029_);
        lean_dec(v_h__2_1028_);
        v___x_1030_ = lean_box(0);
        v___x_1031_ = lean_apply_1(v_h__1_1027_, v___x_1030_);
        return v___x_1031_;
    } else {
        let mut v_n_1032_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1033_: *mut LeanObject = core::ptr::null_mut();
        let mut v_intZero_1034_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1035_: u8 = 0;
        lean_dec(v_h__1_1027_);
        v_n_1032_ = lean_ctor_get(v_x_1026_, 0);
        lean_inc(v_n_1032_);
        v_k_1033_ = lean_ctor_get(v_x_1026_, 1);
        lean_inc(v_k_1033_);
        lean_dec_ref_known(v_x_1026_, 2);
        v_intZero_1034_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1035_ = lean_int_dec_lt(v_k_1033_, v_intZero_1034_);
        if v_isNeg_1035_ == 0 {
            let mut v_a_1036_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1037_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1029_);
            v_a_1036_ = lean_nat_abs(v_k_1033_);
            lean_dec(v_k_1033_);
            v___x_1037_ = lean_apply_3(v_h__2_1028_, v_n_1032_, v_a_1036_, lean_box(0));
            return v___x_1037_;
        } else {
            let mut v_abs_1038_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_1039_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1040_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1028_);
            v_abs_1038_ = lean_nat_abs(v_k_1033_);
            lean_dec(v_k_1033_);
            v_one_1039_ = lean_unsigned_to_nat(1);
            v_a_1040_ = lean_nat_sub(v_abs_1038_, v_one_1039_);
            lean_dec(v_abs_1038_);
            v___x_1041_ = lean_apply_3(v_h__3_1029_, v_n_1032_, v_a_1040_, lean_box(0));
            return v___x_1041_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter___redArg(
    mut v_x_1042_: *mut LeanObject,
    mut v_y_1043_: *mut LeanObject,
    mut v_h__1_1044_: *mut LeanObject,
    mut v_h__2_1045_: *mut LeanObject,
    mut v_h__3_1046_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1052_: u8 = 0;
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1057_: u8 = 0;
    let mut v_n_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1042_) == 0 {
                    lean_dec(v_h__3_1046_);
                    lean_dec(v_h__2_1045_);
                    v___x_1047_ = lean_apply_1(v_h__1_1044_, v_y_1043_);
                    return v___x_1047_;
                } else {
                    lean_dec(v_h__1_1044_);
                    if lean_obj_tag(v_y_1043_) == 0 {
                        lean_dec(v_h__3_1046_);
                        v_n_1048_ = lean_ctor_get(v_x_1042_, 0);
                        v_k_1049_ = lean_ctor_get(v_x_1042_, 1);
                        v_isSharedCheck_1057_ = (!lean_is_exclusive(v_x_1042_)) as u8;
                        if v_isSharedCheck_1057_ == 0 {
                            v___x_1051_ = v_x_1042_;
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_1049_);
                            lean_inc(v_n_1048_);
                            lean_dec(v_x_1042_);
                            v___x_1051_ = lean_box(0);
                            v_isShared_1052_ = v_isSharedCheck_1057_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_h__2_1045_);
                        v_n_1058_ = lean_ctor_get(v_x_1042_, 0);
                        lean_inc(v_n_1058_);
                        v_k_1059_ = lean_ctor_get(v_x_1042_, 1);
                        lean_inc(v_k_1059_);
                        lean_dec_ref_known(v_x_1042_, 2);
                        v_n_1060_ = lean_ctor_get(v_y_1043_, 0);
                        lean_inc(v_n_1060_);
                        v_k_1061_ = lean_ctor_get(v_y_1043_, 1);
                        lean_inc(v_k_1061_);
                        lean_dec_ref_known(v_y_1043_, 2);
                        v___x_1062_ = lean_apply_6(
                            v_h__3_1046_,
                            v_n_1058_,
                            v_k_1059_,
                            lean_box(0),
                            v_n_1060_,
                            v_k_1061_,
                            lean_box(0),
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
                    v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_n_1048_);
                    lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_k_1049_);
                    v___x_1054_ = v_reuseFailAlloc_1056_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1055_ = lean_apply_2(v_h__2_1045_, v___x_1054_, lean_box(0));
                return v___x_1055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__3_splitter(
    mut v_motive_1063_: *mut LeanObject,
    mut v_x_1064_: *mut LeanObject,
    mut v_y_1065_: *mut LeanObject,
    mut v_h__1_1066_: *mut LeanObject,
    mut v_h__2_1067_: *mut LeanObject,
    mut v_h__3_1068_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1074_: u8 = 0;
    let mut v___x_1076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1079_: u8 = 0;
    let mut v_n_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1064_) == 0 {
                    lean_dec(v_h__3_1068_);
                    lean_dec(v_h__2_1067_);
                    v___x_1069_ = lean_apply_1(v_h__1_1066_, v_y_1065_);
                    return v___x_1069_;
                } else {
                    lean_dec(v_h__1_1066_);
                    if lean_obj_tag(v_y_1065_) == 0 {
                        lean_dec(v_h__3_1068_);
                        v_n_1070_ = lean_ctor_get(v_x_1064_, 0);
                        v_k_1071_ = lean_ctor_get(v_x_1064_, 1);
                        v_isSharedCheck_1079_ = (!lean_is_exclusive(v_x_1064_)) as u8;
                        if v_isSharedCheck_1079_ == 0 {
                            v___x_1073_ = v_x_1064_;
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_k_1071_);
                            lean_inc(v_n_1070_);
                            lean_dec(v_x_1064_);
                            v___x_1073_ = lean_box(0);
                            v_isShared_1074_ = v_isSharedCheck_1079_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_h__2_1067_);
                        v_n_1080_ = lean_ctor_get(v_x_1064_, 0);
                        lean_inc(v_n_1080_);
                        v_k_1081_ = lean_ctor_get(v_x_1064_, 1);
                        lean_inc(v_k_1081_);
                        lean_dec_ref_known(v_x_1064_, 2);
                        v_n_1082_ = lean_ctor_get(v_y_1065_, 0);
                        lean_inc(v_n_1082_);
                        v_k_1083_ = lean_ctor_get(v_y_1065_, 1);
                        lean_inc(v_k_1083_);
                        lean_dec_ref_known(v_y_1065_, 2);
                        v___x_1084_ = lean_apply_6(
                            v_h__3_1068_,
                            v_n_1080_,
                            v_k_1081_,
                            lean_box(0),
                            v_n_1082_,
                            v_k_1083_,
                            lean_box(0),
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
                    v_reuseFailAlloc_1078_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1078_, 0, v_n_1070_);
                    lean_ctor_set(v_reuseFailAlloc_1078_, 1, v_k_1071_);
                    v___x_1076_ = v_reuseFailAlloc_1078_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1077_ = lean_apply_2(v_h__2_1067_, v___x_1076_, lean_box(0));
                return v___x_1077_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
    mut v_x_1085_: *mut LeanObject,
    mut v_h__1_1086_: *mut LeanObject,
    mut v_h__2_1087_: *mut LeanObject,
    mut v_h__3_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_1089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1091_: u8 = 0;
    v_natZero_1089_ = lean_unsigned_to_nat(0);
    v_intZero_1090_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1091_ = lean_int_dec_lt(v_x_1085_, v_intZero_1090_);
    if v_isNeg_1091_ == 0 {
        let mut v_a_1092_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1093_: u8 = 0;
        lean_dec(v_h__3_1088_);
        v_a_1092_ = lean_nat_abs(v_x_1085_);
        v_isZero_1093_ = lean_nat_dec_eq(v_a_1092_, v_natZero_1089_);
        if v_isZero_1093_ == 1 {
            let mut v___x_1094_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_1092_);
            lean_dec(v_h__2_1087_);
            v___x_1094_ = lean_box(0);
            v___x_1095_ = lean_apply_1(v_h__1_1086_, v___x_1094_);
            return v___x_1095_;
        } else {
            let mut v_one_1096_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1097_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1086_);
            v_one_1096_ = lean_unsigned_to_nat(1);
            v_n_1097_ = lean_nat_sub(v_a_1092_, v_one_1096_);
            lean_dec(v_a_1092_);
            v___x_1098_ = lean_apply_1(v_h__2_1087_, v_n_1097_);
            return v___x_1098_;
        }
    } else {
        let mut v_abs_1099_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1100_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1101_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1087_);
        lean_dec(v_h__1_1086_);
        v_abs_1099_ = lean_nat_abs(v_x_1085_);
        v_one_1100_ = lean_unsigned_to_nat(1);
        v_a_1101_ = lean_nat_sub(v_abs_1099_, v_one_1100_);
        lean_dec(v_abs_1099_);
        v___x_1102_ = lean_apply_1(v_h__3_1088_, v_a_1101_);
        return v___x_1102_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg___boxed(
    mut v_x_1103_: *mut LeanObject,
    mut v_h__1_1104_: *mut LeanObject,
    mut v_h__2_1105_: *mut LeanObject,
    mut v_h__3_1106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1107_: *mut LeanObject = core::ptr::null_mut();
    v_res_1107_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___redArg(
        v_x_1103_,
        v_h__1_1104_,
        v_h__2_1105_,
        v_h__3_1106_,
    );
    lean_dec(v_x_1103_);
    return v_res_1107_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
    mut v_motive_1108_: *mut LeanObject,
    mut v_x_1109_: *mut LeanObject,
    mut v_h__1_1110_: *mut LeanObject,
    mut v_h__2_1111_: *mut LeanObject,
    mut v_h__3_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1115_: u8 = 0;
    v_natZero_1113_ = lean_unsigned_to_nat(0);
    v_intZero_1114_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1115_ = lean_int_dec_lt(v_x_1109_, v_intZero_1114_);
    if v_isNeg_1115_ == 0 {
        let mut v_a_1116_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isZero_1117_: u8 = 0;
        lean_dec(v_h__3_1112_);
        v_a_1116_ = lean_nat_abs(v_x_1109_);
        v_isZero_1117_ = lean_nat_dec_eq(v_a_1116_, v_natZero_1113_);
        if v_isZero_1117_ == 1 {
            let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_a_1116_);
            lean_dec(v_h__2_1111_);
            v___x_1118_ = lean_box(0);
            v___x_1119_ = lean_apply_1(v_h__1_1110_, v___x_1118_);
            return v___x_1119_;
        } else {
            let mut v_one_1120_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1121_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1122_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1110_);
            v_one_1120_ = lean_unsigned_to_nat(1);
            v_n_1121_ = lean_nat_sub(v_a_1116_, v_one_1120_);
            lean_dec(v_a_1116_);
            v___x_1122_ = lean_apply_1(v_h__2_1111_, v_n_1121_);
            return v___x_1122_;
        }
    } else {
        let mut v_abs_1123_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1124_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1111_);
        lean_dec(v_h__1_1110_);
        v_abs_1123_ = lean_nat_abs(v_x_1109_);
        v_one_1124_ = lean_unsigned_to_nat(1);
        v_a_1125_ = lean_nat_sub(v_abs_1123_, v_one_1124_);
        lean_dec(v_abs_1123_);
        v___x_1126_ = lean_apply_1(v_h__3_1112_, v_a_1125_);
        return v___x_1126_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter___boxed(
    mut v_motive_1127_: *mut LeanObject,
    mut v_x_1128_: *mut LeanObject,
    mut v_h__1_1129_: *mut LeanObject,
    mut v_h__2_1130_: *mut LeanObject,
    mut v_h__3_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1132_: *mut LeanObject = core::ptr::null_mut();
    v_res_1132_ = l___private_Init_Data_Dyadic_Basic_0__Dyadic_add_match__1_splitter(
        v_motive_1127_,
        v_x_1128_,
        v_h__1_1129_,
        v_h__2_1130_,
        v_h__3_1131_,
    );
    lean_dec(v_x_1128_);
    return v_res_1132_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter___redArg(
    mut v_x_1133_: *mut LeanObject,
    mut v_h__1_1134_: *mut LeanObject,
    mut v_h__2_1135_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1133_) == 0 {
        let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1135_);
        v___x_1136_ = lean_box(0);
        v___x_1137_ = lean_apply_1(v_h__1_1134_, v___x_1136_);
        return v___x_1137_;
    } else {
        let mut v_n_1138_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1139_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1134_);
        v_n_1138_ = lean_ctor_get(v_x_1133_, 0);
        lean_inc(v_n_1138_);
        v_k_1139_ = lean_ctor_get(v_x_1133_, 1);
        lean_inc(v_k_1139_);
        lean_dec_ref_known(v_x_1133_, 2);
        v___x_1140_ = lean_apply_3(v_h__2_1135_, v_n_1138_, v_k_1139_, lean_box(0));
        return v___x_1140_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Dyadic_pow_match__1_splitter(
    mut v_motive_1141_: *mut LeanObject,
    mut v_x_1142_: *mut LeanObject,
    mut v_h__1_1143_: *mut LeanObject,
    mut v_h__2_1144_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1142_) == 0 {
        let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1144_);
        v___x_1145_ = lean_box(0);
        v___x_1146_ = lean_apply_1(v_h__1_1143_, v___x_1145_);
        return v___x_1146_;
    } else {
        let mut v_n_1147_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1148_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1143_);
        v_n_1147_ = lean_ctor_get(v_x_1142_, 0);
        lean_inc(v_n_1147_);
        v_k_1148_ = lean_ctor_get(v_x_1142_, 1);
        lean_inc(v_k_1148_);
        lean_dec_ref_known(v_x_1142_, 2);
        v___x_1149_ = lean_apply_3(v_h__2_1144_, v_n_1147_, v_k_1148_, lean_box(0));
        return v___x_1149_;
    }
}
pub unsafe fn l_Dyadic_precision(mut v_x_1150_: *mut LeanObject) -> *mut LeanObject {
    if lean_obj_tag(v_x_1150_) == 0 {
        let mut v___x_1151_: *mut LeanObject = core::ptr::null_mut();
        v___x_1151_ = lean_box(0);
        return v___x_1151_;
    } else {
        let mut v_k_1152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
        v_k_1152_ = lean_ctor_get(v_x_1150_, 1);
        lean_inc(v_k_1152_);
        v___x_1153_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_1153_, 0, v_k_1152_);
        return v___x_1153_;
    }
}
pub unsafe fn l_Dyadic_precision___boxed(mut v_x_1154_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1155_: *mut LeanObject = core::ptr::null_mut();
    v_res_1155_ = l_Dyadic_precision(v_x_1154_);
    lean_dec(v_x_1154_);
    return v_res_1155_;
}
pub unsafe fn l_Rat_toDyadic(
    mut v_x_1156_: *mut LeanObject,
    mut v_prec_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_1158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1159_: u8 = 0;
    v_intZero_1158_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1159_ = lean_int_dec_lt(v_prec_1157_, v_intZero_1158_);
    if v_isNeg_1159_ == 0 {
        let mut v_num_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v_den_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1162_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
        v_num_1160_ = lean_ctor_get(v_x_1156_, 0);
        lean_inc(v_num_1160_);
        v_den_1161_ = lean_ctor_get(v_x_1156_, 1);
        lean_inc(v_den_1161_);
        lean_dec_ref(v_x_1156_);
        v_a_1162_ = lean_nat_abs(v_prec_1157_);
        v___x_1163_ = l_Int_shiftLeft(v_num_1160_, v_a_1162_);
        lean_dec(v_a_1162_);
        lean_dec(v_num_1160_);
        v___x_1164_ = lean_nat_to_int(v_den_1161_);
        v___x_1165_ = lean_int_ediv(v___x_1163_, v___x_1164_);
        lean_dec(v___x_1164_);
        lean_dec(v___x_1163_);
        v___x_1166_ = l_Dyadic_ofIntWithPrec(v___x_1165_, v_prec_1157_);
        return v___x_1166_;
    } else {
        let mut v_num_1167_: *mut LeanObject = core::ptr::null_mut();
        let mut v_den_1168_: *mut LeanObject = core::ptr::null_mut();
        let mut v_abs_1169_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1173_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1176_: *mut LeanObject = core::ptr::null_mut();
        v_num_1167_ = lean_ctor_get(v_x_1156_, 0);
        lean_inc(v_num_1167_);
        v_den_1168_ = lean_ctor_get(v_x_1156_, 1);
        lean_inc(v_den_1168_);
        lean_dec_ref(v_x_1156_);
        v_abs_1169_ = lean_nat_abs(v_prec_1157_);
        v_one_1170_ = lean_unsigned_to_nat(1);
        v_a_1171_ = lean_nat_sub(v_abs_1169_, v_one_1170_);
        lean_dec(v_abs_1169_);
        v___x_1172_ = lean_nat_add(v_a_1171_, v_one_1170_);
        lean_dec(v_a_1171_);
        v___x_1173_ = lean_nat_shiftl(v_den_1168_, v___x_1172_);
        lean_dec(v___x_1172_);
        lean_dec(v_den_1168_);
        v___x_1174_ = lean_nat_to_int(v___x_1173_);
        v___x_1175_ = lean_int_ediv(v_num_1167_, v___x_1174_);
        lean_dec(v___x_1174_);
        lean_dec(v_num_1167_);
        v___x_1176_ = l_Dyadic_ofIntWithPrec(v___x_1175_, v_prec_1157_);
        return v___x_1176_;
    }
}
pub unsafe fn l_Rat_toDyadic___boxed(
    mut v_x_1177_: *mut LeanObject,
    mut v_prec_1178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1179_: *mut LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Rat_toDyadic(v_x_1177_, v_prec_1178_);
    lean_dec(v_prec_1178_);
    return v_res_1179_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
    mut v_prec_1180_: *mut LeanObject,
    mut v_h__1_1181_: *mut LeanObject,
    mut v_h__2_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1184_: u8 = 0;
    v_intZero_1183_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1184_ = lean_int_dec_lt(v_prec_1180_, v_intZero_1183_);
    if v_isNeg_1184_ == 0 {
        let mut v_a_1185_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1186_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1182_);
        v_a_1185_ = lean_nat_abs(v_prec_1180_);
        v___x_1186_ = lean_apply_1(v_h__1_1181_, v_a_1185_);
        return v___x_1186_;
    } else {
        let mut v_abs_1187_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1188_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1189_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1181_);
        v_abs_1187_ = lean_nat_abs(v_prec_1180_);
        v_one_1188_ = lean_unsigned_to_nat(1);
        v_a_1189_ = lean_nat_sub(v_abs_1187_, v_one_1188_);
        lean_dec(v_abs_1187_);
        v___x_1190_ = lean_apply_1(v_h__2_1182_, v_a_1189_);
        return v___x_1190_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg___boxed(
    mut v_prec_1191_: *mut LeanObject,
    mut v_h__1_1192_: *mut LeanObject,
    mut v_h__2_1193_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1194_: *mut LeanObject = core::ptr::null_mut();
    v_res_1194_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___redArg(
        v_prec_1191_,
        v_h__1_1192_,
        v_h__2_1193_,
    );
    lean_dec(v_prec_1191_);
    return v_res_1194_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
    mut v_motive_1195_: *mut LeanObject,
    mut v_prec_1196_: *mut LeanObject,
    mut v_h__1_1197_: *mut LeanObject,
    mut v_h__2_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_intZero_1199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1200_: u8 = 0;
    v_intZero_1199_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
        core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
        _init_l_Int_trailingZeros_aux___redArg___closed__1,
    );
    v_isNeg_1200_ = lean_int_dec_lt(v_prec_1196_, v_intZero_1199_);
    if v_isNeg_1200_ == 0 {
        let mut v_a_1201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1202_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1198_);
        v_a_1201_ = lean_nat_abs(v_prec_1196_);
        v___x_1202_ = lean_apply_1(v_h__1_1197_, v_a_1201_);
        return v___x_1202_;
    } else {
        let mut v_abs_1203_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_1204_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_1205_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1197_);
        v_abs_1203_ = lean_nat_abs(v_prec_1196_);
        v_one_1204_ = lean_unsigned_to_nat(1);
        v_a_1205_ = lean_nat_sub(v_abs_1203_, v_one_1204_);
        lean_dec(v_abs_1203_);
        v___x_1206_ = lean_apply_1(v_h__2_1198_, v_a_1205_);
        return v___x_1206_;
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter___boxed(
    mut v_motive_1207_: *mut LeanObject,
    mut v_prec_1208_: *mut LeanObject,
    mut v_h__1_1209_: *mut LeanObject,
    mut v_h__2_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1211_: *mut LeanObject = core::ptr::null_mut();
    v_res_1211_ = l___private_Init_Data_Dyadic_Basic_0__Rat_toDyadic_match__1_splitter(
        v_motive_1207_,
        v_prec_1208_,
        v_h__1_1209_,
        v_h__2_1210_,
    );
    lean_dec(v_prec_1208_);
    return v_res_1211_;
}
pub unsafe fn l_Dyadic_roundDown(
    mut v_x_1212_: *mut LeanObject,
    mut v_prec_1213_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1212_) == 0 {
        return v_x_1212_;
    } else {
        let mut v_n_1214_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1215_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v_intZero_1217_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1218_: u8 = 0;
        v_n_1214_ = lean_ctor_get(v_x_1212_, 0);
        v_k_1215_ = lean_ctor_get(v_x_1212_, 1);
        v___x_1216_ = lean_int_sub(v_k_1215_, v_prec_1213_);
        v_intZero_1217_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1218_ = lean_int_dec_lt(v___x_1216_, v_intZero_1217_);
        if v_isNeg_1218_ == 0 {
            let mut v_a_1219_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1220_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
            v_a_1219_ = lean_nat_abs(v___x_1216_);
            lean_dec(v___x_1216_);
            v___x_1220_ = l_Int_shiftRight(v_n_1214_, v_a_1219_);
            lean_dec(v_a_1219_);
            v___x_1221_ = l_Dyadic_ofIntWithPrec(v___x_1220_, v_prec_1213_);
            return v___x_1221_;
        } else {
            lean_dec(v___x_1216_);
            lean_inc_ref(v_x_1212_);
            return v_x_1212_;
        }
    }
}
pub unsafe fn l_Dyadic_roundDown___boxed(
    mut v_x_1222_: *mut LeanObject,
    mut v_prec_1223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1224_: *mut LeanObject = core::ptr::null_mut();
    v_res_1224_ = l_Dyadic_roundDown(v_x_1222_, v_prec_1223_);
    lean_dec(v_prec_1223_);
    lean_dec(v_x_1222_);
    return v_res_1224_;
}
pub unsafe fn l_Dyadic_blt(mut v_x_1225_: *mut LeanObject, mut v_y_1226_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1225_) == 0 {
        if lean_obj_tag(v_y_1226_) == 0 {
            let mut v___x_1227_: u8 = 0;
            v___x_1227_ = 0;
            return v___x_1227_;
        } else {
            let mut v_n_1228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1230_: u8 = 0;
            v_n_1228_ = lean_ctor_get(v_y_1226_, 0);
            v___x_1229_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1230_ = lean_int_dec_lt(v___x_1229_, v_n_1228_);
            return v___x_1230_;
        }
    } else {
        if lean_obj_tag(v_y_1226_) == 0 {
            let mut v_n_1231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1233_: u8 = 0;
            v_n_1231_ = lean_ctor_get(v_x_1225_, 0);
            v___x_1232_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1233_ = lean_int_dec_lt(v_n_1231_, v___x_1232_);
            return v___x_1233_;
        } else {
            let mut v_n_1234_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1235_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1236_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1237_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
            let mut v_intZero_1239_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1240_: u8 = 0;
            v_n_1234_ = lean_ctor_get(v_x_1225_, 0);
            v_k_1235_ = lean_ctor_get(v_x_1225_, 1);
            v_n_1236_ = lean_ctor_get(v_y_1226_, 0);
            v_k_1237_ = lean_ctor_get(v_y_1226_, 1);
            v___x_1238_ = lean_int_sub(v_k_1237_, v_k_1235_);
            v_intZero_1239_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1240_ = lean_int_dec_lt(v___x_1238_, v_intZero_1239_);
            if v_isNeg_1240_ == 0 {
                let mut v_a_1241_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1242_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1243_: u8 = 0;
                v_a_1241_ = lean_nat_abs(v___x_1238_);
                lean_dec(v___x_1238_);
                v___x_1242_ = l_Int_shiftLeft(v_n_1234_, v_a_1241_);
                lean_dec(v_a_1241_);
                v___x_1243_ = lean_int_dec_lt(v___x_1242_, v_n_1236_);
                lean_dec(v___x_1242_);
                return v___x_1243_;
            } else {
                let mut v_abs_1244_: *mut LeanObject = core::ptr::null_mut();
                let mut v_one_1245_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_1246_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1247_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1249_: u8 = 0;
                v_abs_1244_ = lean_nat_abs(v___x_1238_);
                lean_dec(v___x_1238_);
                v_one_1245_ = lean_unsigned_to_nat(1);
                v_a_1246_ = lean_nat_sub(v_abs_1244_, v_one_1245_);
                lean_dec(v_abs_1244_);
                v___x_1247_ = lean_nat_add(v_a_1246_, v_one_1245_);
                lean_dec(v_a_1246_);
                v___x_1248_ = l_Int_shiftLeft(v_n_1236_, v___x_1247_);
                lean_dec(v___x_1247_);
                v___x_1249_ = lean_int_dec_lt(v_n_1234_, v___x_1248_);
                lean_dec(v___x_1248_);
                return v___x_1249_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_blt___boxed(
    mut v_x_1250_: *mut LeanObject,
    mut v_y_1251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1252_: u8 = 0;
    let mut v_r_1253_: *mut LeanObject = core::ptr::null_mut();
    v_res_1252_ = l_Dyadic_blt(v_x_1250_, v_y_1251_);
    lean_dec(v_y_1251_);
    lean_dec(v_x_1250_);
    v_r_1253_ = lean_box((v_res_1252_) as usize);
    return v_r_1253_;
}
pub unsafe fn l_Dyadic_ble(mut v_x_1254_: *mut LeanObject, mut v_y_1255_: *mut LeanObject) -> u8 {
    if lean_obj_tag(v_x_1254_) == 0 {
        if lean_obj_tag(v_y_1255_) == 0 {
            let mut v___x_1256_: u8 = 0;
            v___x_1256_ = 1;
            return v___x_1256_;
        } else {
            let mut v_n_1257_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1259_: u8 = 0;
            v_n_1257_ = lean_ctor_get(v_y_1255_, 0);
            v___x_1258_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1259_ = lean_int_dec_le(v___x_1258_, v_n_1257_);
            return v___x_1259_;
        }
    } else {
        if lean_obj_tag(v_y_1255_) == 0 {
            let mut v_n_1260_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: u8 = 0;
            v_n_1260_ = lean_ctor_get(v_x_1254_, 0);
            v___x_1261_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v___x_1262_ = lean_int_dec_le(v_n_1260_, v___x_1261_);
            return v___x_1262_;
        } else {
            let mut v_n_1263_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1264_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1265_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1266_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut LeanObject = core::ptr::null_mut();
            let mut v_intZero_1268_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isNeg_1269_: u8 = 0;
            v_n_1263_ = lean_ctor_get(v_x_1254_, 0);
            v_k_1264_ = lean_ctor_get(v_x_1254_, 1);
            v_n_1265_ = lean_ctor_get(v_y_1255_, 0);
            v_k_1266_ = lean_ctor_get(v_y_1255_, 1);
            v___x_1267_ = lean_int_sub(v_k_1266_, v_k_1264_);
            v_intZero_1268_ = lean_obj_once(
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
                core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
                _init_l_Int_trailingZeros_aux___redArg___closed__1,
            );
            v_isNeg_1269_ = lean_int_dec_lt(v___x_1267_, v_intZero_1268_);
            if v_isNeg_1269_ == 0 {
                let mut v_a_1270_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1271_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1272_: u8 = 0;
                v_a_1270_ = lean_nat_abs(v___x_1267_);
                lean_dec(v___x_1267_);
                v___x_1271_ = l_Int_shiftLeft(v_n_1263_, v_a_1270_);
                lean_dec(v_a_1270_);
                v___x_1272_ = lean_int_dec_le(v___x_1271_, v_n_1265_);
                lean_dec(v___x_1271_);
                return v___x_1272_;
            } else {
                let mut v_abs_1273_: *mut LeanObject = core::ptr::null_mut();
                let mut v_one_1274_: *mut LeanObject = core::ptr::null_mut();
                let mut v_a_1275_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1276_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_1278_: u8 = 0;
                v_abs_1273_ = lean_nat_abs(v___x_1267_);
                lean_dec(v___x_1267_);
                v_one_1274_ = lean_unsigned_to_nat(1);
                v_a_1275_ = lean_nat_sub(v_abs_1273_, v_one_1274_);
                lean_dec(v_abs_1273_);
                v___x_1276_ = lean_nat_add(v_a_1275_, v_one_1274_);
                lean_dec(v_a_1275_);
                v___x_1277_ = l_Int_shiftLeft(v_n_1265_, v___x_1276_);
                lean_dec(v___x_1276_);
                v___x_1278_ = lean_int_dec_le(v_n_1263_, v___x_1277_);
                lean_dec(v___x_1277_);
                return v___x_1278_;
            }
        }
    }
}
pub unsafe fn l_Dyadic_ble___boxed(
    mut v_x_1279_: *mut LeanObject,
    mut v_y_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1281_: u8 = 0;
    let mut v_r_1282_: *mut LeanObject = core::ptr::null_mut();
    v_res_1281_ = l_Dyadic_ble(v_x_1279_, v_y_1280_);
    lean_dec(v_y_1280_);
    lean_dec(v_x_1279_);
    v_r_1282_ = lean_box((v_res_1281_) as usize);
    return v_r_1282_;
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter___redArg(
    mut v_x_1283_: *mut LeanObject,
    mut v_x_1284_: *mut LeanObject,
    mut v_h__1_1285_: *mut LeanObject,
    mut v_h__2_1286_: *mut LeanObject,
    mut v_h__3_1287_: *mut LeanObject,
    mut v_h__4_1288_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1283_) == 0 {
        lean_dec(v_h__4_1288_);
        lean_dec(v_h__3_1287_);
        if lean_obj_tag(v_x_1284_) == 0 {
            let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1286_);
            v___x_1289_ = lean_box(0);
            v___x_1290_ = lean_apply_1(v_h__1_1285_, v___x_1289_);
            return v___x_1290_;
        } else {
            let mut v_n_1291_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1292_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1285_);
            v_n_1291_ = lean_ctor_get(v_x_1284_, 0);
            lean_inc(v_n_1291_);
            v_k_1292_ = lean_ctor_get(v_x_1284_, 1);
            lean_inc(v_k_1292_);
            lean_dec_ref_known(v_x_1284_, 2);
            v___x_1293_ = lean_apply_3(v_h__2_1286_, v_n_1291_, v_k_1292_, lean_box(0));
            return v___x_1293_;
        }
    } else {
        lean_dec(v_h__2_1286_);
        lean_dec(v_h__1_1285_);
        if lean_obj_tag(v_x_1284_) == 0 {
            let mut v_n_1294_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1295_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1288_);
            v_n_1294_ = lean_ctor_get(v_x_1283_, 0);
            lean_inc(v_n_1294_);
            v_k_1295_ = lean_ctor_get(v_x_1283_, 1);
            lean_inc(v_k_1295_);
            lean_dec_ref_known(v_x_1283_, 2);
            v___x_1296_ = lean_apply_3(v_h__3_1287_, v_n_1294_, v_k_1295_, lean_box(0));
            return v___x_1296_;
        } else {
            let mut v_n_1297_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1298_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1299_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1300_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1287_);
            v_n_1297_ = lean_ctor_get(v_x_1283_, 0);
            lean_inc(v_n_1297_);
            v_k_1298_ = lean_ctor_get(v_x_1283_, 1);
            lean_inc(v_k_1298_);
            lean_dec_ref_known(v_x_1283_, 2);
            v_n_1299_ = lean_ctor_get(v_x_1284_, 0);
            lean_inc(v_n_1299_);
            v_k_1300_ = lean_ctor_get(v_x_1284_, 1);
            lean_inc(v_k_1300_);
            lean_dec_ref_known(v_x_1284_, 2);
            v___x_1301_ = lean_apply_6(
                v_h__4_1288_,
                v_n_1297_,
                v_k_1298_,
                lean_box(0),
                v_n_1299_,
                v_k_1300_,
                lean_box(0),
            );
            return v___x_1301_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Dyadic_Basic_0__instDecidableEqDyadic_decEq_match__1_splitter(
    mut v_motive_1302_: *mut LeanObject,
    mut v_x_1303_: *mut LeanObject,
    mut v_x_1304_: *mut LeanObject,
    mut v_h__1_1305_: *mut LeanObject,
    mut v_h__2_1306_: *mut LeanObject,
    mut v_h__3_1307_: *mut LeanObject,
    mut v_h__4_1308_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1303_) == 0 {
        lean_dec(v_h__4_1308_);
        lean_dec(v_h__3_1307_);
        if lean_obj_tag(v_x_1304_) == 0 {
            let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1310_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1306_);
            v___x_1309_ = lean_box(0);
            v___x_1310_ = lean_apply_1(v_h__1_1305_, v___x_1309_);
            return v___x_1310_;
        } else {
            let mut v_n_1311_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1312_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1313_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_1305_);
            v_n_1311_ = lean_ctor_get(v_x_1304_, 0);
            lean_inc(v_n_1311_);
            v_k_1312_ = lean_ctor_get(v_x_1304_, 1);
            lean_inc(v_k_1312_);
            lean_dec_ref_known(v_x_1304_, 2);
            v___x_1313_ = lean_apply_3(v_h__2_1306_, v_n_1311_, v_k_1312_, lean_box(0));
            return v___x_1313_;
        }
    } else {
        lean_dec(v_h__2_1306_);
        lean_dec(v_h__1_1305_);
        if lean_obj_tag(v_x_1304_) == 0 {
            let mut v_n_1314_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1315_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1316_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_1308_);
            v_n_1314_ = lean_ctor_get(v_x_1303_, 0);
            lean_inc(v_n_1314_);
            v_k_1315_ = lean_ctor_get(v_x_1303_, 1);
            lean_inc(v_k_1315_);
            lean_dec_ref_known(v_x_1303_, 2);
            v___x_1316_ = lean_apply_3(v_h__3_1307_, v_n_1314_, v_k_1315_, lean_box(0));
            return v___x_1316_;
        } else {
            let mut v_n_1317_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1318_: *mut LeanObject = core::ptr::null_mut();
            let mut v_n_1319_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1320_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1307_);
            v_n_1317_ = lean_ctor_get(v_x_1303_, 0);
            lean_inc(v_n_1317_);
            v_k_1318_ = lean_ctor_get(v_x_1303_, 1);
            lean_inc(v_k_1318_);
            lean_dec_ref_known(v_x_1303_, 2);
            v_n_1319_ = lean_ctor_get(v_x_1304_, 0);
            lean_inc(v_n_1319_);
            v_k_1320_ = lean_ctor_get(v_x_1304_, 1);
            lean_inc(v_k_1320_);
            lean_dec_ref_known(v_x_1304_, 2);
            v___x_1321_ = lean_apply_6(
                v_h__4_1308_,
                v_n_1317_,
                v_k_1318_,
                lean_box(0),
                v_n_1319_,
                v_k_1320_,
                lean_box(0),
            );
            return v___x_1321_;
        }
    }
}
pub unsafe fn _init_l_Dyadic_instLT() -> *mut LeanObject {
    let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
    v___x_1322_ = lean_box(0);
    return v___x_1322_;
}
pub unsafe fn _init_l_Dyadic_instLE() -> *mut LeanObject {
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v___x_1323_ = lean_box(0);
    return v___x_1323_;
}
pub unsafe fn l_Dyadic_instDecidableLT(
    mut v_x_1324_: *mut LeanObject,
    mut v_x_1325_: *mut LeanObject,
) -> u8 {
    let mut v___x_1326_: u8 = 0;
    v___x_1326_ = l_Dyadic_blt(v_x_1324_, v_x_1325_);
    return v___x_1326_;
}
pub unsafe fn l_Dyadic_instDecidableLT___boxed(
    mut v_x_1327_: *mut LeanObject,
    mut v_x_1328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1329_: u8 = 0;
    let mut v_r_1330_: *mut LeanObject = core::ptr::null_mut();
    v_res_1329_ = l_Dyadic_instDecidableLT(v_x_1327_, v_x_1328_);
    lean_dec(v_x_1328_);
    lean_dec(v_x_1327_);
    v_r_1330_ = lean_box((v_res_1329_) as usize);
    return v_r_1330_;
}
pub unsafe fn l_Dyadic_instDecidableLE(
    mut v_x_1331_: *mut LeanObject,
    mut v_x_1332_: *mut LeanObject,
) -> u8 {
    let mut v___x_1333_: u8 = 0;
    v___x_1333_ = l_Dyadic_ble(v_x_1331_, v_x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Dyadic_instDecidableLE___boxed(
    mut v_x_1334_: *mut LeanObject,
    mut v_x_1335_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1336_: u8 = 0;
    let mut v_r_1337_: *mut LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_Dyadic_instDecidableLE(v_x_1334_, v_x_1335_);
    lean_dec(v_x_1335_);
    lean_dec(v_x_1334_);
    v_r_1337_ = lean_box((v_res_1336_) as usize);
    return v_r_1337_;
}
pub unsafe fn l_Dyadic_roundUp(
    mut v_x_1338_: *mut LeanObject,
    mut v_prec_1339_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1338_) == 0 {
        return v_x_1338_;
    } else {
        let mut v_n_1340_: *mut LeanObject = core::ptr::null_mut();
        let mut v_k_1341_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1342_: *mut LeanObject = core::ptr::null_mut();
        let mut v_intZero_1343_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1344_: u8 = 0;
        v_n_1340_ = lean_ctor_get(v_x_1338_, 0);
        v_k_1341_ = lean_ctor_get(v_x_1338_, 1);
        v___x_1342_ = lean_int_sub(v_k_1341_, v_prec_1339_);
        v_intZero_1343_ = lean_obj_once(
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1),
            core::ptr::addr_of_mut!(l_Int_trailingZeros_aux___redArg___closed__1_once),
            _init_l_Int_trailingZeros_aux___redArg___closed__1,
        );
        v_isNeg_1344_ = lean_int_dec_lt(v___x_1342_, v_intZero_1343_);
        if v_isNeg_1344_ == 0 {
            let mut v_a_1345_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1347_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1349_: *mut LeanObject = core::ptr::null_mut();
            v_a_1345_ = lean_nat_abs(v___x_1342_);
            lean_dec(v___x_1342_);
            v___x_1346_ = lean_int_neg(v_n_1340_);
            v___x_1347_ = l_Int_shiftRight(v___x_1346_, v_a_1345_);
            lean_dec(v_a_1345_);
            lean_dec(v___x_1346_);
            v___x_1348_ = lean_int_neg(v___x_1347_);
            lean_dec(v___x_1347_);
            v___x_1349_ = l_Dyadic_ofIntWithPrec(v___x_1348_, v_prec_1339_);
            return v___x_1349_;
        } else {
            lean_dec(v___x_1342_);
            lean_inc_ref(v_x_1338_);
            return v_x_1338_;
        }
    }
}
pub unsafe fn l_Dyadic_roundUp___boxed(
    mut v_x_1350_: *mut LeanObject,
    mut v_prec_1351_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1352_: *mut LeanObject = core::ptr::null_mut();
    v_res_1352_ = l_Dyadic_roundUp(v_x_1350_, v_prec_1351_);
    lean_dec(v_prec_1351_);
    lean_dec(v_x_1350_);
    return v_res_1352_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Dyadic_instLT = _init_l_Dyadic_instLT();
    lean_mark_persistent(l_Dyadic_instLT);
    l_Dyadic_instLE = _init_l_Dyadic_instLE();
    lean_mark_persistent(l_Dyadic_instLE);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Dyadic_Basic(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Bitwise_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Bitwise_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Classes(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Rat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Dyadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Dyadic_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Dyadic_Basic(builtin);
}

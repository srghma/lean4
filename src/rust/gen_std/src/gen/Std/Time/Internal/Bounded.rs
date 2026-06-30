// Lean compiler output
// Module: Std.Time.Internal.Bounded
// Imports: Init.Data.Int.DivMod.Lemmas Init.Data.Order.Ord Init.Data.Int.Repr Init.Omega Init.Ext
use crate::ffi::{
    lean_int_add, lean_int_dec_eq, lean_int_dec_le, lean_int_dec_lt, lean_int_ediv, lean_int_emod,
    lean_int_mod, lean_int_mul, lean_int_neg, lean_int_sub, lean_nat_abs, lean_nat_dec_le,
    lean_nat_sub, lean_nat_to_int,
};
use crate::r#gen::Init::Data::Int::Basic::l_Int_toNat;
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Repr::{
    initialize_Init_Data_Int_Repr, l_Int_repr, runtime_initialize_Init_Data_Int_Repr,
};
use crate::r#gen::Init::Data::Ord::Basic::{l_compareOn___boxed, l_instOrdInt___lam__0___boxed};
use crate::r#gen::Init::Data::Order::Ord::{
    initialize_Init_Data_Order_Ord, runtime_initialize_Init_Data_Order_Ord,
};
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Ext::{initialize_Init_Ext, runtime_initialize_Init_Ext};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub static l_Std_Time_Internal_Bounded_instOrd___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Internal_Bounded_instOrd___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instOrd___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Internal_Bounded_instOrd___closed__1_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instOrdInt___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Internal_Bounded_instOrd___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instOrd___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_Time_Internal_Bounded_instOrd___closed__2_value: leanh::LeanClosureObject<
    4,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 4) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_compareOn___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 4,
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instOrd___closed__1_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instOrd___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Std_Time_Internal_Bounded_instOrd___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instOrd___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Internal_Bounded_instRepr___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_Time_Internal_Bounded_instRepr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_Time_Internal_Bounded_instRepr___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_Time_Internal_Bounded_instLE(
    mut v_rel_843_: *mut leanh::LeanObject,
    mut v_n_844_: *mut leanh::LeanObject,
    mut v_m_845_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_846_ = leanh::lean_box(0);
    return v___x_846_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instLE___boxed(
    mut v_rel_847_: *mut leanh::LeanObject,
    mut v_n_848_: *mut leanh::LeanObject,
    mut v_m_849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_850_ = l_Std_Time_Internal_Bounded_instLE(v_rel_847_, v_n_848_, v_m_849_);
    leanh::lean_dec(v_m_849_);
    leanh::lean_dec(v_n_848_);
    return v_res_850_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instLT(
    mut v_rel_851_: *mut leanh::LeanObject,
    mut v_n_852_: *mut leanh::LeanObject,
    mut v_m_853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_854_ = leanh::lean_box(0);
    return v___x_854_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instLT___boxed(
    mut v_rel_855_: *mut leanh::LeanObject,
    mut v_n_856_: *mut leanh::LeanObject,
    mut v_m_857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_858_ = l_Std_Time_Internal_Bounded_instLT(v_rel_855_, v_n_856_, v_m_857_);
    leanh::lean_dec(v_m_857_);
    leanh::lean_dec(v_n_856_);
    return v_res_858_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instOrd___lam__0(
    mut v_x_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_x_859_);
    return v_x_859_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instOrd___lam__0___boxed(
    mut v_x_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Std_Time_Internal_Bounded_instOrd___lam__0(v_x_860_);
    leanh::lean_dec(v_x_860_);
    return v_res_861_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instOrd(
    mut v_rel_867_: *mut leanh::LeanObject,
    mut v_n_868_: *mut leanh::LeanObject,
    mut v_m_869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Std_Time_Internal_Bounded_instOrd___closed__2;
    return v___x_870_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instOrd___boxed(
    mut v_rel_871_: *mut leanh::LeanObject,
    mut v_n_872_: *mut leanh::LeanObject,
    mut v_m_873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_874_ = l_Std_Time_Internal_Bounded_instOrd(v_rel_871_, v_n_872_, v_m_873_);
    leanh::lean_dec(v_m_873_);
    leanh::lean_dec(v_n_872_);
    return v_res_874_;
}
pub unsafe fn _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_875_ = leanh::lean_unsigned_to_nat(0);
    v___x_876_ = lean_nat_to_int(v___x_875_);
    return v___x_876_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instRepr___lam__0(
    mut v_n_877_: *mut leanh::LeanObject,
    mut v___y_878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: u8 = 0;
    v___x_879_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once),
        _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0,
    );
    v___x_880_ = lean_int_dec_lt(v_n_877_, v___x_879_);
    if v___x_880_ == 0 {
        let mut v___x_881_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_882_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_881_ = l_Int_repr(v_n_877_);
        v___x_882_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_882_, 0, v___x_881_);
        return v___x_882_;
    } else {
        let mut v___x_883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_883_ = l_Int_repr(v_n_877_);
        v___x_884_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_884_, 0, v___x_883_);
        v___x_885_ = l_Repr_addAppParen(v___x_884_, v___y_878_);
        return v___x_885_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_instRepr___lam__0___boxed(
    mut v_n_886_: *mut leanh::LeanObject,
    mut v___y_887_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_888_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_888_ = l_Std_Time_Internal_Bounded_instRepr___lam__0(v_n_886_, v___y_887_);
    leanh::lean_dec(v___y_887_);
    leanh::lean_dec(v_n_886_);
    return v_res_888_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instRepr(
    mut v_rel_890_: *mut leanh::LeanObject,
    mut v_m_891_: *mut leanh::LeanObject,
    mut v_n_892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_893_ = l_Std_Time_Internal_Bounded_instRepr___closed__0;
    return v___f_893_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instRepr___boxed(
    mut v_rel_894_: *mut leanh::LeanObject,
    mut v_m_895_: *mut leanh::LeanObject,
    mut v_n_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_897_ = l_Std_Time_Internal_Bounded_instRepr(v_rel_894_, v_m_895_, v_n_896_);
    leanh::lean_dec(v_n_896_);
    leanh::lean_dec(v_m_895_);
    return v_res_897_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableEq___redArg(
    mut v_a_898_: *mut leanh::LeanObject,
    mut v_b_899_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_900_: u8 = 0;
    v___x_900_ = lean_int_dec_eq(v_a_898_, v_b_899_);
    return v___x_900_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableEq___redArg___boxed(
    mut v_a_901_: *mut leanh::LeanObject,
    mut v_b_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_903_: u8 = 0;
    let mut v_r_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_903_ = l_Std_Time_Internal_Bounded_instDecidableEq___redArg(v_a_901_, v_b_902_);
    leanh::lean_dec(v_b_902_);
    leanh::lean_dec(v_a_901_);
    v_r_904_ = leanh::lean_box((v_res_903_) as usize);
    return v_r_904_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableEq(
    mut v_rel_905_: *mut leanh::LeanObject,
    mut v_n_906_: *mut leanh::LeanObject,
    mut v_m_907_: *mut leanh::LeanObject,
    mut v_a_908_: *mut leanh::LeanObject,
    mut v_b_909_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_910_: u8 = 0;
    v___x_910_ = lean_int_dec_eq(v_a_908_, v_b_909_);
    return v___x_910_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableEq___boxed(
    mut v_rel_911_: *mut leanh::LeanObject,
    mut v_n_912_: *mut leanh::LeanObject,
    mut v_m_913_: *mut leanh::LeanObject,
    mut v_a_914_: *mut leanh::LeanObject,
    mut v_b_915_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_916_: u8 = 0;
    let mut v_r_917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_Std_Time_Internal_Bounded_instDecidableEq(
        v_rel_911_, v_n_912_, v_m_913_, v_a_914_, v_b_915_,
    );
    leanh::lean_dec(v_b_915_);
    leanh::lean_dec(v_a_914_);
    leanh::lean_dec(v_m_913_);
    leanh::lean_dec(v_n_912_);
    v_r_917_ = leanh::lean_box((v_res_916_) as usize);
    return v_r_917_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableLe___redArg(
    mut v_x_918_: *mut leanh::LeanObject,
    mut v_y_919_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_920_: u8 = 0;
    v___x_920_ = lean_int_dec_le(v_x_918_, v_y_919_);
    return v___x_920_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableLe___redArg___boxed(
    mut v_x_921_: *mut leanh::LeanObject,
    mut v_y_922_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_923_: u8 = 0;
    let mut v_r_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_923_ = l_Std_Time_Internal_Bounded_instDecidableLe___redArg(v_x_921_, v_y_922_);
    leanh::lean_dec(v_y_922_);
    leanh::lean_dec(v_x_921_);
    v_r_924_ = leanh::lean_box((v_res_923_) as usize);
    return v_r_924_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableLe(
    mut v_rel_925_: *mut leanh::LeanObject,
    mut v_a_926_: *mut leanh::LeanObject,
    mut v_b_927_: *mut leanh::LeanObject,
    mut v_x_928_: *mut leanh::LeanObject,
    mut v_y_929_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_930_: u8 = 0;
    v___x_930_ = lean_int_dec_le(v_x_928_, v_y_929_);
    return v___x_930_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_instDecidableLe___boxed(
    mut v_rel_931_: *mut leanh::LeanObject,
    mut v_a_932_: *mut leanh::LeanObject,
    mut v_b_933_: *mut leanh::LeanObject,
    mut v_x_934_: *mut leanh::LeanObject,
    mut v_y_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_936_: u8 = 0;
    let mut v_r_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_936_ = l_Std_Time_Internal_Bounded_instDecidableLe(
        v_rel_931_, v_a_932_, v_b_933_, v_x_934_, v_y_935_,
    );
    leanh::lean_dec(v_y_935_);
    leanh::lean_dec(v_x_934_);
    leanh::lean_dec(v_b_933_);
    leanh::lean_dec(v_a_932_);
    v_r_937_ = leanh::lean_box((v_res_936_) as usize);
    return v_r_937_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_cast___redArg(
    mut v_b_938_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_b_938_);
    return v_b_938_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_cast___redArg___boxed(
    mut v_b_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_940_ = l_Std_Time_Internal_Bounded_cast___redArg(v_b_939_);
    leanh::lean_dec(v_b_939_);
    return v_res_940_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_cast(
    mut v_rel_941_: *mut leanh::LeanObject,
    mut v_lo_u2081_942_: *mut leanh::LeanObject,
    mut v_lo_u2082_943_: *mut leanh::LeanObject,
    mut v_hi_u2081_944_: *mut leanh::LeanObject,
    mut v_hi_u2082_945_: *mut leanh::LeanObject,
    mut v_h_u2081_946_: *mut leanh::LeanObject,
    mut v_h_u2082_947_: *mut leanh::LeanObject,
    mut v_b_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_b_948_);
    return v_b_948_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_cast___boxed(
    mut v_rel_949_: *mut leanh::LeanObject,
    mut v_lo_u2081_950_: *mut leanh::LeanObject,
    mut v_lo_u2082_951_: *mut leanh::LeanObject,
    mut v_hi_u2081_952_: *mut leanh::LeanObject,
    mut v_hi_u2082_953_: *mut leanh::LeanObject,
    mut v_h_u2081_954_: *mut leanh::LeanObject,
    mut v_h_u2082_955_: *mut leanh::LeanObject,
    mut v_b_956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_957_ = l_Std_Time_Internal_Bounded_cast(
        v_rel_949_,
        v_lo_u2081_950_,
        v_lo_u2082_951_,
        v_hi_u2081_952_,
        v_hi_u2082_953_,
        v_h_u2081_954_,
        v_h_u2082_955_,
        v_b_956_,
    );
    leanh::lean_dec(v_b_956_);
    leanh::lean_dec(v_hi_u2082_953_);
    leanh::lean_dec(v_hi_u2081_952_);
    leanh::lean_dec(v_lo_u2082_951_);
    leanh::lean_dec(v_lo_u2081_950_);
    return v_res_957_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_mk___redArg(
    mut v_val_958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_958_);
    return v_val_958_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_mk___redArg___boxed(
    mut v_val_959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_960_ = l_Std_Time_Internal_Bounded_mk___redArg(v_val_959_);
    leanh::lean_dec(v_val_959_);
    return v_res_960_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_mk(
    mut v_lo_961_: *mut leanh::LeanObject,
    mut v_hi_962_: *mut leanh::LeanObject,
    mut v_rel_963_: *mut leanh::LeanObject,
    mut v_val_964_: *mut leanh::LeanObject,
    mut v_proof_965_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_964_);
    return v_val_964_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_mk___boxed(
    mut v_lo_966_: *mut leanh::LeanObject,
    mut v_hi_967_: *mut leanh::LeanObject,
    mut v_rel_968_: *mut leanh::LeanObject,
    mut v_val_969_: *mut leanh::LeanObject,
    mut v_proof_970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_971_ =
        l_Std_Time_Internal_Bounded_mk(v_lo_966_, v_hi_967_, v_rel_968_, v_val_969_, v_proof_970_);
    leanh::lean_dec(v_val_969_);
    leanh::lean_dec(v_hi_967_);
    leanh::lean_dec(v_lo_966_);
    return v_res_971_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_ofInt_x3f___redArg(
    mut v_lo_972_: *mut leanh::LeanObject,
    mut v_hi_973_: *mut leanh::LeanObject,
    mut v_inst_974_: *mut leanh::LeanObject,
    mut v_val_975_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: u8 = 0;
    leanh::lean_inc_ref(v_inst_974_);
    leanh::lean_inc_n(v_val_975_, 2);
    v___x_976_ = leanh::lean_apply_2(v_inst_974_, v_val_975_, v_hi_973_);
    v___x_977_ = leanh::lean_apply_2(v_inst_974_, v_lo_972_, v_val_975_);
    v___x_978_ = (leanh::lean_unbox(v___x_977_) as u8);
    if v___x_978_ == 0 {
        let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_val_975_);
        v___x_979_ = leanh::lean_box(0);
        return v___x_979_;
    } else {
        let mut v___x_980_: u8 = 0;
        v___x_980_ = (leanh::lean_unbox(v___x_976_) as u8);
        if v___x_980_ == 0 {
            let mut v___x_981_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_975_);
            v___x_981_ = leanh::lean_box(0);
            return v___x_981_;
        } else {
            let mut v___x_982_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_982_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_982_, 0, v_val_975_);
            return v___x_982_;
        }
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_ofInt_x3f(
    mut v_rel_983_: *mut leanh::LeanObject,
    mut v_lo_984_: *mut leanh::LeanObject,
    mut v_hi_985_: *mut leanh::LeanObject,
    mut v_inst_986_: *mut leanh::LeanObject,
    mut v_val_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: u8 = 0;
    leanh::lean_inc_ref(v_inst_986_);
    leanh::lean_inc_n(v_val_987_, 2);
    v___x_988_ = leanh::lean_apply_2(v_inst_986_, v_val_987_, v_hi_985_);
    v___x_989_ = leanh::lean_apply_2(v_inst_986_, v_lo_984_, v_val_987_);
    v___x_990_ = (leanh::lean_unbox(v___x_989_) as u8);
    if v___x_990_ == 0 {
        let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_val_987_);
        v___x_991_ = leanh::lean_box(0);
        return v___x_991_;
    } else {
        let mut v___x_992_: u8 = 0;
        v___x_992_ = (leanh::lean_unbox(v___x_988_) as u8);
        if v___x_992_ == 0 {
            let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_987_);
            v___x_993_ = leanh::lean_box(0);
            return v___x_993_;
        } else {
            let mut v___x_994_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_994_, 0, v_val_987_);
            return v___x_994_;
        }
    }
}
pub unsafe fn _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_995_ = leanh::lean_unsigned_to_nat(1);
    v___x_996_ = lean_nat_to_int(v___x_995_);
    return v___x_996_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(
    mut v_lo_997_: *mut leanh::LeanObject,
    mut v_hi_998_: *mut leanh::LeanObject,
    mut v_val_999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1000_ = lean_int_sub(v_hi_998_, v_lo_997_);
    v___x_1001_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v_range_1002_ = lean_int_add(v___x_1000_, v___x_1001_);
    leanh::lean_dec(v___x_1000_);
    v___x_1003_ = lean_int_sub(v_val_999_, v_lo_997_);
    v___x_1004_ = lean_int_emod(v___x_1003_, v_range_1002_);
    leanh::lean_dec(v___x_1003_);
    v___x_1005_ = lean_int_add(v___x_1004_, v_range_1002_);
    leanh::lean_dec(v___x_1004_);
    v___x_1006_ = lean_int_emod(v___x_1005_, v_range_1002_);
    leanh::lean_dec(v_range_1002_);
    leanh::lean_dec(v___x_1005_);
    v___x_1007_ = lean_int_add(v___x_1006_, v_lo_997_);
    leanh::lean_dec(v___x_1006_);
    return v___x_1007_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___boxed(
    mut v_lo_1008_: *mut leanh::LeanObject,
    mut v_hi_1009_: *mut leanh::LeanObject,
    mut v_val_1010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1011_ =
        l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg(v_lo_1008_, v_hi_1009_, v_val_1010_);
    leanh::lean_dec(v_val_1010_);
    leanh::lean_dec(v_hi_1009_);
    leanh::lean_dec(v_lo_1008_);
    return v_res_1011_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNatWrapping(
    mut v_lo_1012_: *mut leanh::LeanObject,
    mut v_hi_1013_: *mut leanh::LeanObject,
    mut v_val_1014_: *mut leanh::LeanObject,
    mut v_h_1015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1016_ = lean_int_sub(v_hi_1013_, v_lo_1012_);
    v___x_1017_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v_range_1018_ = lean_int_add(v___x_1016_, v___x_1017_);
    leanh::lean_dec(v___x_1016_);
    v___x_1019_ = lean_int_sub(v_val_1014_, v_lo_1012_);
    v___x_1020_ = lean_int_emod(v___x_1019_, v_range_1018_);
    leanh::lean_dec(v___x_1019_);
    v___x_1021_ = lean_int_add(v___x_1020_, v_range_1018_);
    leanh::lean_dec(v___x_1020_);
    v___x_1022_ = lean_int_emod(v___x_1021_, v_range_1018_);
    leanh::lean_dec(v_range_1018_);
    leanh::lean_dec(v___x_1021_);
    v___x_1023_ = lean_int_add(v___x_1022_, v_lo_1012_);
    leanh::lean_dec(v___x_1022_);
    return v___x_1023_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNatWrapping___boxed(
    mut v_lo_1024_: *mut leanh::LeanObject,
    mut v_hi_1025_: *mut leanh::LeanObject,
    mut v_val_1026_: *mut leanh::LeanObject,
    mut v_h_1027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1028_ = l_Std_Time_Internal_Bounded_LE_ofNatWrapping(
        v_lo_1024_,
        v_hi_1025_,
        v_val_1026_,
        v_h_1027_,
    );
    leanh::lean_dec(v_val_1026_);
    leanh::lean_dec(v_hi_1025_);
    leanh::lean_dec(v_lo_1024_);
    return v_res_1028_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(
    mut v_lo_1029_: *mut leanh::LeanObject,
    mut v_n_1030_: *mut leanh::LeanObject,
    mut v_k_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = lean_nat_to_int(v_k_1031_);
    v___x_1033_ = lean_int_add(v_lo_1029_, v___x_1032_);
    leanh::lean_dec(v___x_1032_);
    v___x_1034_ = lean_nat_to_int(v_n_1030_);
    v___x_1035_ = lean_int_sub(v___x_1033_, v_lo_1029_);
    leanh::lean_dec(v___x_1033_);
    v___x_1036_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v_range_1037_ = lean_int_add(v___x_1035_, v___x_1036_);
    leanh::lean_dec(v___x_1035_);
    v___x_1038_ = lean_int_sub(v___x_1034_, v_lo_1029_);
    leanh::lean_dec(v___x_1034_);
    v___x_1039_ = lean_int_emod(v___x_1038_, v_range_1037_);
    leanh::lean_dec(v___x_1038_);
    v___x_1040_ = lean_int_add(v___x_1039_, v_range_1037_);
    leanh::lean_dec(v___x_1039_);
    v___x_1041_ = lean_int_emod(v___x_1040_, v_range_1037_);
    leanh::lean_dec(v_range_1037_);
    leanh::lean_dec(v___x_1040_);
    v___x_1042_ = lean_int_add(v___x_1041_, v_lo_1029_);
    leanh::lean_dec(v___x_1041_);
    return v___x_1042_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast___boxed(
    mut v_lo_1043_: *mut leanh::LeanObject,
    mut v_n_1044_: *mut leanh::LeanObject,
    mut v_k_1045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1046_ =
        l_Std_Time_Internal_Bounded_LE_instOfNatHAddIntCast(v_lo_1043_, v_n_1044_, v_k_1045_);
    leanh::lean_dec(v_lo_1043_);
    return v_res_1046_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(
    mut v_lo_1047_: *mut leanh::LeanObject,
    mut v_k_1048_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_range_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1049_ = lean_nat_to_int(v_k_1048_);
    v___x_1050_ = lean_int_add(v_lo_1047_, v___x_1049_);
    leanh::lean_dec(v___x_1049_);
    v___x_1051_ = lean_int_sub(v___x_1050_, v_lo_1047_);
    leanh::lean_dec(v___x_1050_);
    v___x_1052_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v_range_1053_ = lean_int_add(v___x_1051_, v___x_1052_);
    leanh::lean_dec(v___x_1051_);
    v___x_1054_ = lean_int_sub(v_lo_1047_, v_lo_1047_);
    v___x_1055_ = lean_int_emod(v___x_1054_, v_range_1053_);
    leanh::lean_dec(v___x_1054_);
    v___x_1056_ = lean_int_add(v___x_1055_, v_range_1053_);
    leanh::lean_dec(v___x_1055_);
    v___x_1057_ = lean_int_emod(v___x_1056_, v_range_1053_);
    leanh::lean_dec(v_range_1053_);
    leanh::lean_dec(v___x_1056_);
    v___x_1058_ = lean_int_add(v___x_1057_, v_lo_1047_);
    leanh::lean_dec(v___x_1057_);
    return v___x_1058_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast___boxed(
    mut v_lo_1059_: *mut leanh::LeanObject,
    mut v_k_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1061_ = l_Std_Time_Internal_Bounded_LE_instInhabitedHAddIntCast(v_lo_1059_, v_k_1060_);
    leanh::lean_dec(v_lo_1059_);
    return v_res_1061_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mk___redArg(
    mut v_val_1062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_1062_);
    return v_val_1062_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mk___redArg___boxed(
    mut v_val_1063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1064_ = l_Std_Time_Internal_Bounded_LE_mk___redArg(v_val_1063_);
    leanh::lean_dec(v_val_1063_);
    return v_res_1064_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mk(
    mut v_lo_1065_: *mut leanh::LeanObject,
    mut v_hi_1066_: *mut leanh::LeanObject,
    mut v_val_1067_: *mut leanh::LeanObject,
    mut v_proof_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_val_1067_);
    return v_val_1067_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mk___boxed(
    mut v_lo_1069_: *mut leanh::LeanObject,
    mut v_hi_1070_: *mut leanh::LeanObject,
    mut v_val_1071_: *mut leanh::LeanObject,
    mut v_proof_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ =
        l_Std_Time_Internal_Bounded_LE_mk(v_lo_1069_, v_hi_1070_, v_val_1071_, v_proof_1072_);
    leanh::lean_dec(v_val_1071_);
    leanh::lean_dec(v_hi_1070_);
    leanh::lean_dec(v_lo_1069_);
    return v_res_1073_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_exact(
    mut v_val_1074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1075_ = lean_nat_to_int(v_val_1074_);
    return v___x_1075_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofInt(
    mut v_lo_1076_: *mut leanh::LeanObject,
    mut v_hi_1077_: *mut leanh::LeanObject,
    mut v_val_1078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1079_: u8 = 0;
    v___x_1079_ = lean_int_dec_le(v_lo_1076_, v_val_1078_);
    if v___x_1079_ == 0 {
        let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_val_1078_);
        v___x_1080_ = leanh::lean_box(0);
        return v___x_1080_;
    } else {
        let mut v___x_1081_: u8 = 0;
        v___x_1081_ = lean_int_dec_le(v_val_1078_, v_hi_1077_);
        if v___x_1081_ == 0 {
            let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_val_1078_);
            v___x_1082_ = leanh::lean_box(0);
            return v___x_1082_;
        } else {
            let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1083_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1083_, 0, v_val_1078_);
            return v___x_1083_;
        }
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofInt___boxed(
    mut v_lo_1084_: *mut leanh::LeanObject,
    mut v_hi_1085_: *mut leanh::LeanObject,
    mut v_val_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_Std_Time_Internal_Bounded_LE_ofInt(v_lo_1084_, v_hi_1085_, v_val_1086_);
    leanh::lean_dec(v_hi_1085_);
    leanh::lean_dec(v_lo_1084_);
    return v_res_1087_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat___redArg(
    mut v_val_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = lean_nat_to_int(v_val_1088_);
    return v___x_1089_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat(
    mut v_hi_1090_: *mut leanh::LeanObject,
    mut v_val_1091_: *mut leanh::LeanObject,
    mut v_h_1092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = lean_nat_to_int(v_val_1091_);
    return v___x_1093_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat___boxed(
    mut v_hi_1094_: *mut leanh::LeanObject,
    mut v_val_1095_: *mut leanh::LeanObject,
    mut v_h_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Std_Time_Internal_Bounded_LE_ofNat(v_hi_1094_, v_val_1095_, v_h_1096_);
    leanh::lean_dec(v_hi_1094_);
    return v_res_1097_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat_x3f(
    mut v_hi_1098_: *mut leanh::LeanObject,
    mut v_val_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1100_: u8 = 0;
    v___x_1100_ = lean_nat_dec_le(v_val_1099_, v_hi_1098_);
    if v___x_1100_ == 0 {
        let mut v___x_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_val_1099_);
        v___x_1101_ = leanh::lean_box(0);
        return v___x_1101_;
    } else {
        let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1102_ = lean_nat_to_int(v_val_1099_);
        v___x_1103_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_1103_, 0, v___x_1102_);
        return v___x_1103_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat_x3f___boxed(
    mut v_hi_1104_: *mut leanh::LeanObject,
    mut v_val_1105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1106_ = l_Std_Time_Internal_Bounded_LE_ofNat_x3f(v_hi_1104_, v_val_1105_);
    leanh::lean_dec(v_hi_1104_);
    return v_res_1106_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat_x27___redArg(
    mut v_val_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1108_ = lean_nat_to_int(v_val_1107_);
    return v___x_1108_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat_x27(
    mut v_lo_1109_: *mut leanh::LeanObject,
    mut v_hi_1110_: *mut leanh::LeanObject,
    mut v_val_1111_: *mut leanh::LeanObject,
    mut v_h_1112_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = lean_nat_to_int(v_val_1111_);
    return v___x_1113_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofNat_x27___boxed(
    mut v_lo_1114_: *mut leanh::LeanObject,
    mut v_hi_1115_: *mut leanh::LeanObject,
    mut v_val_1116_: *mut leanh::LeanObject,
    mut v_h_1117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1118_ =
        l_Std_Time_Internal_Bounded_LE_ofNat_x27(v_lo_1114_, v_hi_1115_, v_val_1116_, v_h_1117_);
    leanh::lean_dec(v_hi_1115_);
    leanh::lean_dec(v_lo_1114_);
    return v_res_1118_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_clip___redArg(
    mut v_lo_1119_: *mut leanh::LeanObject,
    mut v_hi_1120_: *mut leanh::LeanObject,
    mut v_val_1121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1122_: u8 = 0;
    v___x_1122_ = lean_int_dec_le(v_lo_1119_, v_val_1121_);
    if v___x_1122_ == 0 {
        leanh::lean_inc(v_lo_1119_);
        return v_lo_1119_;
    } else {
        let mut v___x_1123_: u8 = 0;
        v___x_1123_ = lean_int_dec_le(v_val_1121_, v_hi_1120_);
        if v___x_1123_ == 0 {
            leanh::lean_inc(v_hi_1120_);
            return v_hi_1120_;
        } else {
            leanh::lean_inc(v_val_1121_);
            return v_val_1121_;
        }
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_clip___redArg___boxed(
    mut v_lo_1124_: *mut leanh::LeanObject,
    mut v_hi_1125_: *mut leanh::LeanObject,
    mut v_val_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_Std_Time_Internal_Bounded_LE_clip___redArg(v_lo_1124_, v_hi_1125_, v_val_1126_);
    leanh::lean_dec(v_val_1126_);
    leanh::lean_dec(v_hi_1125_);
    leanh::lean_dec(v_lo_1124_);
    return v_res_1127_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_clip(
    mut v_lo_1128_: *mut leanh::LeanObject,
    mut v_hi_1129_: *mut leanh::LeanObject,
    mut v_val_1130_: *mut leanh::LeanObject,
    mut v_h_1131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1132_: u8 = 0;
    v___x_1132_ = lean_int_dec_le(v_lo_1128_, v_val_1130_);
    if v___x_1132_ == 0 {
        leanh::lean_inc(v_lo_1128_);
        return v_lo_1128_;
    } else {
        let mut v___x_1133_: u8 = 0;
        v___x_1133_ = lean_int_dec_le(v_val_1130_, v_hi_1129_);
        if v___x_1133_ == 0 {
            leanh::lean_inc(v_hi_1129_);
            return v_hi_1129_;
        } else {
            leanh::lean_inc(v_val_1130_);
            return v_val_1130_;
        }
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_clip___boxed(
    mut v_lo_1134_: *mut leanh::LeanObject,
    mut v_hi_1135_: *mut leanh::LeanObject,
    mut v_val_1136_: *mut leanh::LeanObject,
    mut v_h_1137_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1138_ =
        l_Std_Time_Internal_Bounded_LE_clip(v_lo_1134_, v_hi_1135_, v_val_1136_, v_h_1137_);
    leanh::lean_dec(v_val_1136_);
    leanh::lean_dec(v_hi_1135_);
    leanh::lean_dec(v_lo_1134_);
    return v_res_1138_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat___redArg(
    mut v_n_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1140_ = l_Int_toNat(v_n_1139_);
    return v___x_1140_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat___redArg___boxed(
    mut v_n_1141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1142_ = l_Std_Time_Internal_Bounded_LE_toNat___redArg(v_n_1141_);
    leanh::lean_dec(v_n_1141_);
    return v_res_1142_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat(
    mut v_lo_1143_: *mut leanh::LeanObject,
    mut v_hi_1144_: *mut leanh::LeanObject,
    mut v_n_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Int_toNat(v_n_1145_);
    return v___x_1146_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat___boxed(
    mut v_lo_1147_: *mut leanh::LeanObject,
    mut v_hi_1148_: *mut leanh::LeanObject,
    mut v_n_1149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1150_ = l_Std_Time_Internal_Bounded_LE_toNat(v_lo_1147_, v_hi_1148_, v_n_1149_);
    leanh::lean_dec(v_n_1149_);
    leanh::lean_dec(v_hi_1148_);
    leanh::lean_dec(v_lo_1147_);
    return v_res_1150_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(
    mut v_n_1151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1153_: u8 = 0;
    let mut v_a_1154_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1152_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once),
        _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0,
    );
    v_isNeg_1153_ = lean_int_dec_lt(v_n_1151_, v_intZero_1152_);
    v_a_1154_ = lean_nat_abs(v_n_1151_);
    return v_a_1154_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg___boxed(
    mut v_n_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1156_ = l_Std_Time_Internal_Bounded_LE_toNat_x27___redArg(v_n_1155_);
    leanh::lean_dec(v_n_1155_);
    return v_res_1156_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat_x27(
    mut v_lo_1157_: *mut leanh::LeanObject,
    mut v_hi_1158_: *mut leanh::LeanObject,
    mut v_n_1159_: *mut leanh::LeanObject,
    mut v_h_1160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1162_: u8 = 0;
    let mut v_a_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_intZero_1161_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0_once),
        _init_l_Std_Time_Internal_Bounded_instRepr___lam__0___closed__0,
    );
    v_isNeg_1162_ = lean_int_dec_lt(v_n_1159_, v_intZero_1161_);
    v_a_1163_ = lean_nat_abs(v_n_1159_);
    return v_a_1163_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toNat_x27___boxed(
    mut v_lo_1164_: *mut leanh::LeanObject,
    mut v_hi_1165_: *mut leanh::LeanObject,
    mut v_n_1166_: *mut leanh::LeanObject,
    mut v_h_1167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1168_ =
        l_Std_Time_Internal_Bounded_LE_toNat_x27(v_lo_1164_, v_hi_1165_, v_n_1166_, v_h_1167_);
    leanh::lean_dec(v_n_1166_);
    leanh::lean_dec(v_hi_1165_);
    leanh::lean_dec(v_lo_1164_);
    return v_res_1168_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toInt___redArg(
    mut v_n_1169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_1169_);
    return v_n_1169_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toInt___redArg___boxed(
    mut v_n_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Std_Time_Internal_Bounded_LE_toInt___redArg(v_n_1170_);
    leanh::lean_dec(v_n_1170_);
    return v_res_1171_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toInt(
    mut v_lo_1172_: *mut leanh::LeanObject,
    mut v_hi_1173_: *mut leanh::LeanObject,
    mut v_n_1174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_1174_);
    return v_n_1174_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toInt___boxed(
    mut v_lo_1175_: *mut leanh::LeanObject,
    mut v_hi_1176_: *mut leanh::LeanObject,
    mut v_n_1177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1178_ = l_Std_Time_Internal_Bounded_LE_toInt(v_lo_1175_, v_hi_1176_, v_n_1177_);
    leanh::lean_dec(v_n_1177_);
    leanh::lean_dec(v_hi_1176_);
    leanh::lean_dec(v_lo_1175_);
    return v_res_1178_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toFin___redArg(
    mut v_n_1179_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1180_ = l_Int_toNat(v_n_1179_);
    return v___x_1180_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toFin___redArg___boxed(
    mut v_n_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1182_ = l_Std_Time_Internal_Bounded_LE_toFin___redArg(v_n_1181_);
    leanh::lean_dec(v_n_1181_);
    return v_res_1182_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toFin(
    mut v_lo_1183_: *mut leanh::LeanObject,
    mut v_hi_1184_: *mut leanh::LeanObject,
    mut v_n_1185_: *mut leanh::LeanObject,
    mut v_h_u2080_1186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1187_ = l_Int_toNat(v_n_1185_);
    return v___x_1187_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_toFin___boxed(
    mut v_lo_1188_: *mut leanh::LeanObject,
    mut v_hi_1189_: *mut leanh::LeanObject,
    mut v_n_1190_: *mut leanh::LeanObject,
    mut v_h_u2080_1191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1192_ =
        l_Std_Time_Internal_Bounded_LE_toFin(v_lo_1188_, v_hi_1189_, v_n_1190_, v_h_u2080_1191_);
    leanh::lean_dec(v_n_1190_);
    leanh::lean_dec(v_hi_1189_);
    leanh::lean_dec(v_lo_1188_);
    return v_res_1192_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin___redArg(
    mut v_fin_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1194_ = lean_nat_to_int(v_fin_1193_);
    return v___x_1194_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin(
    mut v_hi_1195_: *mut leanh::LeanObject,
    mut v_fin_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1197_ = lean_nat_to_int(v_fin_1196_);
    return v___x_1197_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin___boxed(
    mut v_hi_1198_: *mut leanh::LeanObject,
    mut v_fin_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ = l_Std_Time_Internal_Bounded_LE_ofFin(v_hi_1198_, v_fin_1199_);
    leanh::lean_dec(v_hi_1198_);
    return v_res_1200_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin_x27___redArg(
    mut v_lo_1201_: *mut leanh::LeanObject,
    mut v_fin_1202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1203_: u8 = 0;
    v___x_1203_ = lean_nat_dec_le(v_lo_1201_, v_fin_1202_);
    if v___x_1203_ == 0 {
        let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fin_1202_);
        v___x_1204_ = lean_nat_to_int(v_lo_1201_);
        return v___x_1204_;
    } else {
        let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_lo_1201_);
        v___x_1205_ = lean_nat_to_int(v_fin_1202_);
        return v___x_1205_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin_x27(
    mut v_hi_1206_: *mut leanh::LeanObject,
    mut v_lo_1207_: *mut leanh::LeanObject,
    mut v_fin_1208_: *mut leanh::LeanObject,
    mut v_h_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1210_: u8 = 0;
    v___x_1210_ = lean_nat_dec_le(v_lo_1207_, v_fin_1208_);
    if v___x_1210_ == 0 {
        let mut v___x_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_fin_1208_);
        v___x_1211_ = lean_nat_to_int(v_lo_1207_);
        return v___x_1211_;
    } else {
        let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_lo_1207_);
        v___x_1212_ = lean_nat_to_int(v_fin_1208_);
        return v___x_1212_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ofFin_x27___boxed(
    mut v_hi_1213_: *mut leanh::LeanObject,
    mut v_lo_1214_: *mut leanh::LeanObject,
    mut v_fin_1215_: *mut leanh::LeanObject,
    mut v_h_1216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1217_ =
        l_Std_Time_Internal_Bounded_LE_ofFin_x27(v_hi_1213_, v_lo_1214_, v_fin_1215_, v_h_1216_);
    leanh::lean_dec(v_hi_1213_);
    return v_res_1217_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byEmod___redArg(
    mut v_b_1218_: *mut leanh::LeanObject,
    mut v_i_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1220_ = lean_int_emod(v_b_1218_, v_i_1219_);
    return v___x_1220_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byEmod___redArg___boxed(
    mut v_b_1221_: *mut leanh::LeanObject,
    mut v_i_1222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1223_ = l_Std_Time_Internal_Bounded_LE_byEmod___redArg(v_b_1221_, v_i_1222_);
    leanh::lean_dec(v_i_1222_);
    leanh::lean_dec(v_b_1221_);
    return v_res_1223_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byEmod(
    mut v_b_1224_: *mut leanh::LeanObject,
    mut v_i_1225_: *mut leanh::LeanObject,
    mut v_hi_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1227_ = lean_int_emod(v_b_1224_, v_i_1225_);
    return v___x_1227_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byEmod___boxed(
    mut v_b_1228_: *mut leanh::LeanObject,
    mut v_i_1229_: *mut leanh::LeanObject,
    mut v_hi_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1231_ = l_Std_Time_Internal_Bounded_LE_byEmod(v_b_1228_, v_i_1229_, v_hi_1230_);
    leanh::lean_dec(v_i_1229_);
    leanh::lean_dec(v_b_1228_);
    return v_res_1231_;
}
pub unsafe fn _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_1232_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_1233_ = lean_nat_to_int(v_natZero_1232_);
    return v_intZero_1233_;
}
pub unsafe fn l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(
    mut v_x_1234_: *mut leanh::LeanObject,
    mut v_x_1235_: *mut leanh::LeanObject,
    mut v_h__1_1236_: *mut leanh::LeanObject,
    mut v_h__2_1237_: *mut leanh::LeanObject,
    mut v_h__3_1238_: *mut leanh::LeanObject,
    mut v_h__4_1239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1241_: u8 = 0;
    v_intZero_1240_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_1241_ = lean_int_dec_lt(v_x_1234_, v_intZero_1240_);
    if v_isNeg_1241_ == 0 {
        let mut v_a_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1243_: u8 = 0;
        leanh::lean_dec(v_h__4_1239_);
        leanh::lean_dec(v_h__3_1238_);
        v_a_1242_ = lean_nat_abs(v_x_1234_);
        v_isNeg_1243_ = lean_int_dec_lt(v_x_1235_, v_intZero_1240_);
        if v_isNeg_1243_ == 0 {
            let mut v_a_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1237_);
            v_a_1244_ = lean_nat_abs(v_x_1235_);
            v___x_1245_ = leanh::lean_apply_2(v_h__1_1236_, v_a_1242_, v_a_1244_);
            return v___x_1245_;
        } else {
            let mut v_abs_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1247_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1249_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1236_);
            v_abs_1246_ = lean_nat_abs(v_x_1235_);
            v_one_1247_ = leanh::lean_unsigned_to_nat(1);
            v_a_1248_ = lean_nat_sub(v_abs_1246_, v_one_1247_);
            leanh::lean_dec(v_abs_1246_);
            v___x_1249_ = leanh::lean_apply_2(v_h__2_1237_, v_a_1242_, v_a_1248_);
            return v___x_1249_;
        }
    } else {
        let mut v_abs_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1251_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1253_: u8 = 0;
        leanh::lean_dec(v_h__2_1237_);
        leanh::lean_dec(v_h__1_1236_);
        v_abs_1250_ = lean_nat_abs(v_x_1234_);
        v_one_1251_ = leanh::lean_unsigned_to_nat(1);
        v_a_1252_ = lean_nat_sub(v_abs_1250_, v_one_1251_);
        leanh::lean_dec(v_abs_1250_);
        v_isNeg_1253_ = lean_int_dec_lt(v_x_1235_, v_intZero_1240_);
        if v_isNeg_1253_ == 0 {
            let mut v_a_1254_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1239_);
            v_a_1254_ = lean_nat_abs(v_x_1235_);
            v___x_1255_ = leanh::lean_apply_2(v_h__3_1238_, v_a_1252_, v_a_1254_);
            return v___x_1255_;
        } else {
            let mut v_abs_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1238_);
            v_abs_1256_ = lean_nat_abs(v_x_1235_);
            v_a_1257_ = lean_nat_sub(v_abs_1256_, v_one_1251_);
            leanh::lean_dec(v_abs_1256_);
            v___x_1258_ = leanh::lean_apply_2(v_h__4_1239_, v_a_1252_, v_a_1257_);
            return v___x_1258_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___boxed(
    mut v_x_1259_: *mut leanh::LeanObject,
    mut v_x_1260_: *mut leanh::LeanObject,
    mut v_h__1_1261_: *mut leanh::LeanObject,
    mut v_h__2_1262_: *mut leanh::LeanObject,
    mut v_h__3_1263_: *mut leanh::LeanObject,
    mut v_h__4_1264_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg(
        v_x_1259_,
        v_x_1260_,
        v_h__1_1261_,
        v_h__2_1262_,
        v_h__3_1263_,
        v_h__4_1264_,
    );
    leanh::lean_dec(v_x_1260_);
    leanh::lean_dec(v_x_1259_);
    return v_res_1265_;
}
pub unsafe fn l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(
    mut v_motive_1266_: *mut leanh::LeanObject,
    mut v_x_1267_: *mut leanh::LeanObject,
    mut v_x_1268_: *mut leanh::LeanObject,
    mut v_h__1_1269_: *mut leanh::LeanObject,
    mut v_h__2_1270_: *mut leanh::LeanObject,
    mut v_h__3_1271_: *mut leanh::LeanObject,
    mut v_h__4_1272_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_intZero_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_1274_: u8 = 0;
    v_intZero_1273_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v_isNeg_1274_ = lean_int_dec_lt(v_x_1267_, v_intZero_1273_);
    if v_isNeg_1274_ == 0 {
        let mut v_a_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1276_: u8 = 0;
        leanh::lean_dec(v_h__4_1272_);
        leanh::lean_dec(v_h__3_1271_);
        v_a_1275_ = lean_nat_abs(v_x_1267_);
        v_isNeg_1276_ = lean_int_dec_lt(v_x_1268_, v_intZero_1273_);
        if v_isNeg_1276_ == 0 {
            let mut v_a_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1270_);
            v_a_1277_ = lean_nat_abs(v_x_1268_);
            v___x_1278_ = leanh::lean_apply_2(v_h__1_1269_, v_a_1275_, v_a_1277_);
            return v___x_1278_;
        } else {
            let mut v_abs_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_1280_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1269_);
            v_abs_1279_ = lean_nat_abs(v_x_1268_);
            v_one_1280_ = leanh::lean_unsigned_to_nat(1);
            v_a_1281_ = lean_nat_sub(v_abs_1279_, v_one_1280_);
            leanh::lean_dec(v_abs_1279_);
            v___x_1282_ = leanh::lean_apply_2(v_h__2_1270_, v_a_1275_, v_a_1281_);
            return v___x_1282_;
        }
    } else {
        let mut v_abs_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_1286_: u8 = 0;
        leanh::lean_dec(v_h__2_1270_);
        leanh::lean_dec(v_h__1_1269_);
        v_abs_1283_ = lean_nat_abs(v_x_1267_);
        v_one_1284_ = leanh::lean_unsigned_to_nat(1);
        v_a_1285_ = lean_nat_sub(v_abs_1283_, v_one_1284_);
        leanh::lean_dec(v_abs_1283_);
        v_isNeg_1286_ = lean_int_dec_lt(v_x_1268_, v_intZero_1273_);
        if v_isNeg_1286_ == 0 {
            let mut v_a_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1272_);
            v_a_1287_ = lean_nat_abs(v_x_1268_);
            v___x_1288_ = leanh::lean_apply_2(v_h__3_1271_, v_a_1285_, v_a_1287_);
            return v___x_1288_;
        } else {
            let mut v_abs_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1271_);
            v_abs_1289_ = lean_nat_abs(v_x_1268_);
            v_a_1290_ = lean_nat_sub(v_abs_1289_, v_one_1284_);
            leanh::lean_dec(v_abs_1289_);
            v___x_1291_ = leanh::lean_apply_2(v_h__4_1272_, v_a_1285_, v_a_1290_);
            return v___x_1291_;
        }
    }
}
pub unsafe fn l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___boxed(
    mut v_motive_1292_: *mut leanh::LeanObject,
    mut v_x_1293_: *mut leanh::LeanObject,
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_h__1_1295_: *mut leanh::LeanObject,
    mut v_h__2_1296_: *mut leanh::LeanObject,
    mut v_h__3_1297_: *mut leanh::LeanObject,
    mut v_h__4_1298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter(
        v_motive_1292_,
        v_x_1293_,
        v_x_1294_,
        v_h__1_1295_,
        v_h__2_1296_,
        v_h__3_1297_,
        v_h__4_1298_,
    );
    leanh::lean_dec(v_x_1294_);
    leanh::lean_dec(v_x_1293_);
    return v_res_1299_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byMod___redArg(
    mut v_b_1300_: *mut leanh::LeanObject,
    mut v_i_1301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1302_ = lean_int_mod(v_b_1300_, v_i_1301_);
    return v___x_1302_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byMod___redArg___boxed(
    mut v_b_1303_: *mut leanh::LeanObject,
    mut v_i_1304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1305_ = l_Std_Time_Internal_Bounded_LE_byMod___redArg(v_b_1303_, v_i_1304_);
    leanh::lean_dec(v_i_1304_);
    leanh::lean_dec(v_b_1303_);
    return v_res_1305_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byMod(
    mut v_b_1306_: *mut leanh::LeanObject,
    mut v_i_1307_: *mut leanh::LeanObject,
    mut v_hi_1308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1309_ = lean_int_mod(v_b_1306_, v_i_1307_);
    return v___x_1309_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_byMod___boxed(
    mut v_b_1310_: *mut leanh::LeanObject,
    mut v_i_1311_: *mut leanh::LeanObject,
    mut v_hi_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_Std_Time_Internal_Bounded_LE_byMod(v_b_1310_, v_i_1311_, v_hi_1312_);
    leanh::lean_dec(v_i_1311_);
    leanh::lean_dec(v_b_1310_);
    return v_res_1313_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncate___redArg(
    mut v_n_1314_: *mut leanh::LeanObject,
    mut v_bounded_1315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1316_ = lean_int_sub(v_bounded_1315_, v_n_1314_);
    return v___x_1316_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncate___redArg___boxed(
    mut v_n_1317_: *mut leanh::LeanObject,
    mut v_bounded_1318_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1319_ = l_Std_Time_Internal_Bounded_LE_truncate___redArg(v_n_1317_, v_bounded_1318_);
    leanh::lean_dec(v_bounded_1318_);
    leanh::lean_dec(v_n_1317_);
    return v_res_1319_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncate(
    mut v_n_1320_: *mut leanh::LeanObject,
    mut v_m_1321_: *mut leanh::LeanObject,
    mut v_bounded_1322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1323_ = lean_int_sub(v_bounded_1322_, v_n_1320_);
    return v___x_1323_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncate___boxed(
    mut v_n_1324_: *mut leanh::LeanObject,
    mut v_m_1325_: *mut leanh::LeanObject,
    mut v_bounded_1326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1327_ = l_Std_Time_Internal_Bounded_LE_truncate(v_n_1324_, v_m_1325_, v_bounded_1326_);
    leanh::lean_dec(v_bounded_1326_);
    leanh::lean_dec(v_m_1325_);
    leanh::lean_dec(v_n_1324_);
    return v_res_1327_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(
    mut v_bounded_1328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1328_);
    return v_bounded_1328_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateTop___redArg___boxed(
    mut v_bounded_1329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1330_ = l_Std_Time_Internal_Bounded_LE_truncateTop___redArg(v_bounded_1329_);
    leanh::lean_dec(v_bounded_1329_);
    return v_res_1330_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateTop(
    mut v_n_1331_: *mut leanh::LeanObject,
    mut v_m_1332_: *mut leanh::LeanObject,
    mut v_j_1333_: *mut leanh::LeanObject,
    mut v_bounded_1334_: *mut leanh::LeanObject,
    mut v_h_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1334_);
    return v_bounded_1334_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateTop___boxed(
    mut v_n_1336_: *mut leanh::LeanObject,
    mut v_m_1337_: *mut leanh::LeanObject,
    mut v_j_1338_: *mut leanh::LeanObject,
    mut v_bounded_1339_: *mut leanh::LeanObject,
    mut v_h_1340_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1341_ = l_Std_Time_Internal_Bounded_LE_truncateTop(
        v_n_1336_,
        v_m_1337_,
        v_j_1338_,
        v_bounded_1339_,
        v_h_1340_,
    );
    leanh::lean_dec(v_bounded_1339_);
    leanh::lean_dec(v_j_1338_);
    leanh::lean_dec(v_m_1337_);
    leanh::lean_dec(v_n_1336_);
    return v_res_1341_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(
    mut v_bounded_1342_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1342_);
    return v_bounded_1342_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg___boxed(
    mut v_bounded_1343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1344_ = l_Std_Time_Internal_Bounded_LE_truncateBottom___redArg(v_bounded_1343_);
    leanh::lean_dec(v_bounded_1343_);
    return v_res_1344_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateBottom(
    mut v_n_1345_: *mut leanh::LeanObject,
    mut v_m_1346_: *mut leanh::LeanObject,
    mut v_j_1347_: *mut leanh::LeanObject,
    mut v_bounded_1348_: *mut leanh::LeanObject,
    mut v_h_1349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1348_);
    return v_bounded_1348_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_truncateBottom___boxed(
    mut v_n_1350_: *mut leanh::LeanObject,
    mut v_m_1351_: *mut leanh::LeanObject,
    mut v_j_1352_: *mut leanh::LeanObject,
    mut v_bounded_1353_: *mut leanh::LeanObject,
    mut v_h_1354_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1355_ = l_Std_Time_Internal_Bounded_LE_truncateBottom(
        v_n_1350_,
        v_m_1351_,
        v_j_1352_,
        v_bounded_1353_,
        v_h_1354_,
    );
    leanh::lean_dec(v_bounded_1353_);
    leanh::lean_dec(v_j_1352_);
    leanh::lean_dec(v_m_1351_);
    leanh::lean_dec(v_n_1350_);
    return v_res_1355_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_neg___redArg(
    mut v_bounded_1356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1357_ = lean_int_neg(v_bounded_1356_);
    return v___x_1357_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_neg___redArg___boxed(
    mut v_bounded_1358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1359_ = l_Std_Time_Internal_Bounded_LE_neg___redArg(v_bounded_1358_);
    leanh::lean_dec(v_bounded_1358_);
    return v_res_1359_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_neg(
    mut v_n_1360_: *mut leanh::LeanObject,
    mut v_m_1361_: *mut leanh::LeanObject,
    mut v_bounded_1362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1363_ = lean_int_neg(v_bounded_1362_);
    return v___x_1363_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_neg___boxed(
    mut v_n_1364_: *mut leanh::LeanObject,
    mut v_m_1365_: *mut leanh::LeanObject,
    mut v_bounded_1366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1367_ = l_Std_Time_Internal_Bounded_LE_neg(v_n_1364_, v_m_1365_, v_bounded_1366_);
    leanh::lean_dec(v_bounded_1366_);
    leanh::lean_dec(v_m_1365_);
    leanh::lean_dec(v_n_1364_);
    return v_res_1367_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_add___redArg(
    mut v_bounded_1368_: *mut leanh::LeanObject,
    mut v_num_1369_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1370_ = lean_int_add(v_bounded_1368_, v_num_1369_);
    return v___x_1370_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_add___redArg___boxed(
    mut v_bounded_1371_: *mut leanh::LeanObject,
    mut v_num_1372_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1373_ = l_Std_Time_Internal_Bounded_LE_add___redArg(v_bounded_1371_, v_num_1372_);
    leanh::lean_dec(v_num_1372_);
    leanh::lean_dec(v_bounded_1371_);
    return v_res_1373_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_add(
    mut v_n_1374_: *mut leanh::LeanObject,
    mut v_m_1375_: *mut leanh::LeanObject,
    mut v_bounded_1376_: *mut leanh::LeanObject,
    mut v_num_1377_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1378_ = lean_int_add(v_bounded_1376_, v_num_1377_);
    return v___x_1378_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_add___boxed(
    mut v_n_1379_: *mut leanh::LeanObject,
    mut v_m_1380_: *mut leanh::LeanObject,
    mut v_bounded_1381_: *mut leanh::LeanObject,
    mut v_num_1382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1383_ =
        l_Std_Time_Internal_Bounded_LE_add(v_n_1379_, v_m_1380_, v_bounded_1381_, v_num_1382_);
    leanh::lean_dec(v_num_1382_);
    leanh::lean_dec(v_bounded_1381_);
    leanh::lean_dec(v_m_1380_);
    leanh::lean_dec(v_n_1379_);
    return v_res_1383_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addProven___redArg(
    mut v_num_1384_: *mut leanh::LeanObject,
    mut v_bounded_1385_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1386_ = lean_int_add(v_bounded_1385_, v_num_1384_);
    return v___x_1386_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addProven___redArg___boxed(
    mut v_num_1387_: *mut leanh::LeanObject,
    mut v_bounded_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1389_ = l_Std_Time_Internal_Bounded_LE_addProven___redArg(v_num_1387_, v_bounded_1388_);
    leanh::lean_dec(v_bounded_1388_);
    leanh::lean_dec(v_num_1387_);
    return v_res_1389_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addProven(
    mut v_n_1390_: *mut leanh::LeanObject,
    mut v_m_1391_: *mut leanh::LeanObject,
    mut v_num_1392_: *mut leanh::LeanObject,
    mut v_bounded_1393_: *mut leanh::LeanObject,
    mut v_h_u2080_1394_: *mut leanh::LeanObject,
    mut v_h_u2081_1395_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1396_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1396_ = lean_int_add(v_bounded_1393_, v_num_1392_);
    return v___x_1396_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addProven___boxed(
    mut v_n_1397_: *mut leanh::LeanObject,
    mut v_m_1398_: *mut leanh::LeanObject,
    mut v_num_1399_: *mut leanh::LeanObject,
    mut v_bounded_1400_: *mut leanh::LeanObject,
    mut v_h_u2080_1401_: *mut leanh::LeanObject,
    mut v_h_u2081_1402_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1403_ = l_Std_Time_Internal_Bounded_LE_addProven(
        v_n_1397_,
        v_m_1398_,
        v_num_1399_,
        v_bounded_1400_,
        v_h_u2080_1401_,
        v_h_u2081_1402_,
    );
    leanh::lean_dec(v_bounded_1400_);
    leanh::lean_dec(v_num_1399_);
    leanh::lean_dec(v_m_1398_);
    leanh::lean_dec(v_n_1397_);
    return v_res_1403_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addTop___redArg(
    mut v_bounded_1404_: *mut leanh::LeanObject,
    mut v_num_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1406_ = lean_int_add(v_bounded_1404_, v_num_1405_);
    return v___x_1406_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addTop___redArg___boxed(
    mut v_bounded_1407_: *mut leanh::LeanObject,
    mut v_num_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1409_ = l_Std_Time_Internal_Bounded_LE_addTop___redArg(v_bounded_1407_, v_num_1408_);
    leanh::lean_dec(v_num_1408_);
    leanh::lean_dec(v_bounded_1407_);
    return v_res_1409_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addTop(
    mut v_n_1410_: *mut leanh::LeanObject,
    mut v_m_1411_: *mut leanh::LeanObject,
    mut v_bounded_1412_: *mut leanh::LeanObject,
    mut v_num_1413_: *mut leanh::LeanObject,
    mut v_h_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1415_ = lean_int_add(v_bounded_1412_, v_num_1413_);
    return v___x_1415_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addTop___boxed(
    mut v_n_1416_: *mut leanh::LeanObject,
    mut v_m_1417_: *mut leanh::LeanObject,
    mut v_bounded_1418_: *mut leanh::LeanObject,
    mut v_num_1419_: *mut leanh::LeanObject,
    mut v_h_1420_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1421_ = l_Std_Time_Internal_Bounded_LE_addTop(
        v_n_1416_,
        v_m_1417_,
        v_bounded_1418_,
        v_num_1419_,
        v_h_1420_,
    );
    leanh::lean_dec(v_num_1419_);
    leanh::lean_dec(v_bounded_1418_);
    leanh::lean_dec(v_m_1417_);
    leanh::lean_dec(v_n_1416_);
    return v_res_1421_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBottom___redArg(
    mut v_bounded_1422_: *mut leanh::LeanObject,
    mut v_num_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1424_ = lean_int_sub(v_bounded_1422_, v_num_1423_);
    return v___x_1424_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBottom___redArg___boxed(
    mut v_bounded_1425_: *mut leanh::LeanObject,
    mut v_num_1426_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1427_ = l_Std_Time_Internal_Bounded_LE_subBottom___redArg(v_bounded_1425_, v_num_1426_);
    leanh::lean_dec(v_num_1426_);
    leanh::lean_dec(v_bounded_1425_);
    return v_res_1427_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBottom(
    mut v_n_1428_: *mut leanh::LeanObject,
    mut v_m_1429_: *mut leanh::LeanObject,
    mut v_bounded_1430_: *mut leanh::LeanObject,
    mut v_num_1431_: *mut leanh::LeanObject,
    mut v_h_1432_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1433_ = lean_int_sub(v_bounded_1430_, v_num_1431_);
    return v___x_1433_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBottom___boxed(
    mut v_n_1434_: *mut leanh::LeanObject,
    mut v_m_1435_: *mut leanh::LeanObject,
    mut v_bounded_1436_: *mut leanh::LeanObject,
    mut v_num_1437_: *mut leanh::LeanObject,
    mut v_h_1438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1439_ = l_Std_Time_Internal_Bounded_LE_subBottom(
        v_n_1434_,
        v_m_1435_,
        v_bounded_1436_,
        v_num_1437_,
        v_h_1438_,
    );
    leanh::lean_dec(v_num_1437_);
    leanh::lean_dec(v_bounded_1436_);
    leanh::lean_dec(v_m_1435_);
    leanh::lean_dec(v_n_1434_);
    return v_res_1439_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addBounds___redArg(
    mut v_bounded_1440_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1442_ = lean_int_add(v_bounded_1440_, v_bounded_u2082_1441_);
    return v___x_1442_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addBounds___redArg___boxed(
    mut v_bounded_1443_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ =
        l_Std_Time_Internal_Bounded_LE_addBounds___redArg(v_bounded_1443_, v_bounded_u2082_1444_);
    leanh::lean_dec(v_bounded_u2082_1444_);
    leanh::lean_dec(v_bounded_1443_);
    return v_res_1445_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addBounds(
    mut v_n_1446_: *mut leanh::LeanObject,
    mut v_m_1447_: *mut leanh::LeanObject,
    mut v_i_1448_: *mut leanh::LeanObject,
    mut v_j_1449_: *mut leanh::LeanObject,
    mut v_bounded_1450_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1452_ = lean_int_add(v_bounded_1450_, v_bounded_u2082_1451_);
    return v___x_1452_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_addBounds___boxed(
    mut v_n_1453_: *mut leanh::LeanObject,
    mut v_m_1454_: *mut leanh::LeanObject,
    mut v_i_1455_: *mut leanh::LeanObject,
    mut v_j_1456_: *mut leanh::LeanObject,
    mut v_bounded_1457_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1458_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1459_ = l_Std_Time_Internal_Bounded_LE_addBounds(
        v_n_1453_,
        v_m_1454_,
        v_i_1455_,
        v_j_1456_,
        v_bounded_1457_,
        v_bounded_u2082_1458_,
    );
    leanh::lean_dec(v_bounded_u2082_1458_);
    leanh::lean_dec(v_bounded_1457_);
    leanh::lean_dec(v_j_1456_);
    leanh::lean_dec(v_i_1455_);
    leanh::lean_dec(v_m_1454_);
    leanh::lean_dec(v_n_1453_);
    return v_res_1459_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_sub___redArg(
    mut v_bounded_1460_: *mut leanh::LeanObject,
    mut v_num_1461_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1462_ = lean_int_neg(v_num_1461_);
    v___x_1463_ = lean_int_add(v_bounded_1460_, v___x_1462_);
    leanh::lean_dec(v___x_1462_);
    return v___x_1463_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_sub___redArg___boxed(
    mut v_bounded_1464_: *mut leanh::LeanObject,
    mut v_num_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1466_ = l_Std_Time_Internal_Bounded_LE_sub___redArg(v_bounded_1464_, v_num_1465_);
    leanh::lean_dec(v_num_1465_);
    leanh::lean_dec(v_bounded_1464_);
    return v_res_1466_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_sub(
    mut v_n_1467_: *mut leanh::LeanObject,
    mut v_m_1468_: *mut leanh::LeanObject,
    mut v_bounded_1469_: *mut leanh::LeanObject,
    mut v_num_1470_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1471_ = lean_int_neg(v_num_1470_);
    v___x_1472_ = lean_int_add(v_bounded_1469_, v___x_1471_);
    leanh::lean_dec(v___x_1471_);
    return v___x_1472_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_sub___boxed(
    mut v_n_1473_: *mut leanh::LeanObject,
    mut v_m_1474_: *mut leanh::LeanObject,
    mut v_bounded_1475_: *mut leanh::LeanObject,
    mut v_num_1476_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1477_ =
        l_Std_Time_Internal_Bounded_LE_sub(v_n_1473_, v_m_1474_, v_bounded_1475_, v_num_1476_);
    leanh::lean_dec(v_num_1476_);
    leanh::lean_dec(v_bounded_1475_);
    leanh::lean_dec(v_m_1474_);
    leanh::lean_dec(v_n_1473_);
    return v_res_1477_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBounds___redArg(
    mut v_bounded_1478_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1480_ = lean_int_neg(v_bounded_u2082_1479_);
    v___x_1481_ = lean_int_add(v_bounded_1478_, v___x_1480_);
    leanh::lean_dec(v___x_1480_);
    return v___x_1481_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBounds___redArg___boxed(
    mut v_bounded_1482_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1484_ =
        l_Std_Time_Internal_Bounded_LE_subBounds___redArg(v_bounded_1482_, v_bounded_u2082_1483_);
    leanh::lean_dec(v_bounded_u2082_1483_);
    leanh::lean_dec(v_bounded_1482_);
    return v_res_1484_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBounds(
    mut v_n_1485_: *mut leanh::LeanObject,
    mut v_m_1486_: *mut leanh::LeanObject,
    mut v_i_1487_: *mut leanh::LeanObject,
    mut v_j_1488_: *mut leanh::LeanObject,
    mut v_bounded_1489_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1491_ = lean_int_neg(v_bounded_u2082_1490_);
    v___x_1492_ = lean_int_add(v_bounded_1489_, v___x_1491_);
    leanh::lean_dec(v___x_1491_);
    return v___x_1492_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_subBounds___boxed(
    mut v_n_1493_: *mut leanh::LeanObject,
    mut v_m_1494_: *mut leanh::LeanObject,
    mut v_i_1495_: *mut leanh::LeanObject,
    mut v_j_1496_: *mut leanh::LeanObject,
    mut v_bounded_1497_: *mut leanh::LeanObject,
    mut v_bounded_u2082_1498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_Std_Time_Internal_Bounded_LE_subBounds(
        v_n_1493_,
        v_m_1494_,
        v_i_1495_,
        v_j_1496_,
        v_bounded_1497_,
        v_bounded_u2082_1498_,
    );
    leanh::lean_dec(v_bounded_u2082_1498_);
    leanh::lean_dec(v_bounded_1497_);
    leanh::lean_dec(v_j_1496_);
    leanh::lean_dec(v_i_1495_);
    leanh::lean_dec(v_m_1494_);
    leanh::lean_dec(v_n_1493_);
    return v_res_1499_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_emod___redArg(
    mut v_bounded_1500_: *mut leanh::LeanObject,
    mut v_num_1501_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1502_ = lean_int_emod(v_bounded_1500_, v_num_1501_);
    return v___x_1502_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_emod___redArg___boxed(
    mut v_bounded_1503_: *mut leanh::LeanObject,
    mut v_num_1504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1505_ = l_Std_Time_Internal_Bounded_LE_emod___redArg(v_bounded_1503_, v_num_1504_);
    leanh::lean_dec(v_num_1504_);
    leanh::lean_dec(v_bounded_1503_);
    return v_res_1505_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_emod(
    mut v_n_1506_: *mut leanh::LeanObject,
    mut v_num_1507_: *mut leanh::LeanObject,
    mut v_bounded_1508_: *mut leanh::LeanObject,
    mut v_num_1509_: *mut leanh::LeanObject,
    mut v_hi_1510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1511_ = lean_int_emod(v_bounded_1508_, v_num_1509_);
    return v___x_1511_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_emod___boxed(
    mut v_n_1512_: *mut leanh::LeanObject,
    mut v_num_1513_: *mut leanh::LeanObject,
    mut v_bounded_1514_: *mut leanh::LeanObject,
    mut v_num_1515_: *mut leanh::LeanObject,
    mut v_hi_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1517_ = l_Std_Time_Internal_Bounded_LE_emod(
        v_n_1512_,
        v_num_1513_,
        v_bounded_1514_,
        v_num_1515_,
        v_hi_1516_,
    );
    leanh::lean_dec(v_num_1515_);
    leanh::lean_dec(v_bounded_1514_);
    leanh::lean_dec(v_num_1513_);
    leanh::lean_dec(v_n_1512_);
    return v_res_1517_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mod___redArg(
    mut v_bounded_1518_: *mut leanh::LeanObject,
    mut v_num_1519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1520_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1520_ = lean_int_mod(v_bounded_1518_, v_num_1519_);
    return v___x_1520_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mod___redArg___boxed(
    mut v_bounded_1521_: *mut leanh::LeanObject,
    mut v_num_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l_Std_Time_Internal_Bounded_LE_mod___redArg(v_bounded_1521_, v_num_1522_);
    leanh::lean_dec(v_num_1522_);
    leanh::lean_dec(v_bounded_1521_);
    return v_res_1523_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mod(
    mut v_n_1524_: *mut leanh::LeanObject,
    mut v_num_1525_: *mut leanh::LeanObject,
    mut v_bounded_1526_: *mut leanh::LeanObject,
    mut v_num_1527_: *mut leanh::LeanObject,
    mut v_hi_1528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1529_ = lean_int_mod(v_bounded_1526_, v_num_1527_);
    return v___x_1529_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mod___boxed(
    mut v_n_1530_: *mut leanh::LeanObject,
    mut v_num_1531_: *mut leanh::LeanObject,
    mut v_bounded_1532_: *mut leanh::LeanObject,
    mut v_num_1533_: *mut leanh::LeanObject,
    mut v_hi_1534_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1535_ = l_Std_Time_Internal_Bounded_LE_mod(
        v_n_1530_,
        v_num_1531_,
        v_bounded_1532_,
        v_num_1533_,
        v_hi_1534_,
    );
    leanh::lean_dec(v_num_1533_);
    leanh::lean_dec(v_bounded_1532_);
    leanh::lean_dec(v_num_1531_);
    leanh::lean_dec(v_n_1530_);
    return v_res_1535_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(
    mut v_bounded_1536_: *mut leanh::LeanObject,
    mut v_num_1537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1538_ = lean_int_mul(v_bounded_1536_, v_num_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__pos___redArg___boxed(
    mut v_bounded_1539_: *mut leanh::LeanObject,
    mut v_num_1540_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_Std_Time_Internal_Bounded_LE_mul__pos___redArg(v_bounded_1539_, v_num_1540_);
    leanh::lean_dec(v_num_1540_);
    leanh::lean_dec(v_bounded_1539_);
    return v_res_1541_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__pos(
    mut v_n_1542_: *mut leanh::LeanObject,
    mut v_m_1543_: *mut leanh::LeanObject,
    mut v_bounded_1544_: *mut leanh::LeanObject,
    mut v_num_1545_: *mut leanh::LeanObject,
    mut v_h_1546_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1547_ = lean_int_mul(v_bounded_1544_, v_num_1545_);
    return v___x_1547_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__pos___boxed(
    mut v_n_1548_: *mut leanh::LeanObject,
    mut v_m_1549_: *mut leanh::LeanObject,
    mut v_bounded_1550_: *mut leanh::LeanObject,
    mut v_num_1551_: *mut leanh::LeanObject,
    mut v_h_1552_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1553_ = l_Std_Time_Internal_Bounded_LE_mul__pos(
        v_n_1548_,
        v_m_1549_,
        v_bounded_1550_,
        v_num_1551_,
        v_h_1552_,
    );
    leanh::lean_dec(v_num_1551_);
    leanh::lean_dec(v_bounded_1550_);
    leanh::lean_dec(v_m_1549_);
    leanh::lean_dec(v_n_1548_);
    return v_res_1553_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(
    mut v_bounded_1554_: *mut leanh::LeanObject,
    mut v_num_1555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = lean_int_mul(v_bounded_1554_, v_num_1555_);
    return v___x_1556_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__neg___redArg___boxed(
    mut v_bounded_1557_: *mut leanh::LeanObject,
    mut v_num_1558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1559_ = l_Std_Time_Internal_Bounded_LE_mul__neg___redArg(v_bounded_1557_, v_num_1558_);
    leanh::lean_dec(v_num_1558_);
    leanh::lean_dec(v_bounded_1557_);
    return v_res_1559_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__neg(
    mut v_n_1560_: *mut leanh::LeanObject,
    mut v_m_1561_: *mut leanh::LeanObject,
    mut v_bounded_1562_: *mut leanh::LeanObject,
    mut v_num_1563_: *mut leanh::LeanObject,
    mut v_h_1564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1565_ = lean_int_mul(v_bounded_1562_, v_num_1563_);
    return v___x_1565_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_mul__neg___boxed(
    mut v_n_1566_: *mut leanh::LeanObject,
    mut v_m_1567_: *mut leanh::LeanObject,
    mut v_bounded_1568_: *mut leanh::LeanObject,
    mut v_num_1569_: *mut leanh::LeanObject,
    mut v_h_1570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1571_ = l_Std_Time_Internal_Bounded_LE_mul__neg(
        v_n_1566_,
        v_m_1567_,
        v_bounded_1568_,
        v_num_1569_,
        v_h_1570_,
    );
    leanh::lean_dec(v_num_1569_);
    leanh::lean_dec(v_bounded_1568_);
    leanh::lean_dec(v_m_1567_);
    leanh::lean_dec(v_n_1566_);
    return v_res_1571_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ediv___redArg(
    mut v_bounded_1572_: *mut leanh::LeanObject,
    mut v_num_1573_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1574_ = lean_int_ediv(v_bounded_1572_, v_num_1573_);
    return v___x_1574_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ediv___redArg___boxed(
    mut v_bounded_1575_: *mut leanh::LeanObject,
    mut v_num_1576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1577_ = l_Std_Time_Internal_Bounded_LE_ediv___redArg(v_bounded_1575_, v_num_1576_);
    leanh::lean_dec(v_num_1576_);
    leanh::lean_dec(v_bounded_1575_);
    return v_res_1577_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ediv(
    mut v_n_1578_: *mut leanh::LeanObject,
    mut v_m_1579_: *mut leanh::LeanObject,
    mut v_bounded_1580_: *mut leanh::LeanObject,
    mut v_num_1581_: *mut leanh::LeanObject,
    mut v_h_1582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1583_ = lean_int_ediv(v_bounded_1580_, v_num_1581_);
    return v___x_1583_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_ediv___boxed(
    mut v_n_1584_: *mut leanh::LeanObject,
    mut v_m_1585_: *mut leanh::LeanObject,
    mut v_bounded_1586_: *mut leanh::LeanObject,
    mut v_num_1587_: *mut leanh::LeanObject,
    mut v_h_1588_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Std_Time_Internal_Bounded_LE_ediv(
        v_n_1584_,
        v_m_1585_,
        v_bounded_1586_,
        v_num_1587_,
        v_h_1588_,
    );
    leanh::lean_dec(v_num_1587_);
    leanh::lean_dec(v_bounded_1586_);
    leanh::lean_dec(v_m_1585_);
    leanh::lean_dec(v_n_1584_);
    return v_res_1589_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_eq(
    mut v_n_1590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_n_1590_);
    return v_n_1590_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_eq___boxed(
    mut v_n_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_Std_Time_Internal_Bounded_LE_eq(v_n_1591_);
    leanh::lean_dec(v_n_1591_);
    return v_res_1592_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expand___redArg(
    mut v_bounded_1593_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1593_);
    return v_bounded_1593_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expand___redArg___boxed(
    mut v_bounded_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = l_Std_Time_Internal_Bounded_LE_expand___redArg(v_bounded_1594_);
    leanh::lean_dec(v_bounded_1594_);
    return v_res_1595_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expand(
    mut v_lo_1596_: *mut leanh::LeanObject,
    mut v_hi_1597_: *mut leanh::LeanObject,
    mut v_nhi_1598_: *mut leanh::LeanObject,
    mut v_nlo_1599_: *mut leanh::LeanObject,
    mut v_bounded_1600_: *mut leanh::LeanObject,
    mut v_h_1601_: *mut leanh::LeanObject,
    mut v_h_u2081_1602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1600_);
    return v_bounded_1600_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expand___boxed(
    mut v_lo_1603_: *mut leanh::LeanObject,
    mut v_hi_1604_: *mut leanh::LeanObject,
    mut v_nhi_1605_: *mut leanh::LeanObject,
    mut v_nlo_1606_: *mut leanh::LeanObject,
    mut v_bounded_1607_: *mut leanh::LeanObject,
    mut v_h_1608_: *mut leanh::LeanObject,
    mut v_h_u2081_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1610_ = l_Std_Time_Internal_Bounded_LE_expand(
        v_lo_1603_,
        v_hi_1604_,
        v_nhi_1605_,
        v_nlo_1606_,
        v_bounded_1607_,
        v_h_1608_,
        v_h_u2081_1609_,
    );
    leanh::lean_dec(v_bounded_1607_);
    leanh::lean_dec(v_nlo_1606_);
    leanh::lean_dec(v_nhi_1605_);
    leanh::lean_dec(v_hi_1604_);
    leanh::lean_dec(v_lo_1603_);
    return v_res_1610_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandTop___redArg(
    mut v_bounded_1611_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1611_);
    return v_bounded_1611_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandTop___redArg___boxed(
    mut v_bounded_1612_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1613_ = l_Std_Time_Internal_Bounded_LE_expandTop___redArg(v_bounded_1612_);
    leanh::lean_dec(v_bounded_1612_);
    return v_res_1613_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandTop(
    mut v_lo_1614_: *mut leanh::LeanObject,
    mut v_hi_1615_: *mut leanh::LeanObject,
    mut v_nhi_1616_: *mut leanh::LeanObject,
    mut v_bounded_1617_: *mut leanh::LeanObject,
    mut v_h_1618_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1617_);
    return v_bounded_1617_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandTop___boxed(
    mut v_lo_1619_: *mut leanh::LeanObject,
    mut v_hi_1620_: *mut leanh::LeanObject,
    mut v_nhi_1621_: *mut leanh::LeanObject,
    mut v_bounded_1622_: *mut leanh::LeanObject,
    mut v_h_1623_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1624_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_Std_Time_Internal_Bounded_LE_expandTop(
        v_lo_1619_,
        v_hi_1620_,
        v_nhi_1621_,
        v_bounded_1622_,
        v_h_1623_,
    );
    leanh::lean_dec(v_bounded_1622_);
    leanh::lean_dec(v_nhi_1621_);
    leanh::lean_dec(v_hi_1620_);
    leanh::lean_dec(v_lo_1619_);
    return v_res_1624_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(
    mut v_bounded_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1625_);
    return v_bounded_1625_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandBottom___redArg___boxed(
    mut v_bounded_1626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1627_ = l_Std_Time_Internal_Bounded_LE_expandBottom___redArg(v_bounded_1626_);
    leanh::lean_dec(v_bounded_1626_);
    return v_res_1627_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandBottom(
    mut v_lo_1628_: *mut leanh::LeanObject,
    mut v_hi_1629_: *mut leanh::LeanObject,
    mut v_nlo_1630_: *mut leanh::LeanObject,
    mut v_bounded_1631_: *mut leanh::LeanObject,
    mut v_h_1632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_bounded_1631_);
    return v_bounded_1631_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_expandBottom___boxed(
    mut v_lo_1633_: *mut leanh::LeanObject,
    mut v_hi_1634_: *mut leanh::LeanObject,
    mut v_nlo_1635_: *mut leanh::LeanObject,
    mut v_bounded_1636_: *mut leanh::LeanObject,
    mut v_h_1637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1638_ = l_Std_Time_Internal_Bounded_LE_expandBottom(
        v_lo_1633_,
        v_hi_1634_,
        v_nlo_1635_,
        v_bounded_1636_,
        v_h_1637_,
    );
    leanh::lean_dec(v_bounded_1636_);
    leanh::lean_dec(v_nlo_1635_);
    leanh::lean_dec(v_hi_1634_);
    leanh::lean_dec(v_lo_1633_);
    return v_res_1638_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_succ___redArg(
    mut v_bounded_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v___x_1641_ = lean_int_add(v_bounded_1639_, v___x_1640_);
    return v___x_1641_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_succ___redArg___boxed(
    mut v_bounded_1642_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1643_ = l_Std_Time_Internal_Bounded_LE_succ___redArg(v_bounded_1642_);
    leanh::lean_dec(v_bounded_1642_);
    return v_res_1643_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_succ(
    mut v_lo_1644_: *mut leanh::LeanObject,
    mut v_hi_1645_: *mut leanh::LeanObject,
    mut v_bounded_1646_: *mut leanh::LeanObject,
    mut v_h_1647_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1648_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0),
        core::ptr::addr_of_mut!(
            l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0_once
        ),
        _init_l_Std_Time_Internal_Bounded_LE_ofNatWrapping___redArg___closed__0,
    );
    v___x_1649_ = lean_int_add(v_bounded_1646_, v___x_1648_);
    return v___x_1649_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_succ___boxed(
    mut v_lo_1650_: *mut leanh::LeanObject,
    mut v_hi_1651_: *mut leanh::LeanObject,
    mut v_bounded_1652_: *mut leanh::LeanObject,
    mut v_h_1653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1654_ =
        l_Std_Time_Internal_Bounded_LE_succ(v_lo_1650_, v_hi_1651_, v_bounded_1652_, v_h_1653_);
    leanh::lean_dec(v_bounded_1652_);
    leanh::lean_dec(v_hi_1651_);
    leanh::lean_dec(v_lo_1650_);
    return v_res_1654_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_abs___redArg(
    mut v_bo_1655_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: u8 = 0;
    v___x_1656_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v___x_1657_ = lean_int_dec_le(v___x_1656_, v_bo_1655_);
    if v___x_1657_ == 0 {
        let mut v_r_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_r_1658_ = lean_int_neg(v_bo_1655_);
        return v_r_1658_;
    } else {
        leanh::lean_inc(v_bo_1655_);
        return v_bo_1655_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_abs___redArg___boxed(
    mut v_bo_1659_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1660_ = l_Std_Time_Internal_Bounded_LE_abs___redArg(v_bo_1659_);
    leanh::lean_dec(v_bo_1659_);
    return v_res_1660_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_abs(
    mut v_i_1661_: *mut leanh::LeanObject,
    mut v_bo_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: u8 = 0;
    v___x_1663_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0_once), _init_l___private_Std_Time_Internal_Bounded_0__Int_tdiv_match__1_splitter___redArg___closed__0);
    v___x_1664_ = lean_int_dec_le(v___x_1663_, v_bo_1662_);
    if v___x_1664_ == 0 {
        let mut v_r_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_r_1665_ = lean_int_neg(v_bo_1662_);
        return v_r_1665_;
    } else {
        leanh::lean_inc(v_bo_1662_);
        return v_bo_1662_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_abs___boxed(
    mut v_i_1666_: *mut leanh::LeanObject,
    mut v_bo_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1668_ = l_Std_Time_Internal_Bounded_LE_abs(v_i_1666_, v_bo_1667_);
    leanh::lean_dec(v_bo_1667_);
    leanh::lean_dec(v_i_1666_);
    return v_res_1668_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_max___redArg(
    mut v_bounded_1669_: *mut leanh::LeanObject,
    mut v_val_1670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1671_: u8 = 0;
    v___x_1671_ = lean_int_dec_le(v_bounded_1669_, v_val_1670_);
    if v___x_1671_ == 0 {
        leanh::lean_inc(v_bounded_1669_);
        return v_bounded_1669_;
    } else {
        leanh::lean_inc(v_val_1670_);
        return v_val_1670_;
    }
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_max___redArg___boxed(
    mut v_bounded_1672_: *mut leanh::LeanObject,
    mut v_val_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_1672_, v_val_1673_);
    leanh::lean_dec(v_val_1673_);
    leanh::lean_dec(v_bounded_1672_);
    return v_res_1674_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_max(
    mut v_n_1675_: *mut leanh::LeanObject,
    mut v_m_1676_: *mut leanh::LeanObject,
    mut v_bounded_1677_: *mut leanh::LeanObject,
    mut v_val_1678_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1679_ = l_Std_Time_Internal_Bounded_LE_max___redArg(v_bounded_1677_, v_val_1678_);
    return v___x_1679_;
}
pub unsafe fn l_Std_Time_Internal_Bounded_LE_max___boxed(
    mut v_n_1680_: *mut leanh::LeanObject,
    mut v_m_1681_: *mut leanh::LeanObject,
    mut v_bounded_1682_: *mut leanh::LeanObject,
    mut v_val_1683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1684_ =
        l_Std_Time_Internal_Bounded_LE_max(v_n_1680_, v_m_1681_, v_bounded_1682_, v_val_1683_);
    leanh::lean_dec(v_val_1683_);
    leanh::lean_dec(v_bounded_1682_);
    leanh::lean_dec(v_m_1681_);
    leanh::lean_dec(v_n_1680_);
    return v_res_1684_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Internal_Bounded(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Ord(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Internal_Bounded(
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
pub unsafe fn initialize_Std_Time_Internal_Bounded(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Ord(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Repr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Ext(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Internal_Bounded(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Std_Time_Internal_Bounded(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Std_Time_Internal_Bounded(builtin);
}
// Lean compiler output
// Module: Init.Data.BitVec.Bitblast
// Imports: Init.Data.Nat.Bitwise.Basic Init.Data.Int.DivMod Init.Data.BitVec.Basic Init.Data.BitVec.Folds Init.BinderPredicates Init.Data.BitVec.Lemmas Init.Data.Nat.Lemmas Init.ByCases Init.Data.BitVec.Bootstrap Init.Data.BitVec.Decidable Init.Data.Int.Pow Init.Data.Nat.Div.Lemmas Init.Data.Nat.Mod Init.Data.Nat.Simproc Init.TacticsExtra
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_land, lean_nat_mod,
    lean_nat_mul, lean_nat_pow, lean_nat_shiftr, lean_nat_sub,
};
use crate::r#gen::Init::BinderPredicates::{
    initialize_Init_BinderPredicates, runtime_initialize_Init_BinderPredicates,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::BitVec::Basic::{
    initialize_Init_Data_BitVec_Basic, l_BitVec_append___redArg, l_BitVec_extractLsb_x27___redArg,
    l_BitVec_setWidth, l_BitVec_shiftConcat, l_BitVec_shiftLeft, l_BitVec_sshiftRight,
    l_BitVec_twoPow, runtime_initialize_Init_Data_BitVec_Basic,
};
use crate::r#gen::Init::Data::BitVec::BasicAux::{l_BitVec_add, l_BitVec_sub};
use crate::r#gen::Init::Data::BitVec::Bootstrap::{
    initialize_Init_Data_BitVec_Bootstrap, runtime_initialize_Init_Data_BitVec_Bootstrap,
};
use crate::r#gen::Init::Data::BitVec::Decidable::{
    initialize_Init_Data_BitVec_Decidable, runtime_initialize_Init_Data_BitVec_Decidable,
};
use crate::r#gen::Init::Data::BitVec::Folds::{
    initialize_Init_Data_BitVec_Folds, l_BitVec_iunfoldr___redArg,
    runtime_initialize_Init_Data_BitVec_Folds,
};
use crate::r#gen::Init::Data::BitVec::Lemmas::{
    initialize_Init_Data_BitVec_Lemmas, runtime_initialize_Init_Data_BitVec_Lemmas,
};
use crate::r#gen::Init::Data::Bool::l_Bool_toNat;
use crate::r#gen::Init::Data::Int::DivMod::{
    initialize_Init_Data_Int_DivMod, runtime_initialize_Init_Data_Int_DivMod,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Bitwise::Basic::{
    initialize_Init_Data_Nat_Bitwise_Basic, l_Nat_testBit,
    runtime_initialize_Init_Data_Nat_Bitwise_Basic,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Mod::{
    initialize_Init_Data_Nat_Mod, runtime_initialize_Init_Data_Nat_Mod,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Prelude::l_BitVec_ofNat;
use crate::r#gen::Init::TacticsExtra::{
    initialize_Init_TacticsExtra, runtime_initialize_Init_TacticsExtra,
};
static mut l_BitVec_extractAndExtend___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_BitVec_extractAndExtend___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l_Bool_atLeastTwo(mut v_a_838_: u8, mut v_b_839_: u8, mut v_c_840_: u8) -> u8 {
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_a_838_ == 0 {
                    state = 1;
                    continue;
                } else {
                    if v_b_839_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        return v_b_839_;
                    }
                }
            }
            1 => {
                if v_a_838_ == 0 {
                    if v_b_839_ == 0 {
                        return v_b_839_;
                    } else {
                        return v_c_840_;
                    }
                } else {
                    if v_c_840_ == 0 {
                        if v_b_839_ == 0 {
                            return v_b_839_;
                        } else {
                            return v_c_840_;
                        }
                    } else {
                        return v_c_840_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Bool_atLeastTwo___boxed(
    mut v_a_842_: *mut leanh::LeanObject,
    mut v_b_843_: *mut leanh::LeanObject,
    mut v_c_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_boxed_845_: u8 = 0;
    let mut v_b_boxed_846_: u8 = 0;
    let mut v_c_boxed_847_: u8 = 0;
    let mut v_res_848_: u8 = 0;
    let mut v_r_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_boxed_845_ = (leanh::lean_unbox(v_a_842_) as u8);
    v_b_boxed_846_ = (leanh::lean_unbox(v_b_843_) as u8);
    v_c_boxed_847_ = (leanh::lean_unbox(v_c_844_) as u8);
    v_res_848_ = l_Bool_atLeastTwo(v_a_boxed_845_, v_b_boxed_846_, v_c_boxed_847_);
    v_r_849_ = leanh::lean_box((v_res_848_) as usize);
    return v_r_849_;
}
pub unsafe fn l_BitVec_carry___redArg(
    mut v_i_850_: *mut leanh::LeanObject,
    mut v_x_851_: *mut leanh::LeanObject,
    mut v_y_852_: *mut leanh::LeanObject,
    mut v_c_853_: u8,
) -> u8 {
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: u8 = 0;
    v___x_854_ = leanh::lean_unsigned_to_nat(2);
    v___x_855_ = lean_nat_pow(v___x_854_, v_i_850_);
    v___x_856_ = lean_nat_mod(v_x_851_, v___x_855_);
    v___x_857_ = lean_nat_mod(v_y_852_, v___x_855_);
    v___x_858_ = lean_nat_add(v___x_856_, v___x_857_);
    leanh::lean_dec(v___x_857_);
    leanh::lean_dec(v___x_856_);
    v___x_859_ = l_Bool_toNat(v_c_853_);
    v___x_860_ = lean_nat_add(v___x_858_, v___x_859_);
    leanh::lean_dec(v___x_859_);
    leanh::lean_dec(v___x_858_);
    v___x_861_ = lean_nat_dec_le(v___x_855_, v___x_860_);
    leanh::lean_dec(v___x_860_);
    leanh::lean_dec(v___x_855_);
    return v___x_861_;
}
pub unsafe fn l_BitVec_carry___redArg___boxed(
    mut v_i_862_: *mut leanh::LeanObject,
    mut v_x_863_: *mut leanh::LeanObject,
    mut v_y_864_: *mut leanh::LeanObject,
    mut v_c_865_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_866_: u8 = 0;
    let mut v_res_867_: u8 = 0;
    let mut v_r_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_866_ = (leanh::lean_unbox(v_c_865_) as u8);
    v_res_867_ = l_BitVec_carry___redArg(v_i_862_, v_x_863_, v_y_864_, v_c_boxed_866_);
    leanh::lean_dec(v_y_864_);
    leanh::lean_dec(v_x_863_);
    leanh::lean_dec(v_i_862_);
    v_r_868_ = leanh::lean_box((v_res_867_) as usize);
    return v_r_868_;
}
pub unsafe fn l_BitVec_carry(
    mut v_w_869_: *mut leanh::LeanObject,
    mut v_i_870_: *mut leanh::LeanObject,
    mut v_x_871_: *mut leanh::LeanObject,
    mut v_y_872_: *mut leanh::LeanObject,
    mut v_c_873_: u8,
) -> u8 {
    let mut v___x_874_: u8 = 0;
    v___x_874_ = l_BitVec_carry___redArg(v_i_870_, v_x_871_, v_y_872_, v_c_873_);
    return v___x_874_;
}
pub unsafe fn l_BitVec_carry___boxed(
    mut v_w_875_: *mut leanh::LeanObject,
    mut v_i_876_: *mut leanh::LeanObject,
    mut v_x_877_: *mut leanh::LeanObject,
    mut v_y_878_: *mut leanh::LeanObject,
    mut v_c_879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_880_: u8 = 0;
    let mut v_res_881_: u8 = 0;
    let mut v_r_882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_880_ = (leanh::lean_unbox(v_c_879_) as u8);
    v_res_881_ = l_BitVec_carry(v_w_875_, v_i_876_, v_x_877_, v_y_878_, v_c_boxed_880_);
    leanh::lean_dec(v_y_878_);
    leanh::lean_dec(v_x_877_);
    leanh::lean_dec(v_i_876_);
    leanh::lean_dec(v_w_875_);
    v_r_882_ = leanh::lean_box((v_res_881_) as usize);
    return v_r_882_;
}
pub unsafe fn l_BitVec_adcb(
    mut v_x_883_: u8,
    mut v_y_884_: u8,
    mut v_c_885_: u8,
) -> *mut leanh::LeanObject {
    let mut v___y_887_: u8 = 0;
    let mut v___x_888_: u8 = 0;
    let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_893_: u8 = 0;
    let mut v___x_894_: u8 = 0;
    let mut v___x_895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_899_: u8 = 0;
    let mut v___y_900_: u8 = 0;
    let mut v___y_902_: u8 = 0;
    let mut v___x_903_: u8 = 0;
    let mut v___y_905_: u8 = 0;
    let mut v___x_906_: u8 = 0;
    let mut v___y_908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_x_883_ == 0 {
                    state = 7;
                    continue;
                } else {
                    if v_y_884_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___y_908_ = v_y_884_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_888_ = 1;
                v___x_889_ = leanh::lean_box((v___y_887_) as usize);
                v___x_890_ = leanh::lean_box((v___x_888_) as usize);
                v___x_891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_891_, 0, v___x_889_);
                leanh::lean_ctor_set(v___x_891_, 1, v___x_890_);
                return v___x_891_;
            }
            2 => {
                v___x_894_ = 0;
                v___x_895_ = leanh::lean_box((v___y_893_) as usize);
                v___x_896_ = leanh::lean_box((v___x_894_) as usize);
                v___x_897_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_897_, 0, v___x_895_);
                leanh::lean_ctor_set(v___x_897_, 1, v___x_896_);
                return v___x_897_;
            }
            3 => {
                if v_x_883_ == 0 {
                    if v___y_900_ == 0 {
                        v___y_893_ = v___y_899_;
                        state = 2;
                        continue;
                    } else {
                        v___y_887_ = v___y_899_;
                        state = 1;
                        continue;
                    }
                } else {
                    if v___y_900_ == 0 {
                        v___y_887_ = v___y_899_;
                        state = 1;
                        continue;
                    } else {
                        v___y_893_ = v___y_899_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_903_ = 1;
                v___y_899_ = v___y_902_;
                v___y_900_ = v___x_903_;
                state = 3;
                continue;
            }
            5 => {
                v___x_906_ = 0;
                v___y_899_ = v___y_905_;
                v___y_900_ = v___x_906_;
                state = 3;
                continue;
            }
            6 => {
                if v_y_884_ == 0 {
                    if v_c_885_ == 0 {
                        v___y_905_ = v___y_908_;
                        state = 5;
                        continue;
                    } else {
                        v___y_902_ = v___y_908_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_c_885_ == 0 {
                        v___y_902_ = v___y_908_;
                        state = 4;
                        continue;
                    } else {
                        v___y_905_ = v___y_908_;
                        state = 5;
                        continue;
                    }
                }
            }
            7 => {
                if v_x_883_ == 0 {
                    if v_y_884_ == 0 {
                        v___y_908_ = v_y_884_;
                        state = 6;
                        continue;
                    } else {
                        v___y_908_ = v_c_885_;
                        state = 6;
                        continue;
                    }
                } else {
                    if v_c_885_ == 0 {
                        if v_y_884_ == 0 {
                            v___y_908_ = v_y_884_;
                            state = 6;
                            continue;
                        } else {
                            v___y_908_ = v_c_885_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v___y_908_ = v_c_885_;
                        state = 6;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_adcb___boxed(
    mut v_x_910_: *mut leanh::LeanObject,
    mut v_y_911_: *mut leanh::LeanObject,
    mut v_c_912_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_913_: u8 = 0;
    let mut v_y_boxed_914_: u8 = 0;
    let mut v_c_boxed_915_: u8 = 0;
    let mut v_res_916_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_913_ = (leanh::lean_unbox(v_x_910_) as u8);
    v_y_boxed_914_ = (leanh::lean_unbox(v_y_911_) as u8);
    v_c_boxed_915_ = (leanh::lean_unbox(v_c_912_) as u8);
    v_res_916_ = l_BitVec_adcb(v_x_boxed_913_, v_y_boxed_914_, v_c_boxed_915_);
    return v_res_916_;
}
pub unsafe fn l_BitVec_adc___lam__0(
    mut v_x_917_: *mut leanh::LeanObject,
    mut v_y_918_: *mut leanh::LeanObject,
    mut v_i_919_: *mut leanh::LeanObject,
    mut v_c_920_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: u8 = 0;
    let mut v___x_923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l_Nat_testBit(v_x_917_, v_i_919_);
    v___x_922_ = l_Nat_testBit(v_y_918_, v_i_919_);
    v___x_923_ = l_BitVec_adcb(v___x_921_, v___x_922_, v_c_920_);
    return v___x_923_;
}
pub unsafe fn l_BitVec_adc___lam__0___boxed(
    mut v_x_924_: *mut leanh::LeanObject,
    mut v_y_925_: *mut leanh::LeanObject,
    mut v_i_926_: *mut leanh::LeanObject,
    mut v_c_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_c_boxed_928_: u8 = 0;
    let mut v_res_929_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_928_ = (leanh::lean_unbox(v_c_927_) as u8);
    v_res_929_ = l_BitVec_adc___lam__0(v_x_924_, v_y_925_, v_i_926_, v_c_boxed_928_);
    leanh::lean_dec(v_i_926_);
    leanh::lean_dec(v_y_925_);
    leanh::lean_dec(v_x_924_);
    return v_res_929_;
}
pub unsafe fn l_BitVec_adc(
    mut v_w_930_: *mut leanh::LeanObject,
    mut v_x_931_: *mut leanh::LeanObject,
    mut v_y_932_: *mut leanh::LeanObject,
    mut v_s_933_: u8,
) -> *mut leanh::LeanObject {
    let mut v___f_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_934_ = leanh::lean_alloc_closure(
        l_BitVec_adc___lam__0___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_934_, 0, v_x_931_);
    leanh::lean_closure_set(v___f_934_, 1, v_y_932_);
    v___x_935_ = leanh::lean_box((v_s_933_) as usize);
    v___x_936_ = l_BitVec_iunfoldr___redArg(v_w_930_, v___f_934_, v___x_935_);
    return v___x_936_;
}
pub unsafe fn l_BitVec_adc___boxed(
    mut v_w_937_: *mut leanh::LeanObject,
    mut v_x_938_: *mut leanh::LeanObject,
    mut v_y_939_: *mut leanh::LeanObject,
    mut v_s_940_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_s_boxed_941_: u8 = 0;
    let mut v_res_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_s_boxed_941_ = (leanh::lean_unbox(v_s_940_) as u8);
    v_res_942_ = l_BitVec_adc(v_w_937_, v_x_938_, v_y_939_, v_s_boxed_941_);
    leanh::lean_dec(v_w_937_);
    return v_res_942_;
}
pub unsafe fn l_BitVec_mulRec(
    mut v_w_943_: *mut leanh::LeanObject,
    mut v_x_944_: *mut leanh::LeanObject,
    mut v_y_945_: *mut leanh::LeanObject,
    mut v_s_946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_950_: u8 = 0;
    let mut v_one_951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v___x_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_955_ = l_Nat_testBit(v_y_945_, v_s_946_);
                if v___x_955_ == 0 {
                    v___x_956_ = leanh::lean_unsigned_to_nat(0);
                    v___x_957_ = l_BitVec_ofNat(v_w_943_, v___x_956_);
                    v___y_948_ = v___x_957_;
                    state = 1;
                    continue;
                } else {
                    v___x_958_ = l_BitVec_shiftLeft(v_w_943_, v_x_944_, v_s_946_);
                    v___y_948_ = v___x_958_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_zero_949_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_950_ = lean_nat_dec_eq(v_s_946_, v_zero_949_);
                if v_isZero_950_ == 1 {
                    return v___y_948_;
                } else {
                    v_one_951_ = leanh::lean_unsigned_to_nat(1);
                    v_n_952_ = lean_nat_sub(v_s_946_, v_one_951_);
                    v___x_953_ = l_BitVec_mulRec(v_w_943_, v_x_944_, v_y_945_, v_n_952_);
                    leanh::lean_dec(v_n_952_);
                    v___x_954_ = l_BitVec_add(v_w_943_, v___x_953_, v___y_948_);
                    leanh::lean_dec(v___y_948_);
                    leanh::lean_dec(v___x_953_);
                    return v___x_954_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_mulRec___boxed(
    mut v_w_959_: *mut leanh::LeanObject,
    mut v_x_960_: *mut leanh::LeanObject,
    mut v_y_961_: *mut leanh::LeanObject,
    mut v_s_962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_963_ = l_BitVec_mulRec(v_w_959_, v_x_960_, v_y_961_, v_s_962_);
    leanh::lean_dec(v_s_962_);
    leanh::lean_dec(v_y_961_);
    leanh::lean_dec(v_x_960_);
    leanh::lean_dec(v_w_959_);
    return v_res_963_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(
    mut v_s_964_: *mut leanh::LeanObject,
    mut v_h__1_965_: *mut leanh::LeanObject,
    mut v_h__2_966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_968_: u8 = 0;
    v_zero_967_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_968_ = lean_nat_dec_eq(v_s_964_, v_zero_967_);
    if v_isZero_968_ == 1 {
        let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_966_);
        v___x_969_ = leanh::lean_box(0);
        v___x_970_ = leanh::lean_apply_1(v_h__1_965_, v___x_969_);
        return v___x_970_;
    } else {
        let mut v_one_971_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_972_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_965_);
        v_one_971_ = leanh::lean_unsigned_to_nat(1);
        v_n_972_ = lean_nat_sub(v_s_964_, v_one_971_);
        v___x_973_ = leanh::lean_apply_1(v_h__2_966_, v_n_972_);
        return v___x_973_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg___boxed(
    mut v_s_974_: *mut leanh::LeanObject,
    mut v_h__1_975_: *mut leanh::LeanObject,
    mut v_h__2_976_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_977_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_977_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___redArg(
        v_s_974_,
        v_h__1_975_,
        v_h__2_976_,
    );
    leanh::lean_dec(v_s_974_);
    return v_res_977_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(
    mut v_motive_978_: *mut leanh::LeanObject,
    mut v_s_979_: *mut leanh::LeanObject,
    mut v_h__1_980_: *mut leanh::LeanObject,
    mut v_h__2_981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_983_: u8 = 0;
    v_zero_982_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_983_ = lean_nat_dec_eq(v_s_979_, v_zero_982_);
    if v_isZero_983_ == 1 {
        let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_981_);
        v___x_984_ = leanh::lean_box(0);
        v___x_985_ = leanh::lean_apply_1(v_h__1_980_, v___x_984_);
        return v___x_985_;
    } else {
        let mut v_one_986_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_987_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_988_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_980_);
        v_one_986_ = leanh::lean_unsigned_to_nat(1);
        v_n_987_ = lean_nat_sub(v_s_979_, v_one_986_);
        v___x_988_ = leanh::lean_apply_1(v_h__2_981_, v_n_987_);
        return v___x_988_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter___boxed(
    mut v_motive_989_: *mut leanh::LeanObject,
    mut v_s_990_: *mut leanh::LeanObject,
    mut v_h__1_991_: *mut leanh::LeanObject,
    mut v_h__2_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_993_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_mulRec_match__1_splitter(
        v_motive_989_,
        v_s_990_,
        v_h__1_991_,
        v_h__2_992_,
    );
    leanh::lean_dec(v_s_990_);
    return v_res_993_;
}
pub unsafe fn l_BitVec_shiftLeftRec(
    mut v_w_u2081_994_: *mut leanh::LeanObject,
    mut v_w_u2082_995_: *mut leanh::LeanObject,
    mut v_x_996_: *mut leanh::LeanObject,
    mut v_y_997_: *mut leanh::LeanObject,
    mut v_n_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shiftAmt_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1002_: u8 = 0;
    v___x_999_ = l_BitVec_twoPow(v_w_u2082_995_, v_n_998_);
    v_shiftAmt_1000_ = lean_nat_land(v_y_997_, v___x_999_);
    leanh::lean_dec(v___x_999_);
    v_zero_1001_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1002_ = lean_nat_dec_eq(v_n_998_, v_zero_1001_);
    if v_isZero_1002_ == 1 {
        let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1003_ = l_BitVec_shiftLeft(v_w_u2081_994_, v_x_996_, v_shiftAmt_1000_);
        leanh::lean_dec(v_shiftAmt_1000_);
        return v___x_1003_;
    } else {
        let mut v_one_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_1004_ = leanh::lean_unsigned_to_nat(1);
        v_n_1005_ = lean_nat_sub(v_n_998_, v_one_1004_);
        v___x_1006_ = l_BitVec_shiftLeftRec(
            v_w_u2081_994_,
            v_w_u2082_995_,
            v_x_996_,
            v_y_997_,
            v_n_1005_,
        );
        leanh::lean_dec(v_n_1005_);
        v___x_1007_ = l_BitVec_shiftLeft(v_w_u2081_994_, v___x_1006_, v_shiftAmt_1000_);
        leanh::lean_dec(v_shiftAmt_1000_);
        leanh::lean_dec(v___x_1006_);
        return v___x_1007_;
    }
}
pub unsafe fn l_BitVec_shiftLeftRec___boxed(
    mut v_w_u2081_1008_: *mut leanh::LeanObject,
    mut v_w_u2082_1009_: *mut leanh::LeanObject,
    mut v_x_1010_: *mut leanh::LeanObject,
    mut v_y_1011_: *mut leanh::LeanObject,
    mut v_n_1012_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1013_ = l_BitVec_shiftLeftRec(
        v_w_u2081_1008_,
        v_w_u2082_1009_,
        v_x_1010_,
        v_y_1011_,
        v_n_1012_,
    );
    leanh::lean_dec(v_n_1012_);
    leanh::lean_dec(v_y_1011_);
    leanh::lean_dec(v_x_1010_);
    leanh::lean_dec(v_w_u2082_1009_);
    leanh::lean_dec(v_w_u2081_1008_);
    return v_res_1013_;
}
pub unsafe fn l_BitVec_DivModState_init(
    mut v_w_1014_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1015_ = leanh::lean_unsigned_to_nat(0);
    v___x_1016_ = l_BitVec_ofNat(v_w_1014_, v___x_1015_);
    leanh::lean_inc(v___x_1016_);
    v___x_1017_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1017_, 0, v_w_1014_);
    leanh::lean_ctor_set(v___x_1017_, 1, v___x_1015_);
    leanh::lean_ctor_set(v___x_1017_, 2, v___x_1016_);
    leanh::lean_ctor_set(v___x_1017_, 3, v___x_1016_);
    return v___x_1017_;
}
pub unsafe fn l_BitVec_divSubtractShift(
    mut v_w_1018_: *mut leanh::LeanObject,
    mut v_args_1019_: *mut leanh::LeanObject,
    mut v_qr_1020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wn_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wr_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_q_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wn_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_wr_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: u8 = 0;
    let mut v_r_x27_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: u8 = 0;
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: u8 = 0;
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1047_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_n_1021_ = leanh::lean_ctor_get(v_args_1019_, 0);
                v_d_1022_ = leanh::lean_ctor_get(v_args_1019_, 1);
                v_wn_1023_ = leanh::lean_ctor_get(v_qr_1020_, 0);
                v_wr_1024_ = leanh::lean_ctor_get(v_qr_1020_, 1);
                v_q_1025_ = leanh::lean_ctor_get(v_qr_1020_, 2);
                v_r_1026_ = leanh::lean_ctor_get(v_qr_1020_, 3);
                v_isSharedCheck_1047_ = (!leanh::lean_is_exclusive(v_qr_1020_)) as u8;
                if v_isSharedCheck_1047_ == 0 {
                    v___x_1028_ = v_qr_1020_;
                    v_isShared_1029_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_r_1026_);
                    leanh::lean_inc(v_q_1025_);
                    leanh::lean_inc(v_wr_1024_);
                    leanh::lean_inc(v_wn_1023_);
                    leanh::lean_dec(v_qr_1020_);
                    v___x_1028_ = leanh::lean_box(0);
                    v_isShared_1029_ = v_isSharedCheck_1047_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1030_ = leanh::lean_unsigned_to_nat(1);
                v_wn_1031_ = lean_nat_sub(v_wn_1023_, v___x_1030_);
                leanh::lean_dec(v_wn_1023_);
                v_wr_1032_ = lean_nat_add(v_wr_1024_, v___x_1030_);
                leanh::lean_dec(v_wr_1024_);
                v___x_1033_ = l_Nat_testBit(v_n_1021_, v_wn_1031_);
                v_r_x27_1034_ = l_BitVec_shiftConcat(v_w_1018_, v_r_1026_, v___x_1033_);
                leanh::lean_dec(v_r_1026_);
                v___x_1035_ = lean_nat_dec_lt(v_r_x27_1034_, v_d_1022_);
                if v___x_1035_ == 0 {
                    v___x_1036_ = 1;
                    v___x_1037_ = l_BitVec_shiftConcat(v_w_1018_, v_q_1025_, v___x_1036_);
                    leanh::lean_dec(v_q_1025_);
                    v___x_1038_ = l_BitVec_sub(v_w_1018_, v_r_x27_1034_, v_d_1022_);
                    leanh::lean_dec(v_r_x27_1034_);
                    if v_isShared_1029_ == 0 {
                        leanh::lean_ctor_set(v___x_1028_, 3, v___x_1038_);
                        leanh::lean_ctor_set(v___x_1028_, 2, v___x_1037_);
                        leanh::lean_ctor_set(v___x_1028_, 1, v_wr_1032_);
                        leanh::lean_ctor_set(v___x_1028_, 0, v_wn_1031_);
                        v___x_1040_ = v___x_1028_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1041_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_wn_1031_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_wr_1032_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 2, v___x_1037_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 3, v___x_1038_);
                        v___x_1040_ = v_reuseFailAlloc_1041_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1042_ = 0;
                    v___x_1043_ = l_BitVec_shiftConcat(v_w_1018_, v_q_1025_, v___x_1042_);
                    leanh::lean_dec(v_q_1025_);
                    if v_isShared_1029_ == 0 {
                        leanh::lean_ctor_set(v___x_1028_, 3, v_r_x27_1034_);
                        leanh::lean_ctor_set(v___x_1028_, 2, v___x_1043_);
                        leanh::lean_ctor_set(v___x_1028_, 1, v_wr_1032_);
                        leanh::lean_ctor_set(v___x_1028_, 0, v_wn_1031_);
                        v___x_1045_ = v___x_1028_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1046_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 0, v_wn_1031_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 1, v_wr_1032_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 2, v___x_1043_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1046_, 3, v_r_x27_1034_);
                        v___x_1045_ = v_reuseFailAlloc_1046_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1040_;
            }
            3 => {
                return v___x_1045_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_divSubtractShift___boxed(
    mut v_w_1048_: *mut leanh::LeanObject,
    mut v_args_1049_: *mut leanh::LeanObject,
    mut v_qr_1050_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1051_ = l_BitVec_divSubtractShift(v_w_1048_, v_args_1049_, v_qr_1050_);
    leanh::lean_dec_ref(v_args_1049_);
    leanh::lean_dec(v_w_1048_);
    return v_res_1051_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___redArg(
    mut v_args_1052_: *mut leanh::LeanObject,
    mut v_h__1_1053_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_1054_ = leanh::lean_ctor_get(v_args_1052_, 0);
    leanh::lean_inc(v_n_1054_);
    v_d_1055_ = leanh::lean_ctor_get(v_args_1052_, 1);
    leanh::lean_inc(v_d_1055_);
    leanh::lean_dec_ref(v_args_1052_);
    v___x_1056_ = leanh::lean_apply_2(v_h__1_1053_, v_n_1054_, v_d_1055_);
    return v___x_1056_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(
    mut v_w_1057_: *mut leanh::LeanObject,
    mut v_motive_1058_: *mut leanh::LeanObject,
    mut v_args_1059_: *mut leanh::LeanObject,
    mut v_h__1_1060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_n_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_d_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_n_1061_ = leanh::lean_ctor_get(v_args_1059_, 0);
    leanh::lean_inc(v_n_1061_);
    v_d_1062_ = leanh::lean_ctor_get(v_args_1059_, 1);
    leanh::lean_inc(v_d_1062_);
    leanh::lean_dec_ref(v_args_1059_);
    v___x_1063_ = leanh::lean_apply_2(v_h__1_1060_, v_n_1061_, v_d_1062_);
    return v___x_1063_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter___boxed(
    mut v_w_1064_: *mut leanh::LeanObject,
    mut v_motive_1065_: *mut leanh::LeanObject,
    mut v_args_1066_: *mut leanh::LeanObject,
    mut v_h__1_1067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_divSubtractShift_match__1_splitter(
            v_w_1064_,
            v_motive_1065_,
            v_args_1066_,
            v_h__1_1067_,
        );
    leanh::lean_dec(v_w_1064_);
    return v_res_1068_;
}
pub unsafe fn l_BitVec_divRec(
    mut v_w_1069_: *mut leanh::LeanObject,
    mut v_m_1070_: *mut leanh::LeanObject,
    mut v_args_1071_: *mut leanh::LeanObject,
    mut v_qr_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1074_: u8 = 0;
    let mut v_one_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1073_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1074_ = lean_nat_dec_eq(v_m_1070_, v_zero_1073_);
                if v_isZero_1074_ == 1 {
                    leanh::lean_dec(v_m_1070_);
                    return v_qr_1072_;
                } else {
                    v_one_1075_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1076_ = lean_nat_sub(v_m_1070_, v_one_1075_);
                    leanh::lean_dec(v_m_1070_);
                    v___x_1077_ = l_BitVec_divSubtractShift(v_w_1069_, v_args_1071_, v_qr_1072_);
                    v_m_1070_ = v_n_1076_;
                    v_qr_1072_ = v___x_1077_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_divRec___boxed(
    mut v_w_1079_: *mut leanh::LeanObject,
    mut v_m_1080_: *mut leanh::LeanObject,
    mut v_args_1081_: *mut leanh::LeanObject,
    mut v_qr_1082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ = l_BitVec_divRec(v_w_1079_, v_m_1080_, v_args_1081_, v_qr_1082_);
    leanh::lean_dec_ref(v_args_1081_);
    leanh::lean_dec(v_w_1079_);
    return v_res_1083_;
}
pub unsafe fn l_BitVec_sshiftRightRec(
    mut v_w_u2081_1084_: *mut leanh::LeanObject,
    mut v_w_u2082_1085_: *mut leanh::LeanObject,
    mut v_x_1086_: *mut leanh::LeanObject,
    mut v_y_1087_: *mut leanh::LeanObject,
    mut v_n_1088_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shiftAmt_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1092_: u8 = 0;
    v___x_1089_ = l_BitVec_twoPow(v_w_u2082_1085_, v_n_1088_);
    v_shiftAmt_1090_ = lean_nat_land(v_y_1087_, v___x_1089_);
    leanh::lean_dec(v___x_1089_);
    v_zero_1091_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1092_ = lean_nat_dec_eq(v_n_1088_, v_zero_1091_);
    if v_isZero_1092_ == 1 {
        let mut v___x_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1093_ = l_BitVec_sshiftRight(v_w_u2081_1084_, v_x_1086_, v_shiftAmt_1090_);
        leanh::lean_dec(v_shiftAmt_1090_);
        return v___x_1093_;
    } else {
        let mut v_one_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_1094_ = leanh::lean_unsigned_to_nat(1);
        v_n_1095_ = lean_nat_sub(v_n_1088_, v_one_1094_);
        v___x_1096_ = l_BitVec_sshiftRightRec(
            v_w_u2081_1084_,
            v_w_u2082_1085_,
            v_x_1086_,
            v_y_1087_,
            v_n_1095_,
        );
        leanh::lean_dec(v_n_1095_);
        v___x_1097_ = l_BitVec_sshiftRight(v_w_u2081_1084_, v___x_1096_, v_shiftAmt_1090_);
        leanh::lean_dec(v_shiftAmt_1090_);
        return v___x_1097_;
    }
}
pub unsafe fn l_BitVec_sshiftRightRec___boxed(
    mut v_w_u2081_1098_: *mut leanh::LeanObject,
    mut v_w_u2082_1099_: *mut leanh::LeanObject,
    mut v_x_1100_: *mut leanh::LeanObject,
    mut v_y_1101_: *mut leanh::LeanObject,
    mut v_n_1102_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_BitVec_sshiftRightRec(
        v_w_u2081_1098_,
        v_w_u2082_1099_,
        v_x_1100_,
        v_y_1101_,
        v_n_1102_,
    );
    leanh::lean_dec(v_n_1102_);
    leanh::lean_dec(v_y_1101_);
    leanh::lean_dec(v_w_u2082_1099_);
    leanh::lean_dec(v_w_u2081_1098_);
    return v_res_1103_;
}
pub unsafe fn l_BitVec_ushiftRightRec___redArg(
    mut v_w_u2082_1104_: *mut leanh::LeanObject,
    mut v_x_1105_: *mut leanh::LeanObject,
    mut v_y_1106_: *mut leanh::LeanObject,
    mut v_n_1107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_shiftAmt_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1111_: u8 = 0;
    v___x_1108_ = l_BitVec_twoPow(v_w_u2082_1104_, v_n_1107_);
    v_shiftAmt_1109_ = lean_nat_land(v_y_1106_, v___x_1108_);
    leanh::lean_dec(v___x_1108_);
    v_zero_1110_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1111_ = lean_nat_dec_eq(v_n_1107_, v_zero_1110_);
    if v_isZero_1111_ == 1 {
        let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1112_ = lean_nat_shiftr(v_x_1105_, v_shiftAmt_1109_);
        leanh::lean_dec(v_shiftAmt_1109_);
        return v___x_1112_;
    } else {
        let mut v_one_1113_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_one_1113_ = leanh::lean_unsigned_to_nat(1);
        v_n_1114_ = lean_nat_sub(v_n_1107_, v_one_1113_);
        v___x_1115_ =
            l_BitVec_ushiftRightRec___redArg(v_w_u2082_1104_, v_x_1105_, v_y_1106_, v_n_1114_);
        leanh::lean_dec(v_n_1114_);
        v___x_1116_ = lean_nat_shiftr(v___x_1115_, v_shiftAmt_1109_);
        leanh::lean_dec(v_shiftAmt_1109_);
        leanh::lean_dec(v___x_1115_);
        return v___x_1116_;
    }
}
pub unsafe fn l_BitVec_ushiftRightRec___redArg___boxed(
    mut v_w_u2082_1117_: *mut leanh::LeanObject,
    mut v_x_1118_: *mut leanh::LeanObject,
    mut v_y_1119_: *mut leanh::LeanObject,
    mut v_n_1120_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1121_ =
        l_BitVec_ushiftRightRec___redArg(v_w_u2082_1117_, v_x_1118_, v_y_1119_, v_n_1120_);
    leanh::lean_dec(v_n_1120_);
    leanh::lean_dec(v_y_1119_);
    leanh::lean_dec(v_x_1118_);
    leanh::lean_dec(v_w_u2082_1117_);
    return v_res_1121_;
}
pub unsafe fn l_BitVec_ushiftRightRec(
    mut v_w_u2081_1122_: *mut leanh::LeanObject,
    mut v_w_u2082_1123_: *mut leanh::LeanObject,
    mut v_x_1124_: *mut leanh::LeanObject,
    mut v_y_1125_: *mut leanh::LeanObject,
    mut v_n_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ =
        l_BitVec_ushiftRightRec___redArg(v_w_u2082_1123_, v_x_1124_, v_y_1125_, v_n_1126_);
    return v___x_1127_;
}
pub unsafe fn l_BitVec_ushiftRightRec___boxed(
    mut v_w_u2081_1128_: *mut leanh::LeanObject,
    mut v_w_u2082_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
    mut v_y_1131_: *mut leanh::LeanObject,
    mut v_n_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1133_ = l_BitVec_ushiftRightRec(
        v_w_u2081_1128_,
        v_w_u2082_1129_,
        v_x_1130_,
        v_y_1131_,
        v_n_1132_,
    );
    leanh::lean_dec(v_n_1132_);
    leanh::lean_dec(v_y_1131_);
    leanh::lean_dec(v_x_1130_);
    leanh::lean_dec(v_w_u2082_1129_);
    leanh::lean_dec(v_w_u2081_1128_);
    return v_res_1133_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(
    mut v_x_1134_: u8,
    mut v_x_1135_: u8,
    mut v_h__1_1136_: *mut leanh::LeanObject,
    mut v_h__2_1137_: *mut leanh::LeanObject,
    mut v_h__3_1138_: *mut leanh::LeanObject,
    mut v_h__4_1139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1134_ == 0 {
        leanh::lean_dec(v_h__4_1139_);
        leanh::lean_dec(v_h__3_1138_);
        if v_x_1135_ == 0 {
            let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1137_);
            v___x_1140_ = leanh::lean_box(0);
            v___x_1141_ = leanh::lean_apply_1(v_h__1_1136_, v___x_1140_);
            return v___x_1141_;
        } else {
            let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1136_);
            v___x_1142_ = leanh::lean_box(0);
            v___x_1143_ = leanh::lean_apply_1(v_h__2_1137_, v___x_1142_);
            return v___x_1143_;
        }
    } else {
        leanh::lean_dec(v_h__2_1137_);
        leanh::lean_dec(v_h__1_1136_);
        if v_x_1135_ == 0 {
            let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1139_);
            v___x_1144_ = leanh::lean_box(0);
            v___x_1145_ = leanh::lean_apply_1(v_h__3_1138_, v___x_1144_);
            return v___x_1145_;
        } else {
            let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1138_);
            v___x_1146_ = leanh::lean_box(0);
            v___x_1147_ = leanh::lean_apply_1(v_h__4_1139_, v___x_1146_);
            return v___x_1147_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg___boxed(
    mut v_x_1148_: *mut leanh::LeanObject,
    mut v_x_1149_: *mut leanh::LeanObject,
    mut v_h__1_1150_: *mut leanh::LeanObject,
    mut v_h__2_1151_: *mut leanh::LeanObject,
    mut v_h__3_1152_: *mut leanh::LeanObject,
    mut v_h__4_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_50__boxed_1154_: u8 = 0;
    let mut v_x_51__boxed_1155_: u8 = 0;
    let mut v_res_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_50__boxed_1154_ = (leanh::lean_unbox(v_x_1148_) as u8);
    v_x_51__boxed_1155_ = (leanh::lean_unbox(v_x_1149_) as u8);
    v_res_1156_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___redArg(
            v_x_50__boxed_1154_,
            v_x_51__boxed_1155_,
            v_h__1_1150_,
            v_h__2_1151_,
            v_h__3_1152_,
            v_h__4_1153_,
        );
    return v_res_1156_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(
    mut v_motive_1157_: *mut leanh::LeanObject,
    mut v_x_1158_: u8,
    mut v_x_1159_: u8,
    mut v_h__1_1160_: *mut leanh::LeanObject,
    mut v_h__2_1161_: *mut leanh::LeanObject,
    mut v_h__3_1162_: *mut leanh::LeanObject,
    mut v_h__4_1163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1158_ == 0 {
        leanh::lean_dec(v_h__4_1163_);
        leanh::lean_dec(v_h__3_1162_);
        if v_x_1159_ == 0 {
            let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1161_);
            v___x_1164_ = leanh::lean_box(0);
            v___x_1165_ = leanh::lean_apply_1(v_h__1_1160_, v___x_1164_);
            return v___x_1165_;
        } else {
            let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1160_);
            v___x_1166_ = leanh::lean_box(0);
            v___x_1167_ = leanh::lean_apply_1(v_h__2_1161_, v___x_1166_);
            return v___x_1167_;
        }
    } else {
        leanh::lean_dec(v_h__2_1161_);
        leanh::lean_dec(v_h__1_1160_);
        if v_x_1159_ == 0 {
            let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1163_);
            v___x_1168_ = leanh::lean_box(0);
            v___x_1169_ = leanh::lean_apply_1(v_h__3_1162_, v___x_1168_);
            return v___x_1169_;
        } else {
            let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1162_);
            v___x_1170_ = leanh::lean_box(0);
            v___x_1171_ = leanh::lean_apply_1(v_h__4_1163_, v___x_1170_);
            return v___x_1171_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter___boxed(
    mut v_motive_1172_: *mut leanh::LeanObject,
    mut v_x_1173_: *mut leanh::LeanObject,
    mut v_x_1174_: *mut leanh::LeanObject,
    mut v_h__1_1175_: *mut leanh::LeanObject,
    mut v_h__2_1176_: *mut leanh::LeanObject,
    mut v_h__3_1177_: *mut leanh::LeanObject,
    mut v_h__4_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_72__boxed_1179_: u8 = 0;
    let mut v_x_73__boxed_1180_: u8 = 0;
    let mut v_res_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_72__boxed_1179_ = (leanh::lean_unbox(v_x_1173_) as u8);
    v_x_73__boxed_1180_ = (leanh::lean_unbox(v_x_1174_) as u8);
    v_res_1181_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv__eq_match__1_splitter(
        v_motive_1172_,
        v_x_72__boxed_1179_,
        v_x_73__boxed_1180_,
        v_h__1_1175_,
        v_h__2_1176_,
        v_h__3_1177_,
        v_h__4_1178_,
    );
    return v_res_1181_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(
    mut v_x_1182_: u8,
    mut v_x_1183_: u8,
    mut v_h__1_1184_: *mut leanh::LeanObject,
    mut v_h__2_1185_: *mut leanh::LeanObject,
    mut v_h__3_1186_: *mut leanh::LeanObject,
    mut v_h__4_1187_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1182_ == 0 {
        leanh::lean_dec(v_h__4_1187_);
        leanh::lean_dec(v_h__3_1186_);
        if v_x_1183_ == 0 {
            let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1185_);
            v___x_1188_ = leanh::lean_box(0);
            v___x_1189_ = leanh::lean_apply_1(v_h__1_1184_, v___x_1188_);
            return v___x_1189_;
        } else {
            let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1184_);
            v___x_1190_ = leanh::lean_box(0);
            v___x_1191_ = leanh::lean_apply_1(v_h__2_1185_, v___x_1190_);
            return v___x_1191_;
        }
    } else {
        leanh::lean_dec(v_h__2_1185_);
        leanh::lean_dec(v_h__1_1184_);
        if v_x_1183_ == 0 {
            let mut v___x_1192_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1193_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1187_);
            v___x_1192_ = leanh::lean_box(0);
            v___x_1193_ = leanh::lean_apply_1(v_h__3_1186_, v___x_1192_);
            return v___x_1193_;
        } else {
            let mut v___x_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1195_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1186_);
            v___x_1194_ = leanh::lean_box(0);
            v___x_1195_ = leanh::lean_apply_1(v_h__4_1187_, v___x_1194_);
            return v___x_1195_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg___boxed(
    mut v_x_1196_: *mut leanh::LeanObject,
    mut v_x_1197_: *mut leanh::LeanObject,
    mut v_h__1_1198_: *mut leanh::LeanObject,
    mut v_h__2_1199_: *mut leanh::LeanObject,
    mut v_h__3_1200_: *mut leanh::LeanObject,
    mut v_h__4_1201_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_50__boxed_1202_: u8 = 0;
    let mut v_x_51__boxed_1203_: u8 = 0;
    let mut v_res_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_50__boxed_1202_ = (leanh::lean_unbox(v_x_1196_) as u8);
    v_x_51__boxed_1203_ = (leanh::lean_unbox(v_x_1197_) as u8);
    v_res_1204_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___redArg(
        v_x_50__boxed_1202_,
        v_x_51__boxed_1203_,
        v_h__1_1198_,
        v_h__2_1199_,
        v_h__3_1200_,
        v_h__4_1201_,
    );
    return v_res_1204_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(
    mut v_motive_1205_: *mut leanh::LeanObject,
    mut v_x_1206_: u8,
    mut v_x_1207_: u8,
    mut v_h__1_1208_: *mut leanh::LeanObject,
    mut v_h__2_1209_: *mut leanh::LeanObject,
    mut v_h__3_1210_: *mut leanh::LeanObject,
    mut v_h__4_1211_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1206_ == 0 {
        leanh::lean_dec(v_h__4_1211_);
        leanh::lean_dec(v_h__3_1210_);
        if v_x_1207_ == 0 {
            let mut v___x_1212_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1213_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1209_);
            v___x_1212_ = leanh::lean_box(0);
            v___x_1213_ = leanh::lean_apply_1(v_h__1_1208_, v___x_1212_);
            return v___x_1213_;
        } else {
            let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1208_);
            v___x_1214_ = leanh::lean_box(0);
            v___x_1215_ = leanh::lean_apply_1(v_h__2_1209_, v___x_1214_);
            return v___x_1215_;
        }
    } else {
        leanh::lean_dec(v_h__2_1209_);
        leanh::lean_dec(v_h__1_1208_);
        if v_x_1207_ == 0 {
            let mut v___x_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1217_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1211_);
            v___x_1216_ = leanh::lean_box(0);
            v___x_1217_ = leanh::lean_apply_1(v_h__3_1210_, v___x_1216_);
            return v___x_1217_;
        } else {
            let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1219_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1210_);
            v___x_1218_ = leanh::lean_box(0);
            v___x_1219_ = leanh::lean_apply_1(v_h__4_1211_, v___x_1218_);
            return v___x_1219_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter___boxed(
    mut v_motive_1220_: *mut leanh::LeanObject,
    mut v_x_1221_: *mut leanh::LeanObject,
    mut v_x_1222_: *mut leanh::LeanObject,
    mut v_h__1_1223_: *mut leanh::LeanObject,
    mut v_h__2_1224_: *mut leanh::LeanObject,
    mut v_h__3_1225_: *mut leanh::LeanObject,
    mut v_h__4_1226_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_72__boxed_1227_: u8 = 0;
    let mut v_x_73__boxed_1228_: u8 = 0;
    let mut v_res_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_72__boxed_1227_ = (leanh::lean_unbox(v_x_1221_) as u8);
    v_x_73__boxed_1228_ = (leanh::lean_unbox(v_x_1222_) as u8);
    v_res_1229_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_sdiv_match__1_splitter(
        v_motive_1220_,
        v_x_72__boxed_1227_,
        v_x_73__boxed_1228_,
        v_h__1_1223_,
        v_h__2_1224_,
        v_h__3_1225_,
        v_h__4_1226_,
    );
    return v_res_1229_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(
    mut v_x_1230_: u8,
    mut v_x_1231_: u8,
    mut v_h__1_1232_: *mut leanh::LeanObject,
    mut v_h__2_1233_: *mut leanh::LeanObject,
    mut v_h__3_1234_: *mut leanh::LeanObject,
    mut v_h__4_1235_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1230_ == 0 {
        leanh::lean_dec(v_h__4_1235_);
        leanh::lean_dec(v_h__3_1234_);
        if v_x_1231_ == 0 {
            let mut v___x_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1233_);
            v___x_1236_ = leanh::lean_box(0);
            v___x_1237_ = leanh::lean_apply_1(v_h__1_1232_, v___x_1236_);
            return v___x_1237_;
        } else {
            let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1232_);
            v___x_1238_ = leanh::lean_box(0);
            v___x_1239_ = leanh::lean_apply_1(v_h__2_1233_, v___x_1238_);
            return v___x_1239_;
        }
    } else {
        leanh::lean_dec(v_h__2_1233_);
        leanh::lean_dec(v_h__1_1232_);
        if v_x_1231_ == 0 {
            let mut v___x_1240_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1241_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1235_);
            v___x_1240_ = leanh::lean_box(0);
            v___x_1241_ = leanh::lean_apply_1(v_h__3_1234_, v___x_1240_);
            return v___x_1241_;
        } else {
            let mut v___x_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1243_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1234_);
            v___x_1242_ = leanh::lean_box(0);
            v___x_1243_ = leanh::lean_apply_1(v_h__4_1235_, v___x_1242_);
            return v___x_1243_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg___boxed(
    mut v_x_1244_: *mut leanh::LeanObject,
    mut v_x_1245_: *mut leanh::LeanObject,
    mut v_h__1_1246_: *mut leanh::LeanObject,
    mut v_h__2_1247_: *mut leanh::LeanObject,
    mut v_h__3_1248_: *mut leanh::LeanObject,
    mut v_h__4_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_50__boxed_1250_: u8 = 0;
    let mut v_x_51__boxed_1251_: u8 = 0;
    let mut v_res_1252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_50__boxed_1250_ = (leanh::lean_unbox(v_x_1244_) as u8);
    v_x_51__boxed_1251_ = (leanh::lean_unbox(v_x_1245_) as u8);
    v_res_1252_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___redArg(
            v_x_50__boxed_1250_,
            v_x_51__boxed_1251_,
            v_h__1_1246_,
            v_h__2_1247_,
            v_h__3_1248_,
            v_h__4_1249_,
        );
    return v_res_1252_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(
    mut v_motive_1253_: *mut leanh::LeanObject,
    mut v_x_1254_: u8,
    mut v_x_1255_: u8,
    mut v_h__1_1256_: *mut leanh::LeanObject,
    mut v_h__2_1257_: *mut leanh::LeanObject,
    mut v_h__3_1258_: *mut leanh::LeanObject,
    mut v_h__4_1259_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_x_1254_ == 0 {
        leanh::lean_dec(v_h__4_1259_);
        leanh::lean_dec(v_h__3_1258_);
        if v_x_1255_ == 0 {
            let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1257_);
            v___x_1260_ = leanh::lean_box(0);
            v___x_1261_ = leanh::lean_apply_1(v_h__1_1256_, v___x_1260_);
            return v___x_1261_;
        } else {
            let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_1256_);
            v___x_1262_ = leanh::lean_box(0);
            v___x_1263_ = leanh::lean_apply_1(v_h__2_1257_, v___x_1262_);
            return v___x_1263_;
        }
    } else {
        leanh::lean_dec(v_h__2_1257_);
        leanh::lean_dec(v_h__1_1256_);
        if v_x_1255_ == 0 {
            let mut v___x_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1265_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1259_);
            v___x_1264_ = leanh::lean_box(0);
            v___x_1265_ = leanh::lean_apply_1(v_h__3_1258_, v___x_1264_);
            return v___x_1265_;
        } else {
            let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1258_);
            v___x_1266_ = leanh::lean_box(0);
            v___x_1267_ = leanh::lean_apply_1(v_h__4_1259_, v___x_1266_);
            return v___x_1267_;
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter___boxed(
    mut v_motive_1268_: *mut leanh::LeanObject,
    mut v_x_1269_: *mut leanh::LeanObject,
    mut v_x_1270_: *mut leanh::LeanObject,
    mut v_h__1_1271_: *mut leanh::LeanObject,
    mut v_h__2_1272_: *mut leanh::LeanObject,
    mut v_h__3_1273_: *mut leanh::LeanObject,
    mut v_h__4_1274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_72__boxed_1275_: u8 = 0;
    let mut v_x_73__boxed_1276_: u8 = 0;
    let mut v_res_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_72__boxed_1275_ = (leanh::lean_unbox(v_x_1269_) as u8);
    v_x_73__boxed_1276_ = (leanh::lean_unbox(v_x_1270_) as u8);
    v_res_1277_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_getElem__sdiv_match__1_splitter(
        v_motive_1268_,
        v_x_72__boxed_1275_,
        v_x_73__boxed_1276_,
        v_h__1_1271_,
        v_h__2_1272_,
        v_h__3_1273_,
        v_h__4_1274_,
    );
    return v_res_1277_;
}
pub unsafe fn l_BitVec_uppcRec___redArg(
    mut v_w_1278_: *mut leanh::LeanObject,
    mut v_x_1279_: *mut leanh::LeanObject,
    mut v_s_1280_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1282_: u8 = 0;
    let mut v___x_1283_: u8 = 0;
    let mut v___x_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: u8 = 0;
    let mut v_one_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1281_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1282_ = lean_nat_dec_eq(v_s_1280_, v_zero_1281_);
                if v_isZero_1282_ == 1 {
                    leanh::lean_dec(v_s_1280_);
                    v___x_1283_ = lean_nat_dec_lt(v_zero_1281_, v_w_1278_);
                    if v___x_1283_ == 0 {
                        return v___x_1283_;
                    } else {
                        v___x_1284_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1285_ = lean_nat_sub(v_w_1278_, v___x_1284_);
                        v___x_1286_ = l_Nat_testBit(v_x_1279_, v___x_1285_);
                        leanh::lean_dec(v___x_1285_);
                        return v___x_1286_;
                    }
                } else {
                    v_one_1287_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1288_ = lean_nat_sub(v_s_1280_, v_one_1287_);
                    leanh::lean_dec(v_s_1280_);
                    v___x_1289_ = lean_nat_sub(v_w_1278_, v_one_1287_);
                    v___x_1290_ = lean_nat_sub(v___x_1289_, v_n_1288_);
                    leanh::lean_dec(v___x_1289_);
                    v___x_1291_ = l_Nat_testBit(v_x_1279_, v___x_1290_);
                    leanh::lean_dec(v___x_1290_);
                    if v___x_1291_ == 0 {
                        v_s_1280_ = v_n_1288_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_1288_);
                        return v___x_1291_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_uppcRec___redArg___boxed(
    mut v_w_1293_: *mut leanh::LeanObject,
    mut v_x_1294_: *mut leanh::LeanObject,
    mut v_s_1295_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1296_: u8 = 0;
    let mut v_r_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1296_ = l_BitVec_uppcRec___redArg(v_w_1293_, v_x_1294_, v_s_1295_);
    leanh::lean_dec(v_x_1294_);
    leanh::lean_dec(v_w_1293_);
    v_r_1297_ = leanh::lean_box((v_res_1296_) as usize);
    return v_r_1297_;
}
pub unsafe fn l_BitVec_uppcRec(
    mut v_w_1298_: *mut leanh::LeanObject,
    mut v_x_1299_: *mut leanh::LeanObject,
    mut v_s_1300_: *mut leanh::LeanObject,
    mut v_hs_1301_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1302_: u8 = 0;
    v___x_1302_ = l_BitVec_uppcRec___redArg(v_w_1298_, v_x_1299_, v_s_1300_);
    return v___x_1302_;
}
pub unsafe fn l_BitVec_uppcRec___boxed(
    mut v_w_1303_: *mut leanh::LeanObject,
    mut v_x_1304_: *mut leanh::LeanObject,
    mut v_s_1305_: *mut leanh::LeanObject,
    mut v_hs_1306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1307_: u8 = 0;
    let mut v_r_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1307_ = l_BitVec_uppcRec(v_w_1303_, v_x_1304_, v_s_1305_, v_hs_1306_);
    leanh::lean_dec(v_x_1304_);
    leanh::lean_dec(v_w_1303_);
    v_r_1308_ = leanh::lean_box((v_res_1307_) as usize);
    return v_r_1308_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(
    mut v_s_1309_: *mut leanh::LeanObject,
    mut v_h__1_1310_: *mut leanh::LeanObject,
    mut v_h__2_1311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1313_: u8 = 0;
    v_zero_1312_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1313_ = lean_nat_dec_eq(v_s_1309_, v_zero_1312_);
    if v_isZero_1313_ == 1 {
        let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1311_);
        v___x_1314_ = leanh::lean_apply_1(v_h__1_1310_, leanh::lean_box(0));
        return v___x_1314_;
    } else {
        let mut v_one_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1310_);
        v_one_1315_ = leanh::lean_unsigned_to_nat(1);
        v_n_1316_ = lean_nat_sub(v_s_1309_, v_one_1315_);
        v___x_1317_ =
            leanh::lean_apply_2(v_h__2_1311_, v_n_1316_, leanh::lean_box(0));
        return v___x_1317_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg___boxed(
    mut v_s_1318_: *mut leanh::LeanObject,
    mut v_h__1_1319_: *mut leanh::LeanObject,
    mut v_h__2_1320_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1321_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___redArg(
            v_s_1318_,
            v_h__1_1319_,
            v_h__2_1320_,
        );
    leanh::lean_dec(v_s_1318_);
    return v_res_1321_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(
    mut v_w_1322_: *mut leanh::LeanObject,
    mut v_motive_1323_: *mut leanh::LeanObject,
    mut v_s_1324_: *mut leanh::LeanObject,
    mut v_hs_1325_: *mut leanh::LeanObject,
    mut v_h__1_1326_: *mut leanh::LeanObject,
    mut v_h__2_1327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1329_: u8 = 0;
    v_zero_1328_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1329_ = lean_nat_dec_eq(v_s_1324_, v_zero_1328_);
    if v_isZero_1329_ == 1 {
        let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1327_);
        v___x_1330_ = leanh::lean_apply_1(v_h__1_1326_, leanh::lean_box(0));
        return v___x_1330_;
    } else {
        let mut v_one_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1332_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1326_);
        v_one_1331_ = leanh::lean_unsigned_to_nat(1);
        v_n_1332_ = lean_nat_sub(v_s_1324_, v_one_1331_);
        v___x_1333_ =
            leanh::lean_apply_2(v_h__2_1327_, v_n_1332_, leanh::lean_box(0));
        return v___x_1333_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter___boxed(
    mut v_w_1334_: *mut leanh::LeanObject,
    mut v_motive_1335_: *mut leanh::LeanObject,
    mut v_s_1336_: *mut leanh::LeanObject,
    mut v_hs_1337_: *mut leanh::LeanObject,
    mut v_h__1_1338_: *mut leanh::LeanObject,
    mut v_h__2_1339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1340_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_uppcRec_match__1_splitter(
        v_w_1334_,
        v_motive_1335_,
        v_s_1336_,
        v_hs_1337_,
        v_h__1_1338_,
        v_h__2_1339_,
    );
    leanh::lean_dec(v_s_1336_);
    leanh::lean_dec(v_w_1334_);
    return v_res_1340_;
}
pub unsafe fn l_BitVec_aandRec___redArg(
    mut v_w_1341_: *mut leanh::LeanObject,
    mut v_x_1342_: *mut leanh::LeanObject,
    mut v_y_1343_: *mut leanh::LeanObject,
    mut v_s_1344_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1345_: u8 = 0;
    v___x_1345_ = l_Nat_testBit(v_y_1343_, v_s_1344_);
    if v___x_1345_ == 0 {
        leanh::lean_dec(v_s_1344_);
        return v___x_1345_;
    } else {
        let mut v___x_1346_: u8 = 0;
        v___x_1346_ = l_BitVec_uppcRec___redArg(v_w_1341_, v_x_1342_, v_s_1344_);
        return v___x_1346_;
    }
}
pub unsafe fn l_BitVec_aandRec___redArg___boxed(
    mut v_w_1347_: *mut leanh::LeanObject,
    mut v_x_1348_: *mut leanh::LeanObject,
    mut v_y_1349_: *mut leanh::LeanObject,
    mut v_s_1350_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1351_: u8 = 0;
    let mut v_r_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1351_ = l_BitVec_aandRec___redArg(v_w_1347_, v_x_1348_, v_y_1349_, v_s_1350_);
    leanh::lean_dec(v_y_1349_);
    leanh::lean_dec(v_x_1348_);
    leanh::lean_dec(v_w_1347_);
    v_r_1352_ = leanh::lean_box((v_res_1351_) as usize);
    return v_r_1352_;
}
pub unsafe fn l_BitVec_aandRec(
    mut v_w_1353_: *mut leanh::LeanObject,
    mut v_x_1354_: *mut leanh::LeanObject,
    mut v_y_1355_: *mut leanh::LeanObject,
    mut v_s_1356_: *mut leanh::LeanObject,
    mut v_hs_1357_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1358_: u8 = 0;
    v___x_1358_ = l_BitVec_aandRec___redArg(v_w_1353_, v_x_1354_, v_y_1355_, v_s_1356_);
    return v___x_1358_;
}
pub unsafe fn l_BitVec_aandRec___boxed(
    mut v_w_1359_: *mut leanh::LeanObject,
    mut v_x_1360_: *mut leanh::LeanObject,
    mut v_y_1361_: *mut leanh::LeanObject,
    mut v_s_1362_: *mut leanh::LeanObject,
    mut v_hs_1363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1364_: u8 = 0;
    let mut v_r_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1364_ = l_BitVec_aandRec(v_w_1359_, v_x_1360_, v_y_1361_, v_s_1362_, v_hs_1363_);
    leanh::lean_dec(v_y_1361_);
    leanh::lean_dec(v_x_1360_);
    leanh::lean_dec(v_w_1359_);
    v_r_1365_ = leanh::lean_box((v_res_1364_) as usize);
    return v_r_1365_;
}
pub unsafe fn l_BitVec_resRec___redArg(
    mut v_w_1366_: *mut leanh::LeanObject,
    mut v_x_1367_: *mut leanh::LeanObject,
    mut v_y_1368_: *mut leanh::LeanObject,
    mut v_s_1369_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1371_: u8 = 0;
    let mut v_one_1372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1374_: u8 = 0;
    v_zero_1370_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1371_ = lean_nat_dec_eq(v_s_1369_, v_zero_1370_);
    v_one_1372_ = leanh::lean_unsigned_to_nat(1);
    v_n_1373_ = lean_nat_sub(v_s_1369_, v_one_1372_);
    v_isZero_1374_ = lean_nat_dec_eq(v_n_1373_, v_zero_1370_);
    if v_isZero_1374_ == 1 {
        let mut v___x_1375_: u8 = 0;
        leanh::lean_dec(v_n_1373_);
        leanh::lean_dec(v_s_1369_);
        v___x_1375_ = l_BitVec_aandRec___redArg(v_w_1366_, v_x_1367_, v_y_1368_, v_one_1372_);
        return v___x_1375_;
    } else {
        let mut v___x_1376_: u8 = 0;
        v___x_1376_ = l_BitVec_resRec___redArg(v_w_1366_, v_x_1367_, v_y_1368_, v_n_1373_);
        if v___x_1376_ == 0 {
            let mut v___x_1377_: u8 = 0;
            v___x_1377_ = l_BitVec_aandRec___redArg(v_w_1366_, v_x_1367_, v_y_1368_, v_s_1369_);
            return v___x_1377_;
        } else {
            leanh::lean_dec(v_s_1369_);
            return v___x_1376_;
        }
    }
}
pub unsafe fn l_BitVec_resRec___redArg___boxed(
    mut v_w_1378_: *mut leanh::LeanObject,
    mut v_x_1379_: *mut leanh::LeanObject,
    mut v_y_1380_: *mut leanh::LeanObject,
    mut v_s_1381_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1382_: u8 = 0;
    let mut v_r_1383_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1382_ = l_BitVec_resRec___redArg(v_w_1378_, v_x_1379_, v_y_1380_, v_s_1381_);
    leanh::lean_dec(v_y_1380_);
    leanh::lean_dec(v_x_1379_);
    leanh::lean_dec(v_w_1378_);
    v_r_1383_ = leanh::lean_box((v_res_1382_) as usize);
    return v_r_1383_;
}
pub unsafe fn l_BitVec_resRec(
    mut v_w_1384_: *mut leanh::LeanObject,
    mut v_x_1385_: *mut leanh::LeanObject,
    mut v_y_1386_: *mut leanh::LeanObject,
    mut v_s_1387_: *mut leanh::LeanObject,
    mut v_hs_1388_: *mut leanh::LeanObject,
    mut v_hslt_1389_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1390_: u8 = 0;
    v___x_1390_ = l_BitVec_resRec___redArg(v_w_1384_, v_x_1385_, v_y_1386_, v_s_1387_);
    return v___x_1390_;
}
pub unsafe fn l_BitVec_resRec___boxed(
    mut v_w_1391_: *mut leanh::LeanObject,
    mut v_x_1392_: *mut leanh::LeanObject,
    mut v_y_1393_: *mut leanh::LeanObject,
    mut v_s_1394_: *mut leanh::LeanObject,
    mut v_hs_1395_: *mut leanh::LeanObject,
    mut v_hslt_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1397_: u8 = 0;
    let mut v_r_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1397_ = l_BitVec_resRec(
        v_w_1391_,
        v_x_1392_,
        v_y_1393_,
        v_s_1394_,
        v_hs_1395_,
        v_hslt_1396_,
    );
    leanh::lean_dec(v_y_1393_);
    leanh::lean_dec(v_x_1392_);
    leanh::lean_dec(v_w_1391_);
    v_r_1398_ = leanh::lean_box((v_res_1397_) as usize);
    return v_r_1398_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(
    mut v_s_1399_: *mut leanh::LeanObject,
    mut v_h__1_1400_: *mut leanh::LeanObject,
    mut v_h__2_1401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1403_: u8 = 0;
    v_zero_1402_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1403_ = lean_nat_dec_eq(v_s_1399_, v_zero_1402_);
    if v_isZero_1403_ == 1 {
        let mut v___x_1404_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1401_);
        v___x_1404_ = leanh::lean_apply_3(
            v_h__1_1400_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1404_;
    } else {
        let mut v_one_1405_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1400_);
        v_one_1405_ = leanh::lean_unsigned_to_nat(1);
        v_n_1406_ = lean_nat_sub(v_s_1399_, v_one_1405_);
        v___x_1407_ = leanh::lean_apply_4(
            v_h__2_1401_,
            v_n_1406_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1407_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg___boxed(
    mut v_s_1408_: *mut leanh::LeanObject,
    mut v_h__1_1409_: *mut leanh::LeanObject,
    mut v_h__2_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1411_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___redArg(
        v_s_1408_,
        v_h__1_1409_,
        v_h__2_1410_,
    );
    leanh::lean_dec(v_s_1408_);
    return v_res_1411_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(
    mut v_w_1412_: *mut leanh::LeanObject,
    mut v_motive_1413_: *mut leanh::LeanObject,
    mut v_s_1414_: *mut leanh::LeanObject,
    mut v_hs_1415_: *mut leanh::LeanObject,
    mut v_hslt_1416_: *mut leanh::LeanObject,
    mut v_h__1_1417_: *mut leanh::LeanObject,
    mut v_h__2_1418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1420_: u8 = 0;
    v_zero_1419_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1420_ = lean_nat_dec_eq(v_s_1414_, v_zero_1419_);
    if v_isZero_1420_ == 1 {
        let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1418_);
        v___x_1421_ = leanh::lean_apply_3(
            v_h__1_1417_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1421_;
    } else {
        let mut v_one_1422_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1423_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1424_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1417_);
        v_one_1422_ = leanh::lean_unsigned_to_nat(1);
        v_n_1423_ = lean_nat_sub(v_s_1414_, v_one_1422_);
        v___x_1424_ = leanh::lean_apply_4(
            v_h__2_1418_,
            v_n_1423_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1424_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter___boxed(
    mut v_w_1425_: *mut leanh::LeanObject,
    mut v_motive_1426_: *mut leanh::LeanObject,
    mut v_s_1427_: *mut leanh::LeanObject,
    mut v_hs_1428_: *mut leanh::LeanObject,
    mut v_hslt_1429_: *mut leanh::LeanObject,
    mut v_h__1_1430_: *mut leanh::LeanObject,
    mut v_h__2_1431_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1432_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__3_splitter(
        v_w_1425_,
        v_motive_1426_,
        v_s_1427_,
        v_hs_1428_,
        v_hslt_1429_,
        v_h__1_1430_,
        v_h__2_1431_,
    );
    leanh::lean_dec(v_s_1427_);
    leanh::lean_dec(v_w_1425_);
    return v_res_1432_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(
    mut v_s_x27_1433_: *mut leanh::LeanObject,
    mut v_h__1_1434_: *mut leanh::LeanObject,
    mut v_h__2_1435_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1437_: u8 = 0;
    v_zero_1436_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1437_ = lean_nat_dec_eq(v_s_x27_1433_, v_zero_1436_);
    if v_isZero_1437_ == 1 {
        let mut v___x_1438_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1435_);
        v___x_1438_ = leanh::lean_apply_4(
            v_h__1_1434_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1438_;
    } else {
        let mut v_one_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1440_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1434_);
        v_one_1439_ = leanh::lean_unsigned_to_nat(1);
        v_n_1440_ = lean_nat_sub(v_s_x27_1433_, v_one_1439_);
        v___x_1441_ = leanh::lean_apply_5(
            v_h__2_1435_,
            v_n_1440_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1441_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg___boxed(
    mut v_s_x27_1442_: *mut leanh::LeanObject,
    mut v_h__1_1443_: *mut leanh::LeanObject,
    mut v_h__2_1444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1445_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1445_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___redArg(
        v_s_x27_1442_,
        v_h__1_1443_,
        v_h__2_1444_,
    );
    leanh::lean_dec(v_s_x27_1442_);
    return v_res_1445_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(
    mut v_w_1446_: *mut leanh::LeanObject,
    mut v_s_1447_: *mut leanh::LeanObject,
    mut v_motive_1448_: *mut leanh::LeanObject,
    mut v_s_x27_1449_: *mut leanh::LeanObject,
    mut v_hs_1450_: *mut leanh::LeanObject,
    mut v_hslt_1451_: *mut leanh::LeanObject,
    mut v_hs0_1452_: *mut leanh::LeanObject,
    mut v_h__1_1453_: *mut leanh::LeanObject,
    mut v_h__2_1454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1456_: u8 = 0;
    v_zero_1455_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1456_ = lean_nat_dec_eq(v_s_x27_1449_, v_zero_1455_);
    if v_isZero_1456_ == 1 {
        let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1454_);
        v___x_1457_ = leanh::lean_apply_4(
            v_h__1_1453_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1457_;
    } else {
        let mut v_one_1458_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1460_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1453_);
        v_one_1458_ = leanh::lean_unsigned_to_nat(1);
        v_n_1459_ = lean_nat_sub(v_s_x27_1449_, v_one_1458_);
        v___x_1460_ = leanh::lean_apply_5(
            v_h__2_1454_,
            v_n_1459_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
            leanh::lean_box(0),
        );
        return v___x_1460_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter___boxed(
    mut v_w_1461_: *mut leanh::LeanObject,
    mut v_s_1462_: *mut leanh::LeanObject,
    mut v_motive_1463_: *mut leanh::LeanObject,
    mut v_s_x27_1464_: *mut leanh::LeanObject,
    mut v_hs_1465_: *mut leanh::LeanObject,
    mut v_hslt_1466_: *mut leanh::LeanObject,
    mut v_hs0_1467_: *mut leanh::LeanObject,
    mut v_h__1_1468_: *mut leanh::LeanObject,
    mut v_h__2_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1470_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_resRec_match__1_splitter(
        v_w_1461_,
        v_s_1462_,
        v_motive_1463_,
        v_s_x27_1464_,
        v_hs_1465_,
        v_hslt_1466_,
        v_hs0_1467_,
        v_h__1_1468_,
        v_h__2_1469_,
    );
    leanh::lean_dec(v_s_x27_1464_);
    leanh::lean_dec(v_s_1462_);
    leanh::lean_dec(v_w_1461_);
    return v_res_1470_;
}
pub unsafe fn l_BitVec_extractAndExtendBit___redArg(
    mut v_idx_1471_: *mut leanh::LeanObject,
    mut v_len_1472_: *mut leanh::LeanObject,
    mut v_x_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_unsigned_to_nat(1);
    v___x_1475_ = l_BitVec_extractLsb_x27___redArg(v_idx_1471_, v___x_1474_, v_x_1473_);
    v___x_1476_ = l_BitVec_setWidth(v___x_1474_, v_len_1472_, v___x_1475_);
    leanh::lean_dec(v___x_1475_);
    return v___x_1476_;
}
pub unsafe fn l_BitVec_extractAndExtendBit___redArg___boxed(
    mut v_idx_1477_: *mut leanh::LeanObject,
    mut v_len_1478_: *mut leanh::LeanObject,
    mut v_x_1479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1480_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1480_ = l_BitVec_extractAndExtendBit___redArg(v_idx_1477_, v_len_1478_, v_x_1479_);
    leanh::lean_dec(v_x_1479_);
    leanh::lean_dec(v_len_1478_);
    leanh::lean_dec(v_idx_1477_);
    return v_res_1480_;
}
pub unsafe fn l_BitVec_extractAndExtendBit(
    mut v_w_1481_: *mut leanh::LeanObject,
    mut v_idx_1482_: *mut leanh::LeanObject,
    mut v_len_1483_: *mut leanh::LeanObject,
    mut v_x_1484_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1485_ = l_BitVec_extractAndExtendBit___redArg(v_idx_1482_, v_len_1483_, v_x_1484_);
    return v___x_1485_;
}
pub unsafe fn l_BitVec_extractAndExtendBit___boxed(
    mut v_w_1486_: *mut leanh::LeanObject,
    mut v_idx_1487_: *mut leanh::LeanObject,
    mut v_len_1488_: *mut leanh::LeanObject,
    mut v_x_1489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1490_ = l_BitVec_extractAndExtendBit(v_w_1486_, v_idx_1487_, v_len_1488_, v_x_1489_);
    leanh::lean_dec(v_x_1489_);
    leanh::lean_dec(v_len_1488_);
    leanh::lean_dec(v_idx_1487_);
    leanh::lean_dec(v_w_1486_);
    return v_res_1490_;
}
pub unsafe fn l_BitVec_extractAndExtendAux___redArg(
    mut v_w_1491_: *mut leanh::LeanObject,
    mut v_k_1492_: *mut leanh::LeanObject,
    mut v_len_1493_: *mut leanh::LeanObject,
    mut v_x_1494_: *mut leanh::LeanObject,
    mut v_acc_1495_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_1497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1498_: u8 = 0;
    let mut v___x_1499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_acc_x27_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1496_ = lean_nat_sub(v_w_1491_, v_k_1492_);
                v_zero_1497_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1498_ = lean_nat_dec_eq(v___x_1496_, v_zero_1497_);
                leanh::lean_dec(v___x_1496_);
                if v_isZero_1498_ == 1 {
                    leanh::lean_dec(v_k_1492_);
                    return v_acc_1495_;
                } else {
                    v___x_1499_ = lean_nat_mul(v_k_1492_, v_len_1493_);
                    v___x_1500_ =
                        l_BitVec_extractAndExtendBit___redArg(v_k_1492_, v_len_1493_, v_x_1494_);
                    v_acc_x27_1501_ =
                        l_BitVec_append___redArg(v___x_1499_, v___x_1500_, v_acc_1495_);
                    leanh::lean_dec(v_acc_1495_);
                    leanh::lean_dec(v___x_1500_);
                    leanh::lean_dec(v___x_1499_);
                    v___x_1502_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1503_ = lean_nat_add(v_k_1492_, v___x_1502_);
                    leanh::lean_dec(v_k_1492_);
                    v_k_1492_ = v___x_1503_;
                    v_acc_1495_ = v_acc_x27_1501_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_extractAndExtendAux___redArg___boxed(
    mut v_w_1505_: *mut leanh::LeanObject,
    mut v_k_1506_: *mut leanh::LeanObject,
    mut v_len_1507_: *mut leanh::LeanObject,
    mut v_x_1508_: *mut leanh::LeanObject,
    mut v_acc_1509_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1510_ = l_BitVec_extractAndExtendAux___redArg(
        v_w_1505_,
        v_k_1506_,
        v_len_1507_,
        v_x_1508_,
        v_acc_1509_,
    );
    leanh::lean_dec(v_x_1508_);
    leanh::lean_dec(v_len_1507_);
    leanh::lean_dec(v_w_1505_);
    return v_res_1510_;
}
pub unsafe fn l_BitVec_extractAndExtendAux(
    mut v_w_1511_: *mut leanh::LeanObject,
    mut v_k_1512_: *mut leanh::LeanObject,
    mut v_len_1513_: *mut leanh::LeanObject,
    mut v_x_1514_: *mut leanh::LeanObject,
    mut v_acc_1515_: *mut leanh::LeanObject,
    mut v_hle_1516_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1517_ = l_BitVec_extractAndExtendAux___redArg(
        v_w_1511_,
        v_k_1512_,
        v_len_1513_,
        v_x_1514_,
        v_acc_1515_,
    );
    return v___x_1517_;
}
pub unsafe fn l_BitVec_extractAndExtendAux___boxed(
    mut v_w_1518_: *mut leanh::LeanObject,
    mut v_k_1519_: *mut leanh::LeanObject,
    mut v_len_1520_: *mut leanh::LeanObject,
    mut v_x_1521_: *mut leanh::LeanObject,
    mut v_acc_1522_: *mut leanh::LeanObject,
    mut v_hle_1523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1524_ = l_BitVec_extractAndExtendAux(
        v_w_1518_,
        v_k_1519_,
        v_len_1520_,
        v_x_1521_,
        v_acc_1522_,
        v_hle_1523_,
    );
    leanh::lean_dec(v_x_1521_);
    leanh::lean_dec(v_len_1520_);
    leanh::lean_dec(v_w_1518_);
    return v_res_1524_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(
    mut v_x_1525_: *mut leanh::LeanObject,
    mut v_h__1_1526_: *mut leanh::LeanObject,
    mut v_h__2_1527_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1529_: u8 = 0;
    v_zero_1528_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1529_ = lean_nat_dec_eq(v_x_1525_, v_zero_1528_);
    if v_isZero_1529_ == 1 {
        let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1527_);
        v___x_1530_ = leanh::lean_apply_1(v_h__1_1526_, leanh::lean_box(0));
        return v___x_1530_;
    } else {
        let mut v_one_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1526_);
        v_one_1531_ = leanh::lean_unsigned_to_nat(1);
        v_n_1532_ = lean_nat_sub(v_x_1525_, v_one_1531_);
        v___x_1533_ =
            leanh::lean_apply_2(v_h__2_1527_, v_n_1532_, leanh::lean_box(0));
        return v___x_1533_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg___boxed(
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_h__1_1535_: *mut leanh::LeanObject,
    mut v_h__2_1536_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1537_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___redArg(v_x_1534_, v_h__1_1535_, v_h__2_1536_);
    leanh::lean_dec(v_x_1534_);
    return v_res_1537_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(
    mut v_motive_1538_: *mut leanh::LeanObject,
    mut v_x_1539_: *mut leanh::LeanObject,
    mut v_h__1_1540_: *mut leanh::LeanObject,
    mut v_h__2_1541_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1543_: u8 = 0;
    v_zero_1542_ = leanh::lean_unsigned_to_nat(0);
    v_isZero_1543_ = lean_nat_dec_eq(v_x_1539_, v_zero_1542_);
    if v_isZero_1543_ == 1 {
        let mut v___x_1544_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_1541_);
        v___x_1544_ = leanh::lean_apply_1(v_h__1_1540_, leanh::lean_box(0));
        return v___x_1544_;
    } else {
        let mut v_one_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_n_1546_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_1540_);
        v_one_1545_ = leanh::lean_unsigned_to_nat(1);
        v_n_1546_ = lean_nat_sub(v_x_1539_, v_one_1545_);
        v___x_1547_ =
            leanh::lean_apply_2(v_h__2_1541_, v_n_1546_, leanh::lean_box(0));
        return v___x_1547_;
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter___boxed(
    mut v_motive_1548_: *mut leanh::LeanObject,
    mut v_x_1549_: *mut leanh::LeanObject,
    mut v_h__1_1550_: *mut leanh::LeanObject,
    mut v_h__2_1551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1552_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_extractAndExtendAux_match__1_splitter(
            v_motive_1548_,
            v_x_1549_,
            v_h__1_1550_,
            v_h__2_1551_,
        );
    leanh::lean_dec(v_x_1549_);
    return v_res_1552_;
}
pub unsafe fn _init_l_BitVec_extractAndExtend___closed__0() -> *mut leanh::LeanObject {
    let mut v___x_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1553_ = leanh::lean_unsigned_to_nat(0);
    v___x_1554_ = l_BitVec_ofNat(v___x_1553_, v___x_1553_);
    return v___x_1554_;
}
pub unsafe fn l_BitVec_extractAndExtend(
    mut v_w_1555_: *mut leanh::LeanObject,
    mut v_len_1556_: *mut leanh::LeanObject,
    mut v_x_1557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1558_ = leanh::lean_unsigned_to_nat(0);
    v___x_1559_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_BitVec_extractAndExtend___closed__0),
        core::ptr::addr_of_mut!(l_BitVec_extractAndExtend___closed__0_once),
        _init_l_BitVec_extractAndExtend___closed__0,
    );
    v___x_1560_ = l_BitVec_extractAndExtendAux___redArg(
        v_w_1555_,
        v___x_1558_,
        v_len_1556_,
        v_x_1557_,
        v___x_1559_,
    );
    return v___x_1560_;
}
pub unsafe fn l_BitVec_extractAndExtend___boxed(
    mut v_w_1561_: *mut leanh::LeanObject,
    mut v_len_1562_: *mut leanh::LeanObject,
    mut v_x_1563_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1564_ = l_BitVec_extractAndExtend(v_w_1561_, v_len_1562_, v_x_1563_);
    leanh::lean_dec(v_x_1563_);
    leanh::lean_dec(v_len_1562_);
    leanh::lean_dec(v_w_1561_);
    return v_res_1564_;
}
pub unsafe fn l_BitVec_cpopLayer___redArg(
    mut v_len_1565_: *mut leanh::LeanObject,
    mut v_w_1566_: *mut leanh::LeanObject,
    mut v_iterNum_1567_: *mut leanh::LeanObject,
    mut v_oldLayer_1568_: *mut leanh::LeanObject,
    mut v_newLayer_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: u8 = 0;
    let mut v___x_1575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op1_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_op2_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newLayer_x27_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1570_ = leanh::lean_unsigned_to_nat(2);
                v___x_1571_ = lean_nat_mul(v_iterNum_1567_, v___x_1570_);
                v___x_1572_ = lean_nat_sub(v_len_1565_, v___x_1571_);
                leanh::lean_dec(v___x_1571_);
                v___x_1573_ = leanh::lean_unsigned_to_nat(0);
                v___x_1574_ = lean_nat_dec_eq(v___x_1572_, v___x_1573_);
                leanh::lean_dec(v___x_1572_);
                if v___x_1574_ == 0 {
                    v___x_1575_ = lean_nat_mul(v___x_1570_, v_iterNum_1567_);
                    v___x_1576_ = lean_nat_mul(v___x_1575_, v_w_1566_);
                    v_op1_1577_ =
                        l_BitVec_extractLsb_x27___redArg(v___x_1576_, v_w_1566_, v_oldLayer_1568_);
                    leanh::lean_dec(v___x_1576_);
                    v___x_1578_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1579_ = lean_nat_add(v___x_1575_, v___x_1578_);
                    leanh::lean_dec(v___x_1575_);
                    v___x_1580_ = lean_nat_mul(v___x_1579_, v_w_1566_);
                    leanh::lean_dec(v___x_1579_);
                    v_op2_1581_ =
                        l_BitVec_extractLsb_x27___redArg(v___x_1580_, v_w_1566_, v_oldLayer_1568_);
                    leanh::lean_dec(v___x_1580_);
                    v___x_1582_ = lean_nat_mul(v_iterNum_1567_, v_w_1566_);
                    v___x_1583_ = l_BitVec_add(v_w_1566_, v_op1_1577_, v_op2_1581_);
                    leanh::lean_dec(v_op2_1581_);
                    leanh::lean_dec(v_op1_1577_);
                    v_newLayer_x27_1584_ =
                        l_BitVec_append___redArg(v___x_1582_, v___x_1583_, v_newLayer_1569_);
                    leanh::lean_dec(v_newLayer_1569_);
                    leanh::lean_dec(v___x_1583_);
                    leanh::lean_dec(v___x_1582_);
                    v___x_1585_ = lean_nat_add(v_iterNum_1567_, v___x_1578_);
                    leanh::lean_dec(v_iterNum_1567_);
                    v_iterNum_1567_ = v___x_1585_;
                    v_newLayer_1569_ = v_newLayer_x27_1584_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_iterNum_1567_);
                    return v_newLayer_1569_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_cpopLayer___redArg___boxed(
    mut v_len_1587_: *mut leanh::LeanObject,
    mut v_w_1588_: *mut leanh::LeanObject,
    mut v_iterNum_1589_: *mut leanh::LeanObject,
    mut v_oldLayer_1590_: *mut leanh::LeanObject,
    mut v_newLayer_1591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1592_ = l_BitVec_cpopLayer___redArg(
        v_len_1587_,
        v_w_1588_,
        v_iterNum_1589_,
        v_oldLayer_1590_,
        v_newLayer_1591_,
    );
    leanh::lean_dec(v_oldLayer_1590_);
    leanh::lean_dec(v_w_1588_);
    leanh::lean_dec(v_len_1587_);
    return v_res_1592_;
}
pub unsafe fn l_BitVec_cpopLayer(
    mut v_len_1593_: *mut leanh::LeanObject,
    mut v_w_1594_: *mut leanh::LeanObject,
    mut v_iterNum_1595_: *mut leanh::LeanObject,
    mut v_oldLayer_1596_: *mut leanh::LeanObject,
    mut v_newLayer_1597_: *mut leanh::LeanObject,
    mut v_hold_1598_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1599_ = l_BitVec_cpopLayer___redArg(
        v_len_1593_,
        v_w_1594_,
        v_iterNum_1595_,
        v_oldLayer_1596_,
        v_newLayer_1597_,
    );
    return v___x_1599_;
}
pub unsafe fn l_BitVec_cpopLayer___boxed(
    mut v_len_1600_: *mut leanh::LeanObject,
    mut v_w_1601_: *mut leanh::LeanObject,
    mut v_iterNum_1602_: *mut leanh::LeanObject,
    mut v_oldLayer_1603_: *mut leanh::LeanObject,
    mut v_newLayer_1604_: *mut leanh::LeanObject,
    mut v_hold_1605_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1606_ = l_BitVec_cpopLayer(
        v_len_1600_,
        v_w_1601_,
        v_iterNum_1602_,
        v_oldLayer_1603_,
        v_newLayer_1604_,
        v_hold_1605_,
    );
    leanh::lean_dec(v_oldLayer_1603_);
    leanh::lean_dec(v_w_1601_);
    leanh::lean_dec(v_len_1600_);
    return v_res_1606_;
}
pub unsafe fn l_BitVec_cpopTree(
    mut v_len_1607_: *mut leanh::LeanObject,
    mut v_w_1608_: *mut leanh::LeanObject,
    mut v_l_1609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1611_: u8 = 0;
    let mut v___x_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u8 = 0;
    let mut v___x_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1610_ = leanh::lean_unsigned_to_nat(0);
                v___x_1611_ = lean_nat_dec_eq(v_len_1607_, v___x_1610_);
                if v___x_1611_ == 0 {
                    v___x_1612_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1613_ = lean_nat_dec_eq(v_len_1607_, v___x_1612_);
                    if v___x_1613_ == 0 {
                        v___x_1614_ = lean_nat_add(v_len_1607_, v___x_1612_);
                        v___x_1615_ = lean_nat_shiftr(v___x_1614_, v___x_1612_);
                        leanh::lean_dec(v___x_1614_);
                        v___x_1616_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_BitVec_extractAndExtend___closed__0),
                            core::ptr::addr_of_mut!(l_BitVec_extractAndExtend___closed__0_once),
                            _init_l_BitVec_extractAndExtend___closed__0,
                        );
                        v___x_1617_ = l_BitVec_cpopLayer___redArg(
                            v_len_1607_,
                            v_w_1608_,
                            v___x_1610_,
                            v_l_1609_,
                            v___x_1616_,
                        );
                        leanh::lean_dec(v_l_1609_);
                        leanh::lean_dec(v_len_1607_);
                        v_len_1607_ = v___x_1615_;
                        v_l_1609_ = v___x_1617_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_len_1607_);
                        return v_l_1609_;
                    }
                } else {
                    leanh::lean_dec(v_l_1609_);
                    leanh::lean_dec(v_len_1607_);
                    v___x_1619_ = l_BitVec_ofNat(v_w_1608_, v___x_1610_);
                    return v___x_1619_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_BitVec_cpopTree___boxed(
    mut v_len_1620_: *mut leanh::LeanObject,
    mut v_w_1621_: *mut leanh::LeanObject,
    mut v_l_1622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1623_ = l_BitVec_cpopTree(v_len_1620_, v_w_1621_, v_l_1622_);
    leanh::lean_dec(v_w_1621_);
    return v_res_1623_;
}
pub unsafe fn l_BitVec_cpopRec(
    mut v_w_1624_: *mut leanh::LeanObject,
    mut v_x_1625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    v___x_1626_ = leanh::lean_unsigned_to_nat(1);
    v___x_1627_ = lean_nat_dec_lt(v___x_1626_, v_w_1624_);
    if v___x_1627_ == 0 {
        let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1629_: u8 = 0;
        v___x_1628_ = leanh::lean_unsigned_to_nat(0);
        v___x_1629_ = lean_nat_dec_lt(v___x_1628_, v_w_1624_);
        if v___x_1629_ == 0 {
            let mut v___x_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1630_ = l_BitVec_ofNat(v_w_1624_, v___x_1628_);
            leanh::lean_dec(v_w_1624_);
            return v___x_1630_;
        } else {
            leanh::lean_dec(v_w_1624_);
            leanh::lean_inc(v_x_1625_);
            return v_x_1625_;
        }
    } else {
        let mut v_extendedBits_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1632_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_extendedBits_1631_ = l_BitVec_extractAndExtend(v_w_1624_, v_w_1624_, v_x_1625_);
        leanh::lean_inc(v_w_1624_);
        v___x_1632_ = l_BitVec_cpopTree(v_w_1624_, v_w_1624_, v_extendedBits_1631_);
        leanh::lean_dec(v_w_1624_);
        return v___x_1632_;
    }
}
pub unsafe fn l_BitVec_cpopRec___boxed(
    mut v_w_1633_: *mut leanh::LeanObject,
    mut v_x_1634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1635_ = l_BitVec_cpopRec(v_w_1633_, v_x_1634_);
    leanh::lean_dec(v_x_1634_);
    return v_res_1635_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(
    mut v_w_1636_: *mut leanh::LeanObject,
    mut v_x_1637_: *mut leanh::LeanObject,
    mut v_rem_1638_: *mut leanh::LeanObject,
    mut v_acc_1639_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1641_: u8 = 0;
    let mut v_one_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1640_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1641_ = lean_nat_dec_eq(v_rem_1638_, v_zero_1640_);
                if v_isZero_1641_ == 1 {
                    leanh::lean_dec(v_rem_1638_);
                    return v_acc_1639_;
                } else {
                    v_one_1642_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1643_ = lean_nat_sub(v_rem_1638_, v_one_1642_);
                    leanh::lean_dec(v_rem_1638_);
                    v___x_1644_ = lean_nat_mul(v_n_1643_, v_w_1636_);
                    v___x_1645_ =
                        l_BitVec_extractLsb_x27___redArg(v___x_1644_, v_w_1636_, v_x_1637_);
                    leanh::lean_dec(v___x_1644_);
                    v___x_1646_ = l_BitVec_add(v_w_1636_, v_acc_1639_, v___x_1645_);
                    leanh::lean_dec(v___x_1645_);
                    leanh::lean_dec(v_acc_1639_);
                    v_rem_1638_ = v_n_1643_;
                    v_acc_1639_ = v___x_1646_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg___boxed(
    mut v_w_1648_: *mut leanh::LeanObject,
    mut v_x_1649_: *mut leanh::LeanObject,
    mut v_rem_1650_: *mut leanh::LeanObject,
    mut v_acc_1651_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1652_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(
        v_w_1648_,
        v_x_1649_,
        v_rem_1650_,
        v_acc_1651_,
    );
    leanh::lean_dec(v_x_1649_);
    leanh::lean_dec(v_w_1648_);
    return v_res_1652_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(
    mut v_l_1653_: *mut leanh::LeanObject,
    mut v_w_1654_: *mut leanh::LeanObject,
    mut v_x_1655_: *mut leanh::LeanObject,
    mut v_rem_1656_: *mut leanh::LeanObject,
    mut v_acc_1657_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1658_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(
        v_w_1654_,
        v_x_1655_,
        v_rem_1656_,
        v_acc_1657_,
    );
    return v___x_1658_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___boxed(
    mut v_l_1659_: *mut leanh::LeanObject,
    mut v_w_1660_: *mut leanh::LeanObject,
    mut v_x_1661_: *mut leanh::LeanObject,
    mut v_rem_1662_: *mut leanh::LeanObject,
    mut v_acc_1663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1664_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux(
        v_l_1659_,
        v_w_1660_,
        v_x_1661_,
        v_rem_1662_,
        v_acc_1663_,
    );
    leanh::lean_dec(v_x_1661_);
    leanh::lean_dec(v_w_1660_);
    leanh::lean_dec(v_l_1659_);
    return v_res_1664_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(
    mut v_l_1665_: *mut leanh::LeanObject,
    mut v_w_1666_: *mut leanh::LeanObject,
    mut v_x_1667_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1668_ = leanh::lean_unsigned_to_nat(0);
    v___x_1669_ = l_BitVec_ofNat(v_w_1666_, v___x_1668_);
    v___x_1670_ = l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRecAux___redArg(
        v_w_1666_,
        v_x_1667_,
        v_l_1665_,
        v___x_1669_,
    );
    return v___x_1670_;
}
pub unsafe fn l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec___boxed(
    mut v_l_1671_: *mut leanh::LeanObject,
    mut v_w_1672_: *mut leanh::LeanObject,
    mut v_x_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1674_ =
        l___private_Init_Data_BitVec_Bitblast_0__BitVec_addRec(v_l_1671_, v_w_1672_, v_x_1673_);
    leanh::lean_dec(v_x_1673_);
    leanh::lean_dec(v_w_1672_);
    return v_res_1674_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_BitVec_Bitblast(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Folds(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Decidable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_BitVec_Bitblast(
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
pub unsafe fn initialize_Init_Data_BitVec_Bitblast(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Folds(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_BinderPredicates(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_BitVec_Decidable(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Pow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Mod(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_TacticsExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_BitVec_Bitblast(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_BitVec_Bitblast(builtin);
}
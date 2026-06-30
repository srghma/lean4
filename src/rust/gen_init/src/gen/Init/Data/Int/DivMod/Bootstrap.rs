// Lean compiler output
// Module: Init.Data.Int.DivMod.Bootstrap
// Imports: Init.Data.Int.DivMod.Basic Init.Data.Nat.Div.Basic Init.ByCases Init.Data.Int.Lemmas Init.Data.Int.Order Init.Data.Nat.Dvd Init.RCases
use crate::ffi::{lean_int_dec_lt, lean_nat_abs, lean_nat_dec_eq, lean_nat_sub, lean_nat_to_int};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::Lemmas::{
    initialize_Init_Data_Int_Lemmas, runtime_initialize_Init_Data_Int_Lemmas,
};
use crate::r#gen::Init::Data::Int::Order::{
    initialize_Init_Data_Int_Order, runtime_initialize_Init_Data_Int_Order,
};
use crate::r#gen::Init::Data::Nat::Div::Basic::{
    initialize_Init_Data_Nat_Div_Basic, runtime_initialize_Init_Data_Nat_Div_Basic,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
static mut l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v_natZero_81_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_82_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_natZero_81_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_82_ = lean_nat_to_int(v_natZero_81_);
    return v_intZero_82_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(
    mut v_x_83_: *mut leanh::LeanObject,
    mut v_x_84_: *mut leanh::LeanObject,
    mut v_h__1_85_: *mut leanh::LeanObject,
    mut v_h__2_86_: *mut leanh::LeanObject,
    mut v_h__3_87_: *mut leanh::LeanObject,
    mut v_h__4_88_: *mut leanh::LeanObject,
    mut v_h__5_89_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_90_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_91_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_92_: u8 = 0;
    v_natZero_90_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_91_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
    v_isNeg_92_ = lean_int_dec_lt(v_x_83_, v_intZero_91_);
    if v_isNeg_92_ == 0 {
        let mut v_a_93_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_94_: u8 = 0;
        leanh::lean_dec(v_h__5_89_);
        leanh::lean_dec(v_h__4_88_);
        leanh::lean_dec(v_h__3_87_);
        v_a_93_ = lean_nat_abs(v_x_83_);
        v_isNeg_94_ = lean_int_dec_lt(v_x_84_, v_intZero_91_);
        if v_isNeg_94_ == 0 {
            let mut v_a_95_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_86_);
            v_a_95_ = lean_nat_abs(v_x_84_);
            v___x_96_ = leanh::lean_apply_2(v_h__1_85_, v_a_93_, v_a_95_);
            return v___x_96_;
        } else {
            let mut v_abs_97_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_98_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_99_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_100_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_85_);
            v_abs_97_ = lean_nat_abs(v_x_84_);
            v_one_98_ = leanh::lean_unsigned_to_nat(1);
            v_a_99_ = lean_nat_sub(v_abs_97_, v_one_98_);
            leanh::lean_dec(v_abs_97_);
            v___x_100_ = leanh::lean_apply_2(v_h__2_86_, v_a_93_, v_a_99_);
            return v___x_100_;
        }
    } else {
        let mut v_abs_101_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_102_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_103_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_104_: u8 = 0;
        leanh::lean_dec(v_h__2_86_);
        leanh::lean_dec(v_h__1_85_);
        v_abs_101_ = lean_nat_abs(v_x_83_);
        v_one_102_ = leanh::lean_unsigned_to_nat(1);
        v_a_103_ = lean_nat_sub(v_abs_101_, v_one_102_);
        leanh::lean_dec(v_abs_101_);
        v_isNeg_104_ = lean_int_dec_lt(v_x_84_, v_intZero_91_);
        if v_isNeg_104_ == 0 {
            let mut v_a_105_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isZero_106_: u8 = 0;
            leanh::lean_dec(v_h__5_89_);
            v_a_105_ = lean_nat_abs(v_x_84_);
            v_isZero_106_ = lean_nat_dec_eq(v_a_105_, v_natZero_90_);
            if v_isZero_106_ == 1 {
                let mut v___x_107_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_a_105_);
                leanh::lean_dec(v_h__4_88_);
                v___x_107_ = leanh::lean_apply_1(v_h__3_87_, v_a_103_);
                return v___x_107_;
            } else {
                let mut v_n_108_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_87_);
                v_n_108_ = lean_nat_sub(v_a_105_, v_one_102_);
                leanh::lean_dec(v_a_105_);
                v___x_109_ = leanh::lean_apply_2(v_h__4_88_, v_a_103_, v_n_108_);
                return v___x_109_;
            }
        } else {
            let mut v_abs_110_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_111_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_88_);
            leanh::lean_dec(v_h__3_87_);
            v_abs_110_ = lean_nat_abs(v_x_84_);
            v_a_111_ = lean_nat_sub(v_abs_110_, v_one_102_);
            leanh::lean_dec(v_abs_110_);
            v___x_112_ = leanh::lean_apply_2(v_h__5_89_, v_a_103_, v_a_111_);
            return v___x_112_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(
    mut v_x_113_: *mut leanh::LeanObject,
    mut v_x_114_: *mut leanh::LeanObject,
    mut v_h__1_115_: *mut leanh::LeanObject,
    mut v_h__2_116_: *mut leanh::LeanObject,
    mut v_h__3_117_: *mut leanh::LeanObject,
    mut v_h__4_118_: *mut leanh::LeanObject,
    mut v_h__5_119_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(
        v_x_113_,
        v_x_114_,
        v_h__1_115_,
        v_h__2_116_,
        v_h__3_117_,
        v_h__4_118_,
        v_h__5_119_,
    );
    leanh::lean_dec(v_x_114_);
    leanh::lean_dec(v_x_113_);
    return v_res_120_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(
    mut v_motive_121_: *mut leanh::LeanObject,
    mut v_x_122_: *mut leanh::LeanObject,
    mut v_x_123_: *mut leanh::LeanObject,
    mut v_h__1_124_: *mut leanh::LeanObject,
    mut v_h__2_125_: *mut leanh::LeanObject,
    mut v_h__3_126_: *mut leanh::LeanObject,
    mut v_h__4_127_: *mut leanh::LeanObject,
    mut v_h__5_128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_natZero_129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_intZero_130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isNeg_131_: u8 = 0;
    v_natZero_129_ = leanh::lean_unsigned_to_nat(0);
    v_intZero_130_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
    v_isNeg_131_ = lean_int_dec_lt(v_x_122_, v_intZero_130_);
    if v_isNeg_131_ == 0 {
        let mut v_a_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_133_: u8 = 0;
        leanh::lean_dec(v_h__5_128_);
        leanh::lean_dec(v_h__4_127_);
        leanh::lean_dec(v_h__3_126_);
        v_a_132_ = lean_nat_abs(v_x_122_);
        v_isNeg_133_ = lean_int_dec_lt(v_x_123_, v_intZero_130_);
        if v_isNeg_133_ == 0 {
            let mut v_a_134_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_125_);
            v_a_134_ = lean_nat_abs(v_x_123_);
            v___x_135_ = leanh::lean_apply_2(v_h__1_124_, v_a_132_, v_a_134_);
            return v___x_135_;
        } else {
            let mut v_abs_136_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_one_137_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_138_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__1_124_);
            v_abs_136_ = lean_nat_abs(v_x_123_);
            v_one_137_ = leanh::lean_unsigned_to_nat(1);
            v_a_138_ = lean_nat_sub(v_abs_136_, v_one_137_);
            leanh::lean_dec(v_abs_136_);
            v___x_139_ = leanh::lean_apply_2(v_h__2_125_, v_a_132_, v_a_138_);
            return v___x_139_;
        }
    } else {
        let mut v_abs_140_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_one_141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_142_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_isNeg_143_: u8 = 0;
        leanh::lean_dec(v_h__2_125_);
        leanh::lean_dec(v_h__1_124_);
        v_abs_140_ = lean_nat_abs(v_x_122_);
        v_one_141_ = leanh::lean_unsigned_to_nat(1);
        v_a_142_ = lean_nat_sub(v_abs_140_, v_one_141_);
        leanh::lean_dec(v_abs_140_);
        v_isNeg_143_ = lean_int_dec_lt(v_x_123_, v_intZero_130_);
        if v_isNeg_143_ == 0 {
            let mut v_a_144_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_isZero_145_: u8 = 0;
            leanh::lean_dec(v_h__5_128_);
            v_a_144_ = lean_nat_abs(v_x_123_);
            v_isZero_145_ = lean_nat_dec_eq(v_a_144_, v_natZero_129_);
            if v_isZero_145_ == 1 {
                let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_a_144_);
                leanh::lean_dec(v_h__4_127_);
                v___x_146_ = leanh::lean_apply_1(v_h__3_126_, v_a_142_);
                return v___x_146_;
            } else {
                let mut v_n_147_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_h__3_126_);
                v_n_147_ = lean_nat_sub(v_a_144_, v_one_141_);
                leanh::lean_dec(v_a_144_);
                v___x_148_ = leanh::lean_apply_2(v_h__4_127_, v_a_142_, v_n_147_);
                return v___x_148_;
            }
        } else {
            let mut v_abs_149_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_150_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_127_);
            leanh::lean_dec(v_h__3_126_);
            v_abs_149_ = lean_nat_abs(v_x_123_);
            v_a_150_ = lean_nat_sub(v_abs_149_, v_one_141_);
            leanh::lean_dec(v_abs_149_);
            v___x_151_ = leanh::lean_apply_2(v_h__5_128_, v_a_142_, v_a_150_);
            return v___x_151_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(
    mut v_motive_152_: *mut leanh::LeanObject,
    mut v_x_153_: *mut leanh::LeanObject,
    mut v_x_154_: *mut leanh::LeanObject,
    mut v_h__1_155_: *mut leanh::LeanObject,
    mut v_h__2_156_: *mut leanh::LeanObject,
    mut v_h__3_157_: *mut leanh::LeanObject,
    mut v_h__4_158_: *mut leanh::LeanObject,
    mut v_h__5_159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_160_ = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(
        v_motive_152_,
        v_x_153_,
        v_x_154_,
        v_h__1_155_,
        v_h__2_156_,
        v_h__3_157_,
        v_h__4_158_,
        v_h__5_159_,
    );
    leanh::lean_dec(v_x_154_);
    leanh::lean_dec(v_x_153_);
    return v_res_160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_DivMod_Bootstrap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_DivMod_Bootstrap(
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
pub unsafe fn initialize_Init_Data_Int_DivMod_Bootstrap(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
}
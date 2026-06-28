// Lean compiler output
// Module: Init.Data.Int.DivMod.Bootstrap
// Imports: Init.Data.Int.DivMod.Basic Init.Data.Nat.Div.Basic Init.ByCases Init.Data.Int.Lemmas Init.Data.Int.Order Init.Data.Nat.Dvd Init.RCases
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
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_nat_sub};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_1, lean_apply_2, lean_box, lean_dec, lean_dec_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_once, lean_unsigned_to_nat,
};
static mut l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0()
-> *mut LeanObject {
    let mut v_natZero_81_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_82_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_81_ = lean_unsigned_to_nat(0);
    v_intZero_82_ = lean_nat_to_int(v_natZero_81_);
    return v_intZero_82_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(
    mut v_x_83_: *mut LeanObject,
    mut v_x_84_: *mut LeanObject,
    mut v_h__1_85_: *mut LeanObject,
    mut v_h__2_86_: *mut LeanObject,
    mut v_h__3_87_: *mut LeanObject,
    mut v_h__4_88_: *mut LeanObject,
    mut v_h__5_89_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_90_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_92_: u8 = 0;
    v_natZero_90_ = lean_unsigned_to_nat(0);
    v_intZero_91_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
    v_isNeg_92_ = lean_int_dec_lt(v_x_83_, v_intZero_91_);
    if v_isNeg_92_ == 0 {
        let mut v_a_93_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_94_: u8 = 0;
        lean_dec(v_h__5_89_);
        lean_dec(v_h__4_88_);
        lean_dec(v_h__3_87_);
        v_a_93_ = lean_nat_abs(v_x_83_);
        v_isNeg_94_ = lean_int_dec_lt(v_x_84_, v_intZero_91_);
        if v_isNeg_94_ == 0 {
            let mut v_a_95_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_86_);
            v_a_95_ = lean_nat_abs(v_x_84_);
            v___x_96_ = lean_apply_2(v_h__1_85_, v_a_93_, v_a_95_);
            return v___x_96_;
        } else {
            let mut v_abs_97_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_98_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_99_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_85_);
            v_abs_97_ = lean_nat_abs(v_x_84_);
            v_one_98_ = lean_unsigned_to_nat(1);
            v_a_99_ = lean_nat_sub(v_abs_97_, v_one_98_);
            lean_dec(v_abs_97_);
            v___x_100_ = lean_apply_2(v_h__2_86_, v_a_93_, v_a_99_);
            return v___x_100_;
        }
    } else {
        let mut v_abs_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_104_: u8 = 0;
        lean_dec(v_h__2_86_);
        lean_dec(v_h__1_85_);
        v_abs_101_ = lean_nat_abs(v_x_83_);
        v_one_102_ = lean_unsigned_to_nat(1);
        v_a_103_ = lean_nat_sub(v_abs_101_, v_one_102_);
        lean_dec(v_abs_101_);
        v_isNeg_104_ = lean_int_dec_lt(v_x_84_, v_intZero_91_);
        if v_isNeg_104_ == 0 {
            let mut v_a_105_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isZero_106_: u8 = 0;
            lean_dec(v_h__5_89_);
            v_a_105_ = lean_nat_abs(v_x_84_);
            v_isZero_106_ = lean_nat_dec_eq(v_a_105_, v_natZero_90_);
            if v_isZero_106_ == 1 {
                let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_a_105_);
                lean_dec(v_h__4_88_);
                v___x_107_ = lean_apply_1(v_h__3_87_, v_a_103_);
                return v___x_107_;
            } else {
                let mut v_n_108_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_109_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_87_);
                v_n_108_ = lean_nat_sub(v_a_105_, v_one_102_);
                lean_dec(v_a_105_);
                v___x_109_ = lean_apply_2(v_h__4_88_, v_a_103_, v_n_108_);
                return v___x_109_;
            }
        } else {
            let mut v_abs_110_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_111_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_88_);
            lean_dec(v_h__3_87_);
            v_abs_110_ = lean_nat_abs(v_x_84_);
            v_a_111_ = lean_nat_sub(v_abs_110_, v_one_102_);
            lean_dec(v_abs_110_);
            v___x_112_ = lean_apply_2(v_h__5_89_, v_a_103_, v_a_111_);
            return v___x_112_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___boxed(
    mut v_x_113_: *mut LeanObject,
    mut v_x_114_: *mut LeanObject,
    mut v_h__1_115_: *mut LeanObject,
    mut v_h__2_116_: *mut LeanObject,
    mut v_h__3_117_: *mut LeanObject,
    mut v_h__4_118_: *mut LeanObject,
    mut v_h__5_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg(
        v_x_113_,
        v_x_114_,
        v_h__1_115_,
        v_h__2_116_,
        v_h__3_117_,
        v_h__4_118_,
        v_h__5_119_,
    );
    lean_dec(v_x_114_);
    lean_dec(v_x_113_);
    return v_res_120_;
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter(
    mut v_motive_121_: *mut LeanObject,
    mut v_x_122_: *mut LeanObject,
    mut v_x_123_: *mut LeanObject,
    mut v_h__1_124_: *mut LeanObject,
    mut v_h__2_125_: *mut LeanObject,
    mut v_h__3_126_: *mut LeanObject,
    mut v_h__4_127_: *mut LeanObject,
    mut v_h__5_128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_natZero_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_131_: u8 = 0;
    v_natZero_129_ = lean_unsigned_to_nat(0);
    v_intZero_130_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0_once), _init_l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___redArg___closed__0);
    v_isNeg_131_ = lean_int_dec_lt(v_x_122_, v_intZero_130_);
    if v_isNeg_131_ == 0 {
        let mut v_a_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_133_: u8 = 0;
        lean_dec(v_h__5_128_);
        lean_dec(v_h__4_127_);
        lean_dec(v_h__3_126_);
        v_a_132_ = lean_nat_abs(v_x_122_);
        v_isNeg_133_ = lean_int_dec_lt(v_x_123_, v_intZero_130_);
        if v_isNeg_133_ == 0 {
            let mut v_a_134_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_125_);
            v_a_134_ = lean_nat_abs(v_x_123_);
            v___x_135_ = lean_apply_2(v_h__1_124_, v_a_132_, v_a_134_);
            return v___x_135_;
        } else {
            let mut v_abs_136_: *mut LeanObject = core::ptr::null_mut();
            let mut v_one_137_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_138_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__1_124_);
            v_abs_136_ = lean_nat_abs(v_x_123_);
            v_one_137_ = lean_unsigned_to_nat(1);
            v_a_138_ = lean_nat_sub(v_abs_136_, v_one_137_);
            lean_dec(v_abs_136_);
            v___x_139_ = lean_apply_2(v_h__2_125_, v_a_132_, v_a_138_);
            return v___x_139_;
        }
    } else {
        let mut v_abs_140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_one_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_142_: *mut LeanObject = core::ptr::null_mut();
        let mut v_isNeg_143_: u8 = 0;
        lean_dec(v_h__2_125_);
        lean_dec(v_h__1_124_);
        v_abs_140_ = lean_nat_abs(v_x_122_);
        v_one_141_ = lean_unsigned_to_nat(1);
        v_a_142_ = lean_nat_sub(v_abs_140_, v_one_141_);
        lean_dec(v_abs_140_);
        v_isNeg_143_ = lean_int_dec_lt(v_x_123_, v_intZero_130_);
        if v_isNeg_143_ == 0 {
            let mut v_a_144_: *mut LeanObject = core::ptr::null_mut();
            let mut v_isZero_145_: u8 = 0;
            lean_dec(v_h__5_128_);
            v_a_144_ = lean_nat_abs(v_x_123_);
            v_isZero_145_ = lean_nat_dec_eq(v_a_144_, v_natZero_129_);
            if v_isZero_145_ == 1 {
                let mut v___x_146_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_a_144_);
                lean_dec(v_h__4_127_);
                v___x_146_ = lean_apply_1(v_h__3_126_, v_a_142_);
                return v___x_146_;
            } else {
                let mut v_n_147_: *mut LeanObject = core::ptr::null_mut();
                let mut v___x_148_: *mut LeanObject = core::ptr::null_mut();
                lean_dec(v_h__3_126_);
                v_n_147_ = lean_nat_sub(v_a_144_, v_one_141_);
                lean_dec(v_a_144_);
                v___x_148_ = lean_apply_2(v_h__4_127_, v_a_142_, v_n_147_);
                return v___x_148_;
            }
        } else {
            let mut v_abs_149_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_150_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__4_127_);
            lean_dec(v_h__3_126_);
            v_abs_149_ = lean_nat_abs(v_x_123_);
            v_a_150_ = lean_nat_sub(v_abs_149_, v_one_141_);
            lean_dec(v_abs_149_);
            v___x_151_ = lean_apply_2(v_h__5_128_, v_a_142_, v_a_150_);
            return v___x_151_;
        }
    }
}
pub unsafe fn l___private_Init_Data_Int_DivMod_Bootstrap_0__Int_ediv_match__1_splitter___boxed(
    mut v_motive_152_: *mut LeanObject,
    mut v_x_153_: *mut LeanObject,
    mut v_x_154_: *mut LeanObject,
    mut v_h__1_155_: *mut LeanObject,
    mut v_h__2_156_: *mut LeanObject,
    mut v_h__3_157_: *mut LeanObject,
    mut v_h__4_158_: *mut LeanObject,
    mut v_h__5_159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_160_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x_154_);
    lean_dec(v_x_153_);
    return v_res_160_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
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
    res = runtime_initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Int_DivMod_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_DivMod_Bootstrap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
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
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
}

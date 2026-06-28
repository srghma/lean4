// Lean compiler output
// Module: Init.Data.Int.Gcd
// Imports: Init.Data.Nat.Lcm Init.Data.Int.DivMod.Basic Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.Data.Nat.Dvd Init.Omega Init.RCases
use crate::r#gen::Init::Data::Int::DivMod::Basic::{
    initialize_Init_Data_Int_DivMod_Basic, runtime_initialize_Init_Data_Int_DivMod_Basic,
};
use crate::r#gen::Init::Data::Int::DivMod::Lemmas::{
    initialize_Init_Data_Int_DivMod_Lemmas, runtime_initialize_Init_Data_Int_DivMod_Lemmas,
};
use crate::r#gen::Init::Data::Int::Pow::{
    initialize_Init_Data_Int_Pow, runtime_initialize_Init_Data_Int_Pow,
};
use crate::r#gen::Init::Data::Nat::Dvd::{
    initialize_Init_Data_Nat_Dvd, runtime_initialize_Init_Data_Nat_Dvd,
};
use crate::r#gen::Init::Data::Nat::Gcd::l_Nat_dvdProdDvdOfDvdProd___redArg;
use crate::r#gen::Init::Data::Nat::Lcm::{
    initialize_Init_Data_Nat_Lcm, l_Nat_lcm, runtime_initialize_Init_Data_Nat_Lcm,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_le, lean_int_neg, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::Nat::Gcd::lean_nat_gcd;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_inc, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_unsigned_to_nat,
};
static mut l_Int_dvdProdDvdOfDvdProd___redArg___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Int_dvdProdDvdOfDvdProd___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l_Int_gcd(
    mut v_m_67_: *mut LeanObject,
    mut v_n_68_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_69_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
    v___x_69_ = lean_nat_abs(v_m_67_);
    v___x_70_ = lean_nat_abs(v_n_68_);
    v___x_71_ = lean_nat_gcd(v___x_69_, v___x_70_);
    lean_dec(v___x_70_);
    lean_dec(v___x_69_);
    return v___x_71_;
}
pub unsafe fn l_Int_gcd___boxed(
    mut v_m_72_: *mut LeanObject,
    mut v_n_73_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_74_: *mut LeanObject = core::ptr::null_mut();
    v_res_74_ = l_Int_gcd(v_m_72_, v_n_73_);
    lean_dec(v_n_73_);
    lean_dec(v_m_72_);
    return v_res_74_;
}
pub unsafe fn l_Nat_cast___at___00Int_dvdProdDvdOfDvdProd_spec__0(
    mut v_a_75_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_76_: *mut LeanObject = core::ptr::null_mut();
    v___x_76_ = lean_nat_to_int(v_a_75_);
    return v___x_76_;
}
pub unsafe fn _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0() -> *mut LeanObject {
    let mut v___x_77_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_78_: *mut LeanObject = core::ptr::null_mut();
    v___x_77_ = lean_unsigned_to_nat(0);
    v___x_78_ = lean_nat_to_int(v___x_77_);
    return v___x_78_;
}
pub unsafe fn l_Int_dvdProdDvdOfDvdProd___redArg(
    mut v_k_79_: *mut LeanObject,
    mut v_m_80_: *mut LeanObject,
    mut v_n_81_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_82_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_83_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_u2080_85_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_87_: u8 = 0;
    let mut v_fst_88_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_89_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_91_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_92_: u8 = 0;
    let mut v___x_93_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_94_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_95_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_98_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_99_: u8 = 0;
    let mut v_fst_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_104_: u8 = 0;
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_110_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_82_ = lean_nat_abs(v_k_79_);
                v___x_83_ = lean_nat_abs(v_m_80_);
                v___x_84_ = lean_nat_abs(v_n_81_);
                v_d_u2080_85_ = l_Nat_dvdProdDvdOfDvdProd___redArg(v___x_82_, v___x_83_, v___x_84_);
                lean_dec(v___x_83_);
                lean_dec(v___x_82_);
                v___x_86_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Int_dvdProdDvdOfDvdProd___redArg___closed__0),
                    core::ptr::addr_of_mut!(l_Int_dvdProdDvdOfDvdProd___redArg___closed__0_once),
                    _init_l_Int_dvdProdDvdOfDvdProd___redArg___closed__0,
                );
                v___x_87_ = lean_int_dec_le(v___x_86_, v_k_79_);
                if v___x_87_ == 0 {
                    v_fst_88_ = lean_ctor_get(v_d_u2080_85_, 0);
                    v_snd_89_ = lean_ctor_get(v_d_u2080_85_, 1);
                    v_isSharedCheck_99_ = (!lean_is_exclusive(v_d_u2080_85_)) as u8;
                    if v_isSharedCheck_99_ == 0 {
                        v___x_91_ = v_d_u2080_85_;
                        v_isShared_92_ = v_isSharedCheck_99_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_89_);
                        lean_inc(v_fst_88_);
                        lean_dec(v_d_u2080_85_);
                        v___x_91_ = lean_box(0);
                        v_isShared_92_ = v_isSharedCheck_99_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_fst_100_ = lean_ctor_get(v_d_u2080_85_, 0);
                    v_snd_101_ = lean_ctor_get(v_d_u2080_85_, 1);
                    v_isSharedCheck_110_ = (!lean_is_exclusive(v_d_u2080_85_)) as u8;
                    if v_isSharedCheck_110_ == 0 {
                        v___x_103_ = v_d_u2080_85_;
                        v_isShared_104_ = v_isSharedCheck_110_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_101_);
                        lean_inc(v_fst_100_);
                        lean_dec(v_d_u2080_85_);
                        v___x_103_ = lean_box(0);
                        v_isShared_104_ = v_isSharedCheck_110_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_93_ = lean_nat_to_int(v_fst_88_);
                v___x_94_ = lean_int_neg(v___x_93_);
                lean_dec(v___x_93_);
                v___x_95_ = lean_nat_to_int(v_snd_89_);
                if v_isShared_92_ == 0 {
                    lean_ctor_set(v___x_91_, 1, v___x_95_);
                    lean_ctor_set(v___x_91_, 0, v___x_94_);
                    v___x_97_ = v___x_91_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_98_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_98_, 0, v___x_94_);
                    lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_95_);
                    v___x_97_ = v_reuseFailAlloc_98_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_97_;
            }
            3 => {
                v___x_105_ = lean_nat_to_int(v_fst_100_);
                v___x_106_ = lean_nat_to_int(v_snd_101_);
                if v_isShared_104_ == 0 {
                    lean_ctor_set(v___x_103_, 1, v___x_106_);
                    lean_ctor_set(v___x_103_, 0, v___x_105_);
                    v___x_108_ = v___x_103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_109_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_109_, 0, v___x_105_);
                    lean_ctor_set(v_reuseFailAlloc_109_, 1, v___x_106_);
                    v___x_108_ = v_reuseFailAlloc_109_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_108_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Int_dvdProdDvdOfDvdProd___redArg___boxed(
    mut v_k_111_: *mut LeanObject,
    mut v_m_112_: *mut LeanObject,
    mut v_n_113_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_114_: *mut LeanObject = core::ptr::null_mut();
    v_res_114_ = l_Int_dvdProdDvdOfDvdProd___redArg(v_k_111_, v_m_112_, v_n_113_);
    lean_dec(v_n_113_);
    lean_dec(v_m_112_);
    lean_dec(v_k_111_);
    return v_res_114_;
}
pub unsafe fn l_Int_dvdProdDvdOfDvdProd(
    mut v_k_115_: *mut LeanObject,
    mut v_m_116_: *mut LeanObject,
    mut v_n_117_: *mut LeanObject,
    mut v_h_118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    v___x_119_ = l_Int_dvdProdDvdOfDvdProd___redArg(v_k_115_, v_m_116_, v_n_117_);
    return v___x_119_;
}
pub unsafe fn l_Int_dvdProdDvdOfDvdProd___boxed(
    mut v_k_120_: *mut LeanObject,
    mut v_m_121_: *mut LeanObject,
    mut v_n_122_: *mut LeanObject,
    mut v_h_123_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_124_: *mut LeanObject = core::ptr::null_mut();
    v_res_124_ = l_Int_dvdProdDvdOfDvdProd(v_k_120_, v_m_121_, v_n_122_, v_h_123_);
    lean_dec(v_n_122_);
    lean_dec(v_m_121_);
    lean_dec(v_k_120_);
    return v_res_124_;
}
pub unsafe fn l_Int_lcm(
    mut v_m_125_: *mut LeanObject,
    mut v_n_126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_129_: *mut LeanObject = core::ptr::null_mut();
    v___x_127_ = lean_nat_abs(v_m_125_);
    v___x_128_ = lean_nat_abs(v_n_126_);
    v___x_129_ = l_Nat_lcm(v___x_127_, v___x_128_);
    lean_dec(v___x_128_);
    lean_dec(v___x_127_);
    return v___x_129_;
}
pub unsafe fn l_Int_lcm___boxed(
    mut v_m_130_: *mut LeanObject,
    mut v_n_131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_132_: *mut LeanObject = core::ptr::null_mut();
    v_res_132_ = l_Int_lcm(v_m_130_, v_n_131_);
    lean_dec(v_n_131_);
    lean_dec(v_m_130_);
    return v_res_132_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Int_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lcm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_DivMod_Basic(builtin);
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
    res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Int_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Int_Gcd(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lcm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Int_DivMod_Basic(builtin);
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
    res = initialize_Init_Data_Nat_Dvd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Int_Gcd(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Int_Gcd(builtin);
}

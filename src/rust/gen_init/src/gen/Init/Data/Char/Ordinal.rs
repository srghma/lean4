// Lean compiler output
// Module: Init.Data.Char.Ordinal
// Imports: Init.Data.Fin.OverflowAware Init.Data.Function Init.Data.Char.Lemmas Init.Data.Char.Order Init.Grind Init.Data.Char.Basic Init.ByCases Init.Data.Fin.Lemmas Init.Data.Int.OfNat Init.Data.Nat.Linear Init.Data.Nat.Simproc Init.Data.Option.Lemmas Init.Data.UInt.Lemmas
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::Char::Order::{
    initialize_Init_Data_Char_Order, runtime_initialize_Init_Data_Char_Order,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::Fin::OverflowAware::{
    initialize_Init_Data_Fin_OverflowAware, runtime_initialize_Init_Data_Fin_OverflowAware,
};
use crate::r#gen::Init::Data::Function::{
    initialize_Init_Data_Function, runtime_initialize_Init_Data_Function,
};
use crate::r#gen::Init::Data::Int::OfNat::{
    initialize_Init_Data_Int_OfNat, runtime_initialize_Init_Data_Int_OfNat,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::UInt::Lemmas::{
    initialize_Init_Data_UInt_Lemmas, runtime_initialize_Init_Data_UInt_Lemmas,
};
use crate::r#gen::Init::Grind::{initialize_Init_Grind, runtime_initialize_Init_Grind};
use crate::ffi::lean_uint32_add;
use crate::ffi::{
    lean_nat_add, lean_nat_dec_lt, lean_nat_sub, lean_uint32_dec_eq, lean_uint32_dec_lt,
    lean_uint32_of_nat, lean_uint32_to_nat,
};
pub static mut l_Char_numSurrogates: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_numCodePoints: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Char_succ_x3f___closed__0___boxed__const__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Char_succ_x3f___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Char_succ_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Char_numSurrogates() -> *mut crate::leanh::LeanObject {
    let mut v___x_60_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_60_ = crate::leanh::lean_unsigned_to_nat(2048);
    return v___x_60_;
}
pub unsafe fn _init_l_Char_numCodePoints() -> *mut crate::leanh::LeanObject {
    let mut v___x_61_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_61_ = crate::leanh::lean_unsigned_to_nat(1112064);
    return v___x_61_;
}
pub unsafe fn l_Char_ordinal(mut v_c_62_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_63_: u32 = 0;
    let mut v___x_64_: u8 = 0;
    v___x_63_ = 55296;
    v___x_64_ = lean_uint32_dec_lt(v_c_62_, v___x_63_);
    if v___x_64_ == 0 {
        let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_66_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_67_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_65_ = lean_uint32_to_nat(v_c_62_);
        v___x_66_ = crate::leanh::lean_unsigned_to_nat(2048);
        v___x_67_ = lean_nat_sub(v___x_65_, v___x_66_);
        crate::leanh::lean_dec(v___x_65_);
        return v___x_67_;
    } else {
        let mut v___x_68_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_68_ = lean_uint32_to_nat(v_c_62_);
        return v___x_68_;
    }
}
pub unsafe fn l_Char_ordinal___boxed(
    mut v_c_69_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_70_: u32 = 0;
    let mut v_res_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_70_ = crate::leanh::lean_unbox_uint32(v_c_69_);
    crate::leanh::lean_dec(v_c_69_);
    v_res_71_ = l_Char_ordinal(v_c_boxed_70_);
    return v_res_71_;
}
pub unsafe fn l_Char_ofOrdinal(mut v_f_72_: *mut crate::leanh::LeanObject) -> u32 {
    let mut v___x_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_74_: u8 = 0;
    v___x_73_ = crate::leanh::lean_unsigned_to_nat(55296);
    v___x_74_ = lean_nat_dec_lt(v_f_72_, v___x_73_);
    if v___x_74_ == 0 {
        let mut v___x_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_77_: u32 = 0;
        v___x_75_ = crate::leanh::lean_unsigned_to_nat(2048);
        v___x_76_ = lean_nat_add(v_f_72_, v___x_75_);
        v___x_77_ = lean_uint32_of_nat(v___x_76_);
        crate::leanh::lean_dec(v___x_76_);
        return v___x_77_;
    } else {
        let mut v___x_78_: u32 = 0;
        v___x_78_ = lean_uint32_of_nat(v_f_72_);
        return v___x_78_;
    }
}
pub unsafe fn l_Char_ofOrdinal___boxed(
    mut v_f_79_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_80_: u32 = 0;
    let mut v_r_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_80_ = l_Char_ofOrdinal(v_f_79_);
    crate::leanh::lean_dec(v_f_79_);
    v_r_81_ = crate::leanh::lean_box_uint32(v_res_80_);
    return v_r_81_;
}
pub unsafe fn _init_l_Char_succ_x3f___closed__0___boxed__const__1() -> *mut crate::leanh::LeanObject
{
    let mut v___x_82_: u32 = 0;
    let mut v___x_83_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_82_ = 57344;
    v___x_83_ = crate::leanh::lean_box_uint32(v___x_82_);
    return v___x_83_;
}
pub unsafe fn _init_l_Char_succ_x3f___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_84_ = l_Char_succ_x3f___closed__0___boxed__const__1;
    v___x_85_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_85_, 0, v___x_84_);
    return v___x_85_;
}
pub unsafe fn l_Char_succ_x3f(mut v_c_86_: u32) -> *mut crate::leanh::LeanObject {
    let mut v___x_87_: u32 = 0;
    let mut v___x_88_: u8 = 0;
    v___x_87_ = 55295;
    v___x_88_ = lean_uint32_dec_lt(v_c_86_, v___x_87_);
    if v___x_88_ == 0 {
        let mut v___x_89_: u8 = 0;
        v___x_89_ = lean_uint32_dec_eq(v_c_86_, v___x_87_);
        if v___x_89_ == 0 {
            let mut v___x_90_: u32 = 0;
            let mut v___x_91_: u8 = 0;
            v___x_90_ = 1114111;
            v___x_91_ = lean_uint32_dec_lt(v_c_86_, v___x_90_);
            if v___x_91_ == 0 {
                let mut v___x_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_92_ = crate::leanh::lean_box(0);
                return v___x_92_;
            } else {
                let mut v___x_93_: u32 = 0;
                let mut v___x_94_: u32 = 0;
                let mut v___x_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_93_ = 1;
                v___x_94_ = lean_uint32_add(v_c_86_, v___x_93_);
                v___x_95_ = crate::leanh::lean_box_uint32(v___x_94_);
                v___x_96_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_96_, 0, v___x_95_);
                return v___x_96_;
            }
        } else {
            let mut v___x_97_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_97_ = crate::leanh::lean_obj_once(
                core::ptr::addr_of_mut!(l_Char_succ_x3f___closed__0),
                core::ptr::addr_of_mut!(l_Char_succ_x3f___closed__0_once),
                _init_l_Char_succ_x3f___closed__0,
            );
            return v___x_97_;
        }
    } else {
        let mut v___x_98_: u32 = 0;
        let mut v___x_99_: u32 = 0;
        let mut v___x_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_98_ = 1;
        v___x_99_ = lean_uint32_add(v_c_86_, v___x_98_);
        v___x_100_ = crate::leanh::lean_box_uint32(v___x_99_);
        v___x_101_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_101_, 0, v___x_100_);
        return v___x_101_;
    }
}
pub unsafe fn l_Char_succ_x3f___boxed(
    mut v_c_102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_103_: u32 = 0;
    let mut v_res_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_103_ = crate::leanh::lean_unbox_uint32(v_c_102_);
    crate::leanh::lean_dec(v_c_102_);
    v_res_104_ = l_Char_succ_x3f(v_c_boxed_103_);
    return v_res_104_;
}
pub unsafe fn l_Char_succMany_x3f(
    mut v_m_105_: *mut crate::leanh::LeanObject,
    mut v_c_106_: u32,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: u8 = 0;
    v___x_107_ = crate::leanh::lean_unsigned_to_nat(1112064);
    v___x_108_ = l_Char_ordinal(v_c_106_);
    v___x_109_ = lean_nat_add(v___x_108_, v_m_105_);
    crate::leanh::lean_dec(v___x_108_);
    v___x_110_ = lean_nat_dec_lt(v___x_109_, v___x_107_);
    if v___x_110_ == 0 {
        let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_109_);
        v___x_111_ = crate::leanh::lean_box(0);
        return v___x_111_;
    } else {
        let mut v___x_112_: u32 = 0;
        let mut v___x_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_112_ = l_Char_ofOrdinal(v___x_109_);
        crate::leanh::lean_dec(v___x_109_);
        v___x_113_ = crate::leanh::lean_box_uint32(v___x_112_);
        v___x_114_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_114_, 0, v___x_113_);
        return v___x_114_;
    }
}
pub unsafe fn l_Char_succMany_x3f___boxed(
    mut v_m_115_: *mut crate::leanh::LeanObject,
    mut v_c_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_c_boxed_117_: u32 = 0;
    let mut v_res_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_c_boxed_117_ = crate::leanh::lean_unbox_uint32(v_c_116_);
    crate::leanh::lean_dec(v_c_116_);
    v_res_118_ = l_Char_succMany_x3f(v_m_115_, v_c_boxed_117_);
    crate::leanh::lean_dec(v_m_115_);
    return v_res_118_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Char_Ordinal(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Fin_OverflowAware(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Char_numSurrogates = _init_l_Char_numSurrogates();
    crate::leanh::lean_mark_persistent(l_Char_numSurrogates);
    l_Char_numCodePoints = _init_l_Char_numCodePoints();
    crate::leanh::lean_mark_persistent(l_Char_numCodePoints);
    l_Char_succ_x3f___closed__0___boxed__const__1 =
        _init_l_Char_succ_x3f___closed__0___boxed__const__1();
    crate::leanh::lean_mark_persistent(l_Char_succ_x3f___closed__0___boxed__const__1);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Char_Ordinal(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Char_Ordinal(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Fin_OverflowAware(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Function(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Int_OfNat(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_UInt_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Ordinal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Char_Ordinal(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Char_Ordinal(builtin);
}

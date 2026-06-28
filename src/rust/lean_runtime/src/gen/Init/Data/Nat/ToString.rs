// Lean compiler output
// Module: Init.Data.Nat.ToString
// Imports: Init.Data.Repr Init.Data.Char.Basic Init.Data.ToString.Basic Init.Data.String.Basic Init.Data.String.Length Init.NotationExtra Init.Data.Repr Init.Omega Init.RCases Init.Data.Nat.Lemmas Init.Data.Nat.Bitwise Init.Data.Nat.Simproc Init.WFTactics Init.Data.Char.Lemmas Init.Data.Nat.Div.Lemmas
use crate::r#gen::Init::Data::Char::Basic::{
    initialize_Init_Data_Char_Basic, runtime_initialize_Init_Data_Char_Basic,
};
use crate::r#gen::Init::Data::Char::Lemmas::{
    initialize_Init_Data_Char_Lemmas, runtime_initialize_Init_Data_Char_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Bitwise::{
    initialize_Init_Data_Nat_Bitwise, runtime_initialize_Init_Data_Nat_Bitwise,
};
use crate::r#gen::Init::Data::Nat::Div::Lemmas::{
    initialize_Init_Data_Nat_Div_Lemmas, runtime_initialize_Init_Data_Nat_Div_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Simproc::{
    initialize_Init_Data_Nat_Simproc, runtime_initialize_Init_Data_Nat_Simproc,
};
use crate::r#gen::Init::Data::Repr::{
    initialize_Init_Data_Repr, runtime_initialize_Init_Data_Repr,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Length::{
    initialize_Init_Data_String_Length, runtime_initialize_Init_Data_String_Length,
};
use crate::r#gen::Init::Data::ToString::Basic::{
    initialize_Init_Data_ToString_Basic, runtime_initialize_Init_Data_ToString_Basic,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_mul, lean_nat_sub, lean_uint32_to_nat,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_apply_2, lean_apply_3, lean_box, lean_ctor_get, lean_dec,
    lean_dec_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag, lean_unbox_uint32,
    lean_unsigned_to_nat,
};
pub unsafe fn l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg(
    mut v_x_61_: *mut LeanObject,
    mut v_x_62_: *mut LeanObject,
    mut v_x_63_: *mut LeanObject,
    mut v_h__1_64_: *mut LeanObject,
    mut v_h__2_65_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_66_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_67_: u8 = 0;
    v_zero_66_ = lean_unsigned_to_nat(0);
    v_isZero_67_ = lean_nat_dec_eq(v_x_61_, v_zero_66_);
    if v_isZero_67_ == 1 {
        let mut v___x_68_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_65_);
        v___x_68_ = lean_apply_2(v_h__1_64_, v_x_62_, v_x_63_);
        return v___x_68_;
    } else {
        let mut v_one_69_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_70_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_71_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_64_);
        v_one_69_ = lean_unsigned_to_nat(1);
        v_n_70_ = lean_nat_sub(v_x_61_, v_one_69_);
        v___x_71_ = lean_apply_3(v_h__2_65_, v_n_70_, v_x_62_, v_x_63_);
        return v___x_71_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg___boxed(
    mut v_x_72_: *mut LeanObject,
    mut v_x_73_: *mut LeanObject,
    mut v_x_74_: *mut LeanObject,
    mut v_h__1_75_: *mut LeanObject,
    mut v_h__2_76_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_77_: *mut LeanObject = core::ptr::null_mut();
    v_res_77_ = l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___redArg(
        v_x_72_, v_x_73_, v_x_74_, v_h__1_75_, v_h__2_76_,
    );
    lean_dec(v_x_72_);
    return v_res_77_;
}
pub unsafe fn l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter(
    mut v_motive_78_: *mut LeanObject,
    mut v_x_79_: *mut LeanObject,
    mut v_x_80_: *mut LeanObject,
    mut v_x_81_: *mut LeanObject,
    mut v_h__1_82_: *mut LeanObject,
    mut v_h__2_83_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_zero_84_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_85_: u8 = 0;
    v_zero_84_ = lean_unsigned_to_nat(0);
    v_isZero_85_ = lean_nat_dec_eq(v_x_79_, v_zero_84_);
    if v_isZero_85_ == 1 {
        let mut v___x_86_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_83_);
        v___x_86_ = lean_apply_2(v_h__1_82_, v_x_80_, v_x_81_);
        return v___x_86_;
    } else {
        let mut v_one_87_: *mut LeanObject = core::ptr::null_mut();
        let mut v_n_88_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_89_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_82_);
        v_one_87_ = lean_unsigned_to_nat(1);
        v_n_88_ = lean_nat_sub(v_x_79_, v_one_87_);
        v___x_89_ = lean_apply_3(v_h__2_83_, v_n_88_, v_x_80_, v_x_81_);
        return v___x_89_;
    }
}
pub unsafe fn l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter___boxed(
    mut v_motive_90_: *mut LeanObject,
    mut v_x_91_: *mut LeanObject,
    mut v_x_92_: *mut LeanObject,
    mut v_x_93_: *mut LeanObject,
    mut v_h__1_94_: *mut LeanObject,
    mut v_h__2_95_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_96_: *mut LeanObject = core::ptr::null_mut();
    v_res_96_ = l___private_Init_Data_Nat_ToString_0__Nat_toDigitsCore_match__1_splitter(
        v_motive_90_,
        v_x_91_,
        v_x_92_,
        v_x_93_,
        v_h__1_94_,
        v_h__2_95_,
    );
    lean_dec(v_x_91_);
    return v_res_96_;
}
pub unsafe fn l_List_foldl___at___00Nat_ofDigitChars_spec__0(
    mut v_b_97_: *mut LeanObject,
    mut v_x_98_: *mut LeanObject,
    mut v_x_99_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_head_100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_103_: u32 = 0;
    let mut v___x_104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_99_) == 0 {
                    return v_x_98_;
                } else {
                    v_head_100_ = lean_ctor_get(v_x_99_, 0);
                    v_tail_101_ = lean_ctor_get(v_x_99_, 1);
                    v___x_102_ = lean_nat_mul(v_b_97_, v_x_98_);
                    lean_dec(v_x_98_);
                    v___x_103_ = lean_unbox_uint32(v_head_100_);
                    v___x_104_ = lean_uint32_to_nat(v___x_103_);
                    v___x_105_ = lean_unsigned_to_nat(48);
                    v___x_106_ = lean_nat_sub(v___x_104_, v___x_105_);
                    lean_dec(v___x_104_);
                    v___x_107_ = lean_nat_add(v___x_102_, v___x_106_);
                    lean_dec(v___x_106_);
                    lean_dec(v___x_102_);
                    v_x_98_ = v___x_107_;
                    v_x_99_ = v_tail_101_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_foldl___at___00Nat_ofDigitChars_spec__0___boxed(
    mut v_b_109_: *mut LeanObject,
    mut v_x_110_: *mut LeanObject,
    mut v_x_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_112_: *mut LeanObject = core::ptr::null_mut();
    v_res_112_ = l_List_foldl___at___00Nat_ofDigitChars_spec__0(v_b_109_, v_x_110_, v_x_111_);
    lean_dec(v_x_111_);
    lean_dec(v_b_109_);
    return v_res_112_;
}
pub unsafe fn l_Nat_ofDigitChars(
    mut v_b_113_: *mut LeanObject,
    mut v_l_114_: *mut LeanObject,
    mut v_init_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_116_: *mut LeanObject = core::ptr::null_mut();
    v___x_116_ = l_List_foldl___at___00Nat_ofDigitChars_spec__0(v_b_113_, v_init_115_, v_l_114_);
    return v___x_116_;
}
pub unsafe fn l_Nat_ofDigitChars___boxed(
    mut v_b_117_: *mut LeanObject,
    mut v_l_118_: *mut LeanObject,
    mut v_init_119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_120_: *mut LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Nat_ofDigitChars(v_b_117_, v_l_118_, v_init_119_);
    lean_dec(v_l_118_);
    lean_dec(v_b_117_);
    return v_res_120_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Nat_ToString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
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
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Bitwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Char_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Nat_ToString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Nat_ToString(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Repr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Char_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Length(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
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
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Bitwise(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Simproc(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Char_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Div_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Nat_ToString(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Nat_ToString(builtin);
}

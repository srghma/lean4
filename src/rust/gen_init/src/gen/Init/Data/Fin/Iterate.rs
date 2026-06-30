// Lean compiler output
// Module: Init.Data.Fin.Iterate
// Imports: Init.Data.Fin.Basic Init.PropLemmas Init.WFTactics Init.Hints
use crate::ffi::{lean_nat_add, lean_nat_dec_lt};
use crate::r#gen::Init::Data::Fin::Basic::{
    initialize_Init_Data_Fin_Basic, runtime_initialize_Init_Data_Fin_Basic,
};
use crate::r#gen::Init::Hints::{initialize_Init_Hints, runtime_initialize_Init_Hints};
use crate::r#gen::Init::PropLemmas::{
    initialize_Init_PropLemmas, runtime_initialize_Init_PropLemmas,
};
use crate::r#gen::Init::WFTactics::{initialize_Init_WFTactics, runtime_initialize_Init_WFTactics};
pub unsafe fn l_Fin_hIterateFrom___redArg(
    mut v_n_48_: *mut leanh::LeanObject,
    mut v_f_49_: *mut leanh::LeanObject,
    mut v_i_50_: *mut leanh::LeanObject,
    mut v_a_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_52_: u8 = 0;
    let mut v___x_53_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_55_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_52_ = lean_nat_dec_lt(v_i_50_, v_n_48_);
                if v___x_52_ == 0 {
                    leanh::lean_dec(v_i_50_);
                    leanh::lean_dec(v_f_49_);
                    return v_a_51_;
                } else {
                    v___x_53_ = leanh::lean_unsigned_to_nat(1);
                    v___x_54_ = lean_nat_add(v_i_50_, v___x_53_);
                    leanh::lean_inc(v_f_49_);
                    v___x_55_ = leanh::lean_apply_2(v_f_49_, v_i_50_, v_a_51_);
                    v_i_50_ = v___x_54_;
                    v_a_51_ = v___x_55_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Fin_hIterateFrom___redArg___boxed(
    mut v_n_57_: *mut leanh::LeanObject,
    mut v_f_58_: *mut leanh::LeanObject,
    mut v_i_59_: *mut leanh::LeanObject,
    mut v_a_60_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_61_ = l_Fin_hIterateFrom___redArg(v_n_57_, v_f_58_, v_i_59_, v_a_60_);
    leanh::lean_dec(v_n_57_);
    return v_res_61_;
}
pub unsafe fn l_Fin_hIterateFrom(
    mut v_P_62_: *mut leanh::LeanObject,
    mut v_n_63_: *mut leanh::LeanObject,
    mut v_f_64_: *mut leanh::LeanObject,
    mut v_i_65_: *mut leanh::LeanObject,
    mut v_ubnd_66_: *mut leanh::LeanObject,
    mut v_a_67_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_68_ = l_Fin_hIterateFrom___redArg(v_n_63_, v_f_64_, v_i_65_, v_a_67_);
    return v___x_68_;
}
pub unsafe fn l_Fin_hIterateFrom___boxed(
    mut v_P_69_: *mut leanh::LeanObject,
    mut v_n_70_: *mut leanh::LeanObject,
    mut v_f_71_: *mut leanh::LeanObject,
    mut v_i_72_: *mut leanh::LeanObject,
    mut v_ubnd_73_: *mut leanh::LeanObject,
    mut v_a_74_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_75_ = l_Fin_hIterateFrom(v_P_69_, v_n_70_, v_f_71_, v_i_72_, v_ubnd_73_, v_a_74_);
    leanh::lean_dec(v_n_70_);
    return v_res_75_;
}
pub unsafe fn l_Fin_hIterate___redArg(
    mut v_n_76_: *mut leanh::LeanObject,
    mut v_init_77_: *mut leanh::LeanObject,
    mut v_f_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_80_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = leanh::lean_unsigned_to_nat(0);
    v___x_80_ = l_Fin_hIterateFrom___redArg(v_n_76_, v_f_78_, v___x_79_, v_init_77_);
    return v___x_80_;
}
pub unsafe fn l_Fin_hIterate___redArg___boxed(
    mut v_n_81_: *mut leanh::LeanObject,
    mut v_init_82_: *mut leanh::LeanObject,
    mut v_f_83_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_84_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_84_ = l_Fin_hIterate___redArg(v_n_81_, v_init_82_, v_f_83_);
    leanh::lean_dec(v_n_81_);
    return v_res_84_;
}
pub unsafe fn l_Fin_hIterate(
    mut v_P_85_: *mut leanh::LeanObject,
    mut v_n_86_: *mut leanh::LeanObject,
    mut v_init_87_: *mut leanh::LeanObject,
    mut v_f_88_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_89_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_89_ = l_Fin_hIterate___redArg(v_n_86_, v_init_87_, v_f_88_);
    return v___x_89_;
}
pub unsafe fn l_Fin_hIterate___boxed(
    mut v_P_90_: *mut leanh::LeanObject,
    mut v_n_91_: *mut leanh::LeanObject,
    mut v_init_92_: *mut leanh::LeanObject,
    mut v_f_93_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_94_ = l_Fin_hIterate(v_P_90_, v_n_91_, v_init_92_, v_f_93_);
    leanh::lean_dec(v_n_91_);
    return v_res_94_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Fin_Iterate(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Hints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Fin_Iterate(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Fin_Iterate(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Fin_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_PropLemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_WFTactics(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Hints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Fin_Iterate(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Fin_Iterate(builtin);
}
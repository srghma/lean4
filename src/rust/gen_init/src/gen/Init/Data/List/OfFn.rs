// Lean compiler output
// Module: Init.Data.List.OfFn
// Imports: Init.Data.Fin.Fold Init.NotationExtra Init.Data.Fin.Lemmas Init.Data.List.Lemmas Init.Data.Nat.Lemmas Init.Data.Option.Lemmas
use crate::ffi::{lean_nat_dec_eq, lean_nat_sub};
use crate::r#gen::Init::Data::Fin::Fold::{
    initialize_Init_Data_Fin_Fold, l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop,
    runtime_initialize_Init_Data_Fin_Fold,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse;
use crate::r#gen::Init::Data::List::Lemmas::{
    initialize_Init_Data_List_Lemmas, runtime_initialize_Init_Data_List_Lemmas,
};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::NotationExtra::{
    initialize_Init_NotationExtra, runtime_initialize_Init_NotationExtra,
};
pub static l_List_ofFnM___redArg___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_List_reverse as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_List_ofFnM___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_List_ofFnM___redArg___closed__0_value) as *mut leanh::LeanObject;
pub unsafe fn l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(
    mut v_f_62_: *mut leanh::LeanObject,
    mut v_i_63_: *mut leanh::LeanObject,
    mut v_a_64_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_65_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_66_: u8 = 0;
    let mut v_one_67_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_68_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_69_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_70_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_65_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_66_ = lean_nat_dec_eq(v_i_63_, v_zero_65_);
                if v_isZero_66_ == 1 {
                    leanh::lean_dec(v_i_63_);
                    leanh::lean_dec(v_f_62_);
                    return v_a_64_;
                } else {
                    v_one_67_ = leanh::lean_unsigned_to_nat(1);
                    v_n_68_ = lean_nat_sub(v_i_63_, v_one_67_);
                    leanh::lean_dec(v_i_63_);
                    leanh::lean_inc(v_f_62_);
                    leanh::lean_inc(v_n_68_);
                    v___x_69_ = leanh::lean_apply_1(v_f_62_, v_n_68_);
                    v___x_70_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_70_, 0, v___x_69_);
                    leanh::lean_ctor_set(v___x_70_, 1, v_a_64_);
                    v_i_63_ = v_n_68_;
                    v_a_64_ = v___x_70_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_ofFn___redArg(
    mut v_n_72_: *mut leanh::LeanObject,
    mut v_f_73_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_74_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_75_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_74_ = leanh::lean_box(0);
    v___x_75_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(v_f_73_, v_n_72_, v___x_74_);
    return v___x_75_;
}
pub unsafe fn l_List_ofFn(
    mut v_00_u03b1_76_: *mut leanh::LeanObject,
    mut v_n_77_: *mut leanh::LeanObject,
    mut v_f_78_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_79_ = l_List_ofFn___redArg(v_n_77_, v_f_78_);
    return v___x_79_;
}
pub unsafe fn l_Fin_foldr_loop___at___00List_ofFn_spec__0(
    mut v_00_u03b1_80_: *mut leanh::LeanObject,
    mut v_f_81_: *mut leanh::LeanObject,
    mut v_n_82_: *mut leanh::LeanObject,
    mut v_i_83_: *mut leanh::LeanObject,
    mut v_a_84_: *mut leanh::LeanObject,
    mut v_a_85_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_86_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_86_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0___redArg(v_f_81_, v_i_83_, v_a_85_);
    return v___x_86_;
}
pub unsafe fn l_Fin_foldr_loop___at___00List_ofFn_spec__0___boxed(
    mut v_00_u03b1_87_: *mut leanh::LeanObject,
    mut v_f_88_: *mut leanh::LeanObject,
    mut v_n_89_: *mut leanh::LeanObject,
    mut v_i_90_: *mut leanh::LeanObject,
    mut v_a_91_: *mut leanh::LeanObject,
    mut v_a_92_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_93_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_93_ = l_Fin_foldr_loop___at___00List_ofFn_spec__0(
        v_00_u03b1_87_,
        v_f_88_,
        v_n_89_,
        v_i_90_,
        v_a_91_,
        v_a_92_,
    );
    leanh::lean_dec(v_n_89_);
    return v_res_93_;
}
pub unsafe fn l_List_ofFnM___redArg___lam__0(
    mut v_xs_94_: *mut leanh::LeanObject,
    mut v_x_95_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_96_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_96_, 0, v_x_95_);
    leanh::lean_ctor_set(v___x_96_, 1, v_xs_94_);
    return v___x_96_;
}
pub unsafe fn l_List_ofFnM___redArg___lam__1(
    mut v_f_97_: *mut leanh::LeanObject,
    mut v_map_98_: *mut leanh::LeanObject,
    mut v_xs_99_: *mut leanh::LeanObject,
    mut v_i_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_101_ = leanh::lean_alloc_closure(
        l_List_ofFnM___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_101_, 0, v_xs_99_);
    v___x_102_ = leanh::lean_apply_1(v_f_97_, v_i_100_);
    v___x_103_ = leanh::lean_apply_4(
        v_map_98_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___f_101_,
        v___x_102_,
    );
    return v___x_103_;
}
pub unsafe fn l_List_ofFnM___redArg(
    mut v_n_105_: *mut leanh::LeanObject,
    mut v_inst_106_: *mut leanh::LeanObject,
    mut v_f_107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_108_ = leanh::lean_ctor_get(v_inst_106_, 0);
    v_toFunctor_109_ = leanh::lean_ctor_get(v_toApplicative_108_, 0);
    v_map_110_ = leanh::lean_ctor_get(v_toFunctor_109_, 0);
    leanh::lean_inc_n(v_map_110_, 2);
    v___f_111_ = leanh::lean_alloc_closure(
        l_List_ofFnM___redArg___lam__1 as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_111_, 0, v_f_107_);
    leanh::lean_closure_set(v___f_111_, 1, v_map_110_);
    v___x_112_ = l_List_ofFnM___redArg___closed__0;
    v___x_113_ = leanh::lean_box(0);
    v___x_114_ = leanh::lean_unsigned_to_nat(0);
    v___x_115_ = l___private_Init_Data_Fin_Fold_0__Fin_foldlM_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_106_,
        v_n_105_,
        v___f_111_,
        v___x_113_,
        v___x_114_,
    );
    v___x_116_ = leanh::lean_apply_4(
        v_map_110_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_112_,
        v___x_115_,
    );
    return v___x_116_;
}
pub unsafe fn l_List_ofFnM(
    mut v_m_117_: *mut leanh::LeanObject,
    mut v_00_u03b1_118_: *mut leanh::LeanObject,
    mut v_n_119_: *mut leanh::LeanObject,
    mut v_inst_120_: *mut leanh::LeanObject,
    mut v_f_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_122_ = l_List_ofFnM___redArg(v_n_119_, v_inst_120_, v_f_121_);
    return v___x_122_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_OfFn(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Fin_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_OfFn(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_OfFn(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Fin_Fold(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_NotationExtra(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_OfFn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_OfFn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_List_OfFn(builtin);
}
// Lean compiler output
// Module: Init.Data.Array.Subarray.Split
// Imports: Init.Data.Array.Subarray Init.Data.Array.Subarray Init.Omega
use crate::ffi::{lean_nat_add, lean_nat_dec_le};
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l_Subarray_drop___redArg(
    mut v_arr_73_: *mut crate::leanh::LeanObject,
    mut v_i_74_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_75_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_76_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_77_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_80_: u8 = 0;
    let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_82_: u8 = 0;
    let mut v___x_84_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_85_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_89_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_75_ = crate::leanh::lean_ctor_get(v_arr_73_, 0);
                v_start_76_ = crate::leanh::lean_ctor_get(v_arr_73_, 1);
                v_stop_77_ = crate::leanh::lean_ctor_get(v_arr_73_, 2);
                v_isSharedCheck_89_ = (!crate::leanh::lean_is_exclusive(v_arr_73_)) as u8;
                if v_isSharedCheck_89_ == 0 {
                    v___x_79_ = v_arr_73_;
                    v_isShared_80_ = v_isSharedCheck_89_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_77_);
                    crate::leanh::lean_inc(v_start_76_);
                    crate::leanh::lean_inc(v_array_75_);
                    crate::leanh::lean_dec(v_arr_73_);
                    v___x_79_ = crate::leanh::lean_box(0);
                    v_isShared_80_ = v_isSharedCheck_89_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_81_ = lean_nat_add(v_start_76_, v_i_74_);
                crate::leanh::lean_dec(v_start_76_);
                v___x_82_ = lean_nat_dec_le(v___x_81_, v_stop_77_);
                if v___x_82_ == 0 {
                    crate::leanh::lean_dec(v___x_81_);
                    crate::leanh::lean_inc(v_stop_77_);
                    if v_isShared_80_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_79_, 1, v_stop_77_);
                        v___x_84_ = v___x_79_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_85_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_85_, 0, v_array_75_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_85_, 1, v_stop_77_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_85_, 2, v_stop_77_);
                        v___x_84_ = v_reuseFailAlloc_85_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_80_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_79_, 1, v___x_81_);
                        v___x_87_ = v___x_79_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_88_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_88_, 0, v_array_75_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_88_, 1, v___x_81_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_88_, 2, v_stop_77_);
                        v___x_87_ = v_reuseFailAlloc_88_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_84_;
            }
            3 => {
                return v___x_87_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_drop___redArg___boxed(
    mut v_arr_90_: *mut crate::leanh::LeanObject,
    mut v_i_91_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_92_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_92_ = l_Subarray_drop___redArg(v_arr_90_, v_i_91_);
    crate::leanh::lean_dec(v_i_91_);
    return v_res_92_;
}
pub unsafe fn l_Subarray_drop(
    mut v_00_u03b1_93_: *mut crate::leanh::LeanObject,
    mut v_arr_94_: *mut crate::leanh::LeanObject,
    mut v_i_95_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_96_ = l_Subarray_drop___redArg(v_arr_94_, v_i_95_);
    return v___x_96_;
}
pub unsafe fn l_Subarray_drop___boxed(
    mut v_00_u03b1_97_: *mut crate::leanh::LeanObject,
    mut v_arr_98_: *mut crate::leanh::LeanObject,
    mut v_i_99_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_100_ = l_Subarray_drop(v_00_u03b1_97_, v_arr_98_, v_i_99_);
    crate::leanh::lean_dec(v_i_99_);
    return v_res_100_;
}
pub unsafe fn l_Subarray_take___redArg(
    mut v_arr_101_: *mut crate::leanh::LeanObject,
    mut v_i_102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_108_: u8 = 0;
    let mut v___x_109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: u8 = 0;
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_117_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_103_ = crate::leanh::lean_ctor_get(v_arr_101_, 0);
                v_start_104_ = crate::leanh::lean_ctor_get(v_arr_101_, 1);
                v_stop_105_ = crate::leanh::lean_ctor_get(v_arr_101_, 2);
                v_isSharedCheck_117_ = (!crate::leanh::lean_is_exclusive(v_arr_101_)) as u8;
                if v_isSharedCheck_117_ == 0 {
                    v___x_107_ = v_arr_101_;
                    v_isShared_108_ = v_isSharedCheck_117_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_105_);
                    crate::leanh::lean_inc(v_start_104_);
                    crate::leanh::lean_inc(v_array_103_);
                    crate::leanh::lean_dec(v_arr_101_);
                    v___x_107_ = crate::leanh::lean_box(0);
                    v_isShared_108_ = v_isSharedCheck_117_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_109_ = lean_nat_add(v_start_104_, v_i_102_);
                v___x_110_ = lean_nat_dec_le(v___x_109_, v_stop_105_);
                if v___x_110_ == 0 {
                    crate::leanh::lean_dec(v___x_109_);
                    if v_isShared_108_ == 0 {
                        v___x_112_ = v___x_107_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_113_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_113_, 0, v_array_103_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_113_, 1, v_start_104_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_113_, 2, v_stop_105_);
                        v___x_112_ = v_reuseFailAlloc_113_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_stop_105_);
                    if v_isShared_108_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_107_, 2, v___x_109_);
                        v___x_115_ = v___x_107_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_116_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_116_, 0, v_array_103_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_116_, 1, v_start_104_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_116_, 2, v___x_109_);
                        v___x_115_ = v_reuseFailAlloc_116_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_112_;
            }
            3 => {
                return v___x_115_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Subarray_take___redArg___boxed(
    mut v_arr_118_: *mut crate::leanh::LeanObject,
    mut v_i_119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_120_ = l_Subarray_take___redArg(v_arr_118_, v_i_119_);
    crate::leanh::lean_dec(v_i_119_);
    return v_res_120_;
}
pub unsafe fn l_Subarray_take(
    mut v_00_u03b1_121_: *mut crate::leanh::LeanObject,
    mut v_arr_122_: *mut crate::leanh::LeanObject,
    mut v_i_123_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = l_Subarray_take___redArg(v_arr_122_, v_i_123_);
    return v___x_124_;
}
pub unsafe fn l_Subarray_take___boxed(
    mut v_00_u03b1_125_: *mut crate::leanh::LeanObject,
    mut v_arr_126_: *mut crate::leanh::LeanObject,
    mut v_i_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l_Subarray_take(v_00_u03b1_125_, v_arr_126_, v_i_127_);
    crate::leanh::lean_dec(v_i_127_);
    return v_res_128_;
}
pub unsafe fn l_Subarray_split___redArg(
    mut v_s_129_: *mut crate::leanh::LeanObject,
    mut v_i_130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_129_);
    v___x_131_ = l_Subarray_take___redArg(v_s_129_, v_i_130_);
    v___x_132_ = l_Subarray_drop___redArg(v_s_129_, v_i_130_);
    v___x_133_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_133_, 0, v___x_131_);
    crate::leanh::lean_ctor_set(v___x_133_, 1, v___x_132_);
    return v___x_133_;
}
pub unsafe fn l_Subarray_split___redArg___boxed(
    mut v_s_134_: *mut crate::leanh::LeanObject,
    mut v_i_135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_136_ = l_Subarray_split___redArg(v_s_134_, v_i_135_);
    crate::leanh::lean_dec(v_i_135_);
    return v_res_136_;
}
pub unsafe fn l_Subarray_split(
    mut v_00_u03b1_137_: *mut crate::leanh::LeanObject,
    mut v_s_138_: *mut crate::leanh::LeanObject,
    mut v_i_139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_140_ = l_Subarray_split___redArg(v_s_138_, v_i_139_);
    return v___x_140_;
}
pub unsafe fn l_Subarray_split___boxed(
    mut v_00_u03b1_141_: *mut crate::leanh::LeanObject,
    mut v_s_142_: *mut crate::leanh::LeanObject,
    mut v_i_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_144_ = l_Subarray_split(v_00_u03b1_141_, v_s_142_, v_i_143_);
    crate::leanh::lean_dec(v_i_143_);
    return v_res_144_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Subarray_Split(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_Subarray_Split(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Subarray_Split(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Subarray_Split(builtin);
}

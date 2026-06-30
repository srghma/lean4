// Lean compiler output
// Module: Lean.ImportingFlag
// Imports: Init.System.IO
use crate::ffi::{lean_io_initializing, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
pub static mut l___private_Lean_ImportingFlag_0__Lean_importingRef: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_ImportingFlag_0__Lean_runInitializersRef:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_102_: u8 = 0;
    let mut v___x_103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_102_ = 0;
    v___x_103_ = leanh::lean_box((v___x_102_) as usize);
    v___x_104_ = lean_st_mk_ref(v___x_103_);
    v___x_105_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_105_, 0, v___x_104_);
    return v___x_105_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(
    mut v_a_106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_107_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_107_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
    return v_res_107_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_109_: u8 = 0;
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_109_ = 0;
    v___x_110_ = leanh::lean_box((v___x_109_) as usize);
    v___x_111_ = lean_st_mk_ref(v___x_110_);
    v___x_112_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_112_, 0, v___x_111_);
    return v___x_112_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(
    mut v_a_113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_114_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
    return v_res_114_;
}
pub unsafe fn lean_enable_initializer_execution() -> *mut leanh::LeanObject {
    let mut v___x_116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_116_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_117_ = 1;
    v___x_118_ = leanh::lean_box((v___x_117_) as usize);
    v___x_119_ = lean_st_ref_set(v___x_116_, v___x_118_);
    v___x_120_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_120_, 0, v___x_119_);
    return v___x_120_;
}
pub unsafe fn l_Lean_enableInitializersExecution___boxed(
    mut v_a_121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_122_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = lean_enable_initializer_execution();
    return v_res_122_;
}
pub unsafe fn l_Lean_isInitializerExecutionEnabled() -> *mut leanh::LeanObject {
    let mut v___x_124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_125_ = lean_st_ref_get(v___x_124_);
    v___x_126_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_126_, 0, v___x_125_);
    return v___x_126_;
}
pub unsafe fn l_Lean_isInitializerExecutionEnabled___boxed(
    mut v_a_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l_Lean_isInitializerExecutionEnabled();
    return v_res_128_;
}
pub unsafe fn l_Lean_initializing() -> *mut leanh::LeanObject {
    let mut v___x_130_: u8 = 0;
    v___x_130_ = lean_io_initializing();
    if v___x_130_ == 0 {
        let mut v___x_131_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_131_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
        v___x_132_ = lean_st_ref_get(v___x_131_);
        v___x_133_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_133_, 0, v___x_132_);
        return v___x_133_;
    } else {
        let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_134_ = leanh::lean_box((v___x_130_) as usize);
        v___x_135_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_135_, 0, v___x_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Lean_initializing___boxed(
    mut v_a_136_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l_Lean_initializing();
    return v_res_137_;
}
pub unsafe fn l_Lean_withImporting___redArg___lam__0(
    mut v___x_138_: *mut leanh::LeanObject,
    mut v___x_139_: u8,
    mut v_x_140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = leanh::lean_box((v___x_139_) as usize);
    v___x_143_ = lean_st_ref_set(v___x_138_, v___x_142_);
    v___x_144_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_145_ = leanh::lean_box((v___x_139_) as usize);
    v___x_146_ = lean_st_ref_set(v___x_144_, v___x_145_);
    v___x_147_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_147_, 0, v___x_146_);
    return v___x_147_;
}
pub unsafe fn l_Lean_withImporting___redArg___lam__0___boxed(
    mut v___x_148_: *mut leanh::LeanObject,
    mut v___x_149_: *mut leanh::LeanObject,
    mut v_x_150_: *mut leanh::LeanObject,
    mut v___y_151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_331__boxed_152_: u8 = 0;
    let mut v_res_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_331__boxed_152_ = (leanh::lean_unbox(v___x_149_) as u8);
    v_res_153_ =
        l_Lean_withImporting___redArg___lam__0(v___x_148_, v___x_331__boxed_152_, v_x_150_);
    leanh::lean_dec(v_x_150_);
    leanh::lean_dec(v___x_148_);
    return v_res_153_;
}
pub unsafe fn l_Lean_withImporting___redArg(
    mut v_x_154_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: u8 = 0;
    let mut v_r_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_165_: u8 = 0;
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_171_: u8 = 0;
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_175_: u8 = 0;
    let mut v_unused_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut v_a_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_184_: u8 = 0;
    let mut v___x_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_188_: u8 = 0;
    let mut v_unused_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_156_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
                v___x_157_ = 1;
                v___x_158_ = leanh::lean_box((v___x_157_) as usize);
                v___x_159_ = lean_st_ref_set(v___x_156_, v___x_158_);
                v___x_160_ = 0;
                v_r_161_ = leanh::lean_apply_1(v_x_154_, leanh::lean_box(0));
                if leanh::lean_obj_tag(v_r_161_) == 0 {
                    v_a_162_ = leanh::lean_ctor_get(v_r_161_, 0);
                    v_isSharedCheck_178_ = (!leanh::lean_is_exclusive(v_r_161_)) as u8;
                    if v_isSharedCheck_178_ == 0 {
                        v___x_164_ = v_r_161_;
                        v_isShared_165_ = v_isSharedCheck_178_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_162_);
                        leanh::lean_dec(v_r_161_);
                        v___x_164_ = leanh::lean_box(0);
                        v_isShared_165_ = v_isSharedCheck_178_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_179_ = leanh::lean_ctor_get(v_r_161_, 0);
                    leanh::lean_inc(v_a_179_);
                    leanh::lean_dec_ref_known(v_r_161_, 1);
                    v___x_180_ = leanh::lean_box(0);
                    v___x_181_ =
                        l_Lean_withImporting___redArg___lam__0(v___x_156_, v___x_160_, v___x_180_);
                    v_isSharedCheck_188_ = (!leanh::lean_is_exclusive(v___x_181_)) as u8;
                    if v_isSharedCheck_188_ == 0 {
                        v_unused_189_ = leanh::lean_ctor_get(v___x_181_, 0);
                        leanh::lean_dec(v_unused_189_);
                        v___x_183_ = v___x_181_;
                        v_isShared_184_ = v_isSharedCheck_188_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_181_);
                        v___x_183_ = leanh::lean_box(0);
                        v_isShared_184_ = v_isSharedCheck_188_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_162_);
                if v_isShared_165_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_164_, 1);
                    v___x_167_ = v___x_164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_177_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_162_);
                    v___x_167_ = v_reuseFailAlloc_177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_168_ =
                    l_Lean_withImporting___redArg___lam__0(v___x_156_, v___x_160_, v___x_167_);
                leanh::lean_dec_ref(v___x_167_);
                v_isSharedCheck_175_ = (!leanh::lean_is_exclusive(v___x_168_)) as u8;
                if v_isSharedCheck_175_ == 0 {
                    v_unused_176_ = leanh::lean_ctor_get(v___x_168_, 0);
                    leanh::lean_dec(v_unused_176_);
                    v___x_170_ = v___x_168_;
                    v_isShared_171_ = v_isSharedCheck_175_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_168_);
                    v___x_170_ = leanh::lean_box(0);
                    v_isShared_171_ = v_isSharedCheck_175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_171_ == 0 {
                    leanh::lean_ctor_set(v___x_170_, 0, v_a_162_);
                    v___x_173_ = v___x_170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_174_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_162_);
                    v___x_173_ = v_reuseFailAlloc_174_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_173_;
            }
            5 => {
                if v_isShared_184_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_183_, 1);
                    leanh::lean_ctor_set(v___x_183_, 0, v_a_179_);
                    v___x_186_ = v___x_183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_179_);
                    v___x_186_ = v_reuseFailAlloc_187_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_186_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_withImporting___redArg___boxed(
    mut v_x_190_: *mut leanh::LeanObject,
    mut v_a_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_withImporting___redArg(v_x_190_);
    return v_res_192_;
}
pub unsafe fn l_Lean_withImporting(
    mut v_00_u03b1_193_: *mut leanh::LeanObject,
    mut v_x_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_196_ = l_Lean_withImporting___redArg(v_x_194_);
    return v___x_196_;
}
pub unsafe fn l_Lean_withImporting___boxed(
    mut v_00_u03b1_197_: *mut leanh::LeanObject,
    mut v_x_198_: *mut leanh::LeanObject,
    mut v_a_199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Lean_withImporting(v_00_u03b1_197_, v_x_198_);
    return v_res_200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ImportingFlag(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ImportingFlag_0__Lean_importingRef =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_importingRef);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ImportingFlag_0__Lean_runInitializersRef =
        leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_runInitializersRef);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ImportingFlag(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ImportingFlag(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ImportingFlag(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ImportingFlag(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_ImportingFlag(builtin);
}
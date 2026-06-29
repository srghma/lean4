// Lean compiler output
// Module: Lean.ImportingFlag
// Imports: Init.System.IO
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::ffi::lean_io_initializing;
use crate::ffi::{lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set};
pub static mut l___private_Lean_ImportingFlag_0__Lean_importingRef: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l___private_Lean_ImportingFlag_0__Lean_runInitializersRef:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_102_: u8 = 0;
    let mut v___x_103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_102_ = 0;
    v___x_103_ = crate::leanh::lean_box((v___x_102_) as usize);
    v___x_104_ = lean_st_mk_ref(v___x_103_);
    v___x_105_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_105_, 0, v___x_104_);
    return v___x_105_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2____boxed(
    mut v_a_106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_107_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
    return v_res_107_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_109_: u8 = 0;
    let mut v___x_110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_109_ = 0;
    v___x_110_ = crate::leanh::lean_box((v___x_109_) as usize);
    v___x_111_ = lean_st_mk_ref(v___x_110_);
    v___x_112_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_112_, 0, v___x_111_);
    return v___x_112_;
}
pub unsafe fn l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2____boxed(
    mut v_a_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_114_ = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
    return v_res_114_;
}
pub unsafe fn lean_enable_initializer_execution() -> *mut crate::leanh::LeanObject {
    let mut v___x_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_116_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_117_ = 1;
    v___x_118_ = crate::leanh::lean_box((v___x_117_) as usize);
    v___x_119_ = lean_st_ref_set(v___x_116_, v___x_118_);
    v___x_120_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_120_, 0, v___x_119_);
    return v___x_120_;
}
pub unsafe fn l_Lean_enableInitializersExecution___boxed(
    mut v_a_121_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_122_ = lean_enable_initializer_execution();
    return v_res_122_;
}
pub unsafe fn l_Lean_isInitializerExecutionEnabled() -> *mut crate::leanh::LeanObject {
    let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_124_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_125_ = lean_st_ref_get(v___x_124_);
    v___x_126_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_126_, 0, v___x_125_);
    return v___x_126_;
}
pub unsafe fn l_Lean_isInitializerExecutionEnabled___boxed(
    mut v_a_127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_128_ = l_Lean_isInitializerExecutionEnabled();
    return v_res_128_;
}
pub unsafe fn l_Lean_initializing() -> *mut crate::leanh::LeanObject {
    let mut v___x_130_: u8 = 0;
    v___x_130_ = lean_io_initializing();
    if v___x_130_ == 0 {
        let mut v___x_131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_131_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
        v___x_132_ = lean_st_ref_get(v___x_131_);
        v___x_133_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_133_, 0, v___x_132_);
        return v___x_133_;
    } else {
        let mut v___x_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_134_ = crate::leanh::lean_box((v___x_130_) as usize);
        v___x_135_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_135_, 0, v___x_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Lean_initializing___boxed(
    mut v_a_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_137_ = l_Lean_initializing();
    return v_res_137_;
}
pub unsafe fn l_Lean_withImporting___redArg___lam__0(
    mut v___x_138_: *mut crate::leanh::LeanObject,
    mut v___x_139_: u8,
    mut v_x_140_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_142_ = crate::leanh::lean_box((v___x_139_) as usize);
    v___x_143_ = lean_st_ref_set(v___x_138_, v___x_142_);
    v___x_144_ = l___private_Lean_ImportingFlag_0__Lean_runInitializersRef;
    v___x_145_ = crate::leanh::lean_box((v___x_139_) as usize);
    v___x_146_ = lean_st_ref_set(v___x_144_, v___x_145_);
    v___x_147_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_147_, 0, v___x_146_);
    return v___x_147_;
}
pub unsafe fn l_Lean_withImporting___redArg___lam__0___boxed(
    mut v___x_148_: *mut crate::leanh::LeanObject,
    mut v___x_149_: *mut crate::leanh::LeanObject,
    mut v_x_150_: *mut crate::leanh::LeanObject,
    mut v___y_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_331__boxed_152_: u8 = 0;
    let mut v_res_153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_331__boxed_152_ = (crate::leanh::lean_unbox(v___x_149_) as u8);
    v_res_153_ =
        l_Lean_withImporting___redArg___lam__0(v___x_148_, v___x_331__boxed_152_, v_x_150_);
    crate::leanh::lean_dec(v_x_150_);
    crate::leanh::lean_dec(v___x_148_);
    return v_res_153_;
}
pub unsafe fn l_Lean_withImporting___redArg(
    mut v_x_154_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_157_: u8 = 0;
    let mut v___x_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_160_: u8 = 0;
    let mut v_r_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_165_: u8 = 0;
    let mut v___x_167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_171_: u8 = 0;
    let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_175_: u8 = 0;
    let mut v_unused_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_178_: u8 = 0;
    let mut v_a_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_184_: u8 = 0;
    let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_188_: u8 = 0;
    let mut v_unused_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_156_ = l___private_Lean_ImportingFlag_0__Lean_importingRef;
                v___x_157_ = 1;
                v___x_158_ = crate::leanh::lean_box((v___x_157_) as usize);
                v___x_159_ = lean_st_ref_set(v___x_156_, v___x_158_);
                v___x_160_ = 0;
                v_r_161_ = crate::leanh::lean_apply_1(v_x_154_, crate::leanh::lean_box(0));
                if crate::leanh::lean_obj_tag(v_r_161_) == 0 {
                    v_a_162_ = crate::leanh::lean_ctor_get(v_r_161_, 0);
                    v_isSharedCheck_178_ = (!crate::leanh::lean_is_exclusive(v_r_161_)) as u8;
                    if v_isSharedCheck_178_ == 0 {
                        v___x_164_ = v_r_161_;
                        v_isShared_165_ = v_isSharedCheck_178_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_162_);
                        crate::leanh::lean_dec(v_r_161_);
                        v___x_164_ = crate::leanh::lean_box(0);
                        v_isShared_165_ = v_isSharedCheck_178_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_179_ = crate::leanh::lean_ctor_get(v_r_161_, 0);
                    crate::leanh::lean_inc(v_a_179_);
                    crate::leanh::lean_dec_ref_known(v_r_161_, 1);
                    v___x_180_ = crate::leanh::lean_box(0);
                    v___x_181_ =
                        l_Lean_withImporting___redArg___lam__0(v___x_156_, v___x_160_, v___x_180_);
                    v_isSharedCheck_188_ = (!crate::leanh::lean_is_exclusive(v___x_181_)) as u8;
                    if v_isSharedCheck_188_ == 0 {
                        v_unused_189_ = crate::leanh::lean_ctor_get(v___x_181_, 0);
                        crate::leanh::lean_dec(v_unused_189_);
                        v___x_183_ = v___x_181_;
                        v_isShared_184_ = v_isSharedCheck_188_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_181_);
                        v___x_183_ = crate::leanh::lean_box(0);
                        v_isShared_184_ = v_isSharedCheck_188_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_162_);
                if v_isShared_165_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_164_, 1);
                    v___x_167_ = v___x_164_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_177_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_177_, 0, v_a_162_);
                    v___x_167_ = v_reuseFailAlloc_177_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_168_ =
                    l_Lean_withImporting___redArg___lam__0(v___x_156_, v___x_160_, v___x_167_);
                crate::leanh::lean_dec_ref(v___x_167_);
                v_isSharedCheck_175_ = (!crate::leanh::lean_is_exclusive(v___x_168_)) as u8;
                if v_isSharedCheck_175_ == 0 {
                    v_unused_176_ = crate::leanh::lean_ctor_get(v___x_168_, 0);
                    crate::leanh::lean_dec(v_unused_176_);
                    v___x_170_ = v___x_168_;
                    v_isShared_171_ = v_isSharedCheck_175_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_168_);
                    v___x_170_ = crate::leanh::lean_box(0);
                    v_isShared_171_ = v_isSharedCheck_175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_171_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_170_, 0, v_a_162_);
                    v___x_173_ = v___x_170_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_174_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_174_, 0, v_a_162_);
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
                    crate::leanh::lean_ctor_set_tag(v___x_183_, 1);
                    crate::leanh::lean_ctor_set(v___x_183_, 0, v_a_179_);
                    v___x_186_ = v___x_183_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_179_);
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
    mut v_x_190_: *mut crate::leanh::LeanObject,
    mut v_a_191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_192_ = l_Lean_withImporting___redArg(v_x_190_);
    return v_res_192_;
}
pub unsafe fn l_Lean_withImporting(
    mut v_00_u03b1_193_: *mut crate::leanh::LeanObject,
    mut v_x_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_196_ = l_Lean_withImporting___redArg(v_x_194_);
    return v___x_196_;
}
pub unsafe fn l_Lean_withImporting___boxed(
    mut v_00_u03b1_197_: *mut crate::leanh::LeanObject,
    mut v_x_198_: *mut crate::leanh::LeanObject,
    mut v_a_199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_200_ = l_Lean_withImporting(v_00_u03b1_197_, v_x_198_);
    return v_res_200_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_ImportingFlag(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_1124607303____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ImportingFlag_0__Lean_importingRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_importingRef);
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_ImportingFlag_0__Lean_initFn_00___x40_Lean_ImportingFlag_2251799370____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    l___private_Lean_ImportingFlag_0__Lean_runInitializersRef =
        crate::leanh::lean_io_result_get_value(res);
    crate::leanh::lean_mark_persistent(l___private_Lean_ImportingFlag_0__Lean_runInitializersRef);
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_ImportingFlag(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_ImportingFlag(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ImportingFlag(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_ImportingFlag(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_ImportingFlag(builtin);
}

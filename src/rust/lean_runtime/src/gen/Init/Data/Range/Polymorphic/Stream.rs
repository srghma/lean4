// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Stream
// Imports: Init.Data.Range.Polymorphic.Iterators Init.Data.Stream
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Data::Stream::{
    initialize_Init_Data_Stream, runtime_initialize_Init_Data_Stream,
};
pub static l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___lam__0
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___lam__0(
    mut v_r_137_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_142_: u8 = 0;
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_147_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_138_ = crate::leanh::lean_ctor_get(v_r_137_, 0);
                v_upper_139_ = crate::leanh::lean_ctor_get(v_r_137_, 1);
                v_isSharedCheck_147_ = (!crate::leanh::lean_is_exclusive(v_r_137_)) as u8;
                if v_isSharedCheck_147_ == 0 {
                    v___x_141_ = v_r_137_;
                    v_isShared_142_ = v_isSharedCheck_147_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_139_);
                    crate::leanh::lean_inc(v_lower_138_);
                    crate::leanh::lean_dec(v_r_137_);
                    v___x_141_ = crate::leanh::lean_box(0);
                    v_isShared_142_ = v_isSharedCheck_147_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_143_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_143_, 0, v_lower_138_);
                if v_isShared_142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_141_, 0, v___x_143_);
                    v___x_145_ = v___x_141_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_146_, 0, v___x_143_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_146_, 1, v_upper_139_);
                    v___x_145_ = v_reuseFailAlloc_146_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_145_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable(
    mut v_00_u03b1_149_: *mut crate::leanh::LeanObject,
    mut v_inst_150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_151_ = l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___closed__0;
    return v___f_151_;
}
pub unsafe fn l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable___boxed(
    mut v_00_u03b1_152_: *mut crate::leanh::LeanObject,
    mut v_inst_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_154_ =
        l_Std_PRange_instToStreamRccIterIteratorOfUpwardEnumerable(v_00_u03b1_152_, v_inst_153_);
    crate::leanh::lean_dec_ref(v_inst_153_);
    return v_res_154_;
}
pub unsafe fn l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___lam__0(
    mut v_r_155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_160_: u8 = 0;
    let mut v___x_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_156_ = crate::leanh::lean_ctor_get(v_r_155_, 0);
                v_upper_157_ = crate::leanh::lean_ctor_get(v_r_155_, 1);
                v_isSharedCheck_165_ = (!crate::leanh::lean_is_exclusive(v_r_155_)) as u8;
                if v_isSharedCheck_165_ == 0 {
                    v___x_159_ = v_r_155_;
                    v_isShared_160_ = v_isSharedCheck_165_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_157_);
                    crate::leanh::lean_inc(v_lower_156_);
                    crate::leanh::lean_dec(v_r_155_);
                    v___x_159_ = crate::leanh::lean_box(0);
                    v_isShared_160_ = v_isSharedCheck_165_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_161_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_161_, 0, v_lower_156_);
                if v_isShared_160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_159_, 0, v___x_161_);
                    v___x_163_ = v___x_159_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_164_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_164_, 0, v___x_161_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_164_, 1, v_upper_157_);
                    v___x_163_ = v_reuseFailAlloc_164_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable(
    mut v_00_u03b1_167_: *mut crate::leanh::LeanObject,
    mut v_inst_168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_169_ = l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___closed__0;
    return v___f_169_;
}
pub unsafe fn l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable___boxed(
    mut v_00_u03b1_170_: *mut crate::leanh::LeanObject,
    mut v_inst_171_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_172_ =
        l_Std_PRange_instToStreamRcoIterIteratorOfUpwardEnumerable(v_00_u03b1_170_, v_inst_171_);
    crate::leanh::lean_dec_ref(v_inst_171_);
    return v_res_172_;
}
pub unsafe fn l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___lam__0(
    mut v_r_173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_174_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_174_, 0, v_r_173_);
    return v___x_174_;
}
pub unsafe fn l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable(
    mut v_00_u03b1_176_: *mut crate::leanh::LeanObject,
    mut v_inst_177_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_178_ = l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___closed__0;
    return v___f_178_;
}
pub unsafe fn l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable___boxed(
    mut v_00_u03b1_179_: *mut crate::leanh::LeanObject,
    mut v_inst_180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ =
        l_Std_PRange_instToStreamRciIterIteratorOfUpwardEnumerable(v_00_u03b1_179_, v_inst_180_);
    crate::leanh::lean_dec_ref(v_inst_180_);
    return v_res_181_;
}
pub unsafe fn l_Std_PRange_instToStreamRocIterIteratorOfUpwardEnumerable___redArg___lam__0(
    mut v_inst_182_: *mut crate::leanh::LeanObject,
    mut v_r_183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_189_: u8 = 0;
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_184_ = crate::leanh::lean_ctor_get(v_inst_182_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_184_);
                crate::leanh::lean_dec_ref(v_inst_182_);
                v_lower_185_ = crate::leanh::lean_ctor_get(v_r_183_, 0);
                v_upper_186_ = crate::leanh::lean_ctor_get(v_r_183_, 1);
                v_isSharedCheck_194_ = (!crate::leanh::lean_is_exclusive(v_r_183_)) as u8;
                if v_isSharedCheck_194_ == 0 {
                    v___x_188_ = v_r_183_;
                    v_isShared_189_ = v_isSharedCheck_194_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_186_);
                    crate::leanh::lean_inc(v_lower_185_);
                    crate::leanh::lean_dec(v_r_183_);
                    v___x_188_ = crate::leanh::lean_box(0);
                    v_isShared_189_ = v_isSharedCheck_194_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_190_ = crate::leanh::lean_apply_1(v_succ_x3f_184_, v_lower_185_);
                if v_isShared_189_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_188_, 0, v___x_190_);
                    v___x_192_ = v___x_188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_193_, 0, v___x_190_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_193_, 1, v_upper_186_);
                    v___x_192_ = v_reuseFailAlloc_193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_PRange_instToStreamRocIterIteratorOfUpwardEnumerable___redArg(
    mut v_inst_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_196_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRocIterIteratorOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_196_, 0, v_inst_195_);
    return v___f_196_;
}
pub unsafe fn l_Std_PRange_instToStreamRocIterIteratorOfUpwardEnumerable(
    mut v_00_u03b1_197_: *mut crate::leanh::LeanObject,
    mut v_inst_198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_199_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRocIterIteratorOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_199_, 0, v_inst_198_);
    return v___f_199_;
}
pub unsafe fn l_Std_PRange_instToStreamRooIterIteratorOfUpwardEnumerable___redArg___lam__0(
    mut v_inst_200_: *mut crate::leanh::LeanObject,
    mut v_r_201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_207_: u8 = 0;
    let mut v___x_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_212_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_succ_x3f_202_ = crate::leanh::lean_ctor_get(v_inst_200_, 0);
                crate::leanh::lean_inc_ref(v_succ_x3f_202_);
                crate::leanh::lean_dec_ref(v_inst_200_);
                v_lower_203_ = crate::leanh::lean_ctor_get(v_r_201_, 0);
                v_upper_204_ = crate::leanh::lean_ctor_get(v_r_201_, 1);
                v_isSharedCheck_212_ = (!crate::leanh::lean_is_exclusive(v_r_201_)) as u8;
                if v_isSharedCheck_212_ == 0 {
                    v___x_206_ = v_r_201_;
                    v_isShared_207_ = v_isSharedCheck_212_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_upper_204_);
                    crate::leanh::lean_inc(v_lower_203_);
                    crate::leanh::lean_dec(v_r_201_);
                    v___x_206_ = crate::leanh::lean_box(0);
                    v_isShared_207_ = v_isSharedCheck_212_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_208_ = crate::leanh::lean_apply_1(v_succ_x3f_202_, v_lower_203_);
                if v_isShared_207_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_206_, 0, v___x_208_);
                    v___x_210_ = v___x_206_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_211_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_208_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_211_, 1, v_upper_204_);
                    v___x_210_ = v_reuseFailAlloc_211_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_210_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_PRange_instToStreamRooIterIteratorOfUpwardEnumerable___redArg(
    mut v_inst_213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_214_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRooIterIteratorOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_214_, 0, v_inst_213_);
    return v___f_214_;
}
pub unsafe fn l_Std_PRange_instToStreamRooIterIteratorOfUpwardEnumerable(
    mut v_00_u03b1_215_: *mut crate::leanh::LeanObject,
    mut v_inst_216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_217_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRooIterIteratorOfUpwardEnumerable___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_217_, 0, v_inst_216_);
    return v___f_217_;
}
pub unsafe fn l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0(
    mut v_inst_218_: *mut crate::leanh::LeanObject,
    mut v_r_219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_succ_x3f_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_succ_x3f_220_ = crate::leanh::lean_ctor_get(v_inst_218_, 0);
    crate::leanh::lean_inc_ref(v_succ_x3f_220_);
    crate::leanh::lean_dec_ref(v_inst_218_);
    v___x_221_ = crate::leanh::lean_apply_1(v_succ_x3f_220_, v_r_219_);
    return v___x_221_;
}
pub unsafe fn l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg(
    mut v_inst_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_223_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_223_, 0, v_inst_222_);
    return v___f_223_;
}
pub unsafe fn l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f(
    mut v_00_u03b1_224_: *mut crate::leanh::LeanObject,
    mut v_inst_225_: *mut crate::leanh::LeanObject,
    mut v_inst_226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_227_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_227_, 0, v_inst_225_);
    return v___f_227_;
}
pub unsafe fn l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f___boxed(
    mut v_00_u03b1_228_: *mut crate::leanh::LeanObject,
    mut v_inst_229_: *mut crate::leanh::LeanObject,
    mut v_inst_230_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_231_ = l_Std_PRange_instToStreamRoiIterIteratorOfUpwardEnumerableOfLeast_x3f(
        v_00_u03b1_228_,
        v_inst_229_,
        v_inst_230_,
    );
    crate::leanh::lean_dec(v_inst_230_);
    return v_res_231_;
}
pub unsafe fn l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0(
    mut v_inst_232_: *mut crate::leanh::LeanObject,
    mut v_r_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_234_, 0, v_inst_232_);
    crate::leanh::lean_ctor_set(v___x_234_, 1, v_r_233_);
    return v___x_234_;
}
pub unsafe fn l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg(
    mut v_inst_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_236_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_236_, 0, v_inst_235_);
    return v___f_236_;
}
pub unsafe fn l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f(
    mut v_00_u03b1_237_: *mut crate::leanh::LeanObject,
    mut v_inst_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_240_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_240_, 0, v_inst_239_);
    return v___f_240_;
}
pub unsafe fn l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f___boxed(
    mut v_00_u03b1_241_: *mut crate::leanh::LeanObject,
    mut v_inst_242_: *mut crate::leanh::LeanObject,
    mut v_inst_243_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_244_ = l_Std_PRange_instToStreamRicIterIteratorOfUpwardEnumerableOfLeast_x3f(
        v_00_u03b1_241_,
        v_inst_242_,
        v_inst_243_,
    );
    crate::leanh::lean_dec_ref(v_inst_242_);
    return v_res_244_;
}
pub unsafe fn l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0(
    mut v_inst_245_: *mut crate::leanh::LeanObject,
    mut v_r_246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_247_, 0, v_inst_245_);
    crate::leanh::lean_ctor_set(v___x_247_, 1, v_r_246_);
    return v___x_247_;
}
pub unsafe fn l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg(
    mut v_inst_248_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_249_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_249_, 0, v_inst_248_);
    return v___f_249_;
}
pub unsafe fn l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f(
    mut v_00_u03b1_250_: *mut crate::leanh::LeanObject,
    mut v_inst_251_: *mut crate::leanh::LeanObject,
    mut v_inst_252_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_253_ = crate::leanh::lean_alloc_closure(
        l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_253_, 0, v_inst_252_);
    return v___f_253_;
}
pub unsafe fn l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f___boxed(
    mut v_00_u03b1_254_: *mut crate::leanh::LeanObject,
    mut v_inst_255_: *mut crate::leanh::LeanObject,
    mut v_inst_256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_257_ = l_Std_PRange_instToStreamRioIterIteratorOfUpwardEnumerableOfLeast_x3f(
        v_00_u03b1_254_,
        v_inst_255_,
        v_inst_256_,
    );
    crate::leanh::lean_dec_ref(v_inst_255_);
    return v_res_257_;
}
pub unsafe fn l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0(
    mut v_inst_258_: *mut crate::leanh::LeanObject,
    mut v_r_259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_inst_258_);
    return v_inst_258_;
}
pub unsafe fn l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0___boxed(
    mut v_inst_260_: *mut crate::leanh::LeanObject,
    mut v_r_261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_262_ =
        l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0(
            v_inst_260_,
            v_r_261_,
        );
    crate::leanh::lean_dec(v_inst_260_);
    return v_res_262_;
}
pub unsafe fn l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg(
    mut v_inst_263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_264_ = crate::leanh::lean_alloc_closure(l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_264_, 0, v_inst_263_);
    return v___f_264_;
}
pub unsafe fn l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f(
    mut v_00_u03b1_265_: *mut crate::leanh::LeanObject,
    mut v_inst_266_: *mut crate::leanh::LeanObject,
    mut v_inst_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_268_ = crate::leanh::lean_alloc_closure(l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___redArg___lam__0___boxed as *mut core::ffi::c_void, 2, 1);
    crate::leanh::lean_closure_set(v___f_268_, 0, v_inst_267_);
    return v___f_268_;
}
pub unsafe fn l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f___boxed(
    mut v_00_u03b1_269_: *mut crate::leanh::LeanObject,
    mut v_inst_270_: *mut crate::leanh::LeanObject,
    mut v_inst_271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_272_ = l_Std_PRange_instToStreamRiiIterIteratorOfUpwardEnumerableOfLeast_x3f(
        v_00_u03b1_269_,
        v_inst_270_,
        v_inst_271_,
    );
    crate::leanh::lean_dec_ref(v_inst_270_);
    return v_res_272_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Stream(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Stream(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Stream(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Stream(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Stream(builtin);
}

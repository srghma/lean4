// Lean compiler output
// Module: Lake.Util.Lock
// Imports: Init.System.IO Init.Data.ToString.Macro
use crate::ffi::{
    lean_get_stderr, lean_io_prim_handle_mk, lean_io_process_get_pid, lean_string_append,
    lean_uint32_to_nat,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Basic::l_instToStringString___lam__0___boxed;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_parent;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_IO_FS_Handle_putStrLn, l_IO_FS_Stream_putStrLn,
    l_IO_FS_createDirAll, l_IO_FS_removeFile___boxed, l_IO_eprintln___redArg, l_IO_sleep,
    l_instMonadExceptOfEIO___aux__3___boxed, runtime_initialize_Init_System_IO,
};
pub static l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value:
    crate::leanh::LeanStringObject<74> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 74,
    m_capacity: 74,
    m_length: 73,
    m_data: [
        119, 97, 114, 110, 105, 110, 103, 58, 32, 119, 97, 105, 116, 105, 110, 103, 32, 102, 111,
        114, 32, 112, 114, 105, 111, 114, 32, 96, 108, 97, 107, 101, 32, 98, 117, 105, 108, 100,
        96, 32, 105, 110, 118, 111, 99, 97, 116, 105, 111, 110, 32, 116, 111, 32, 102, 105, 110,
        105, 115, 104, 46, 46, 46, 32, 40, 114, 101, 109, 111, 118, 101, 32, 39, 0,
    ],
};
static mut l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value:
    crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [39, 32, 105, 102, 32, 115, 116, 117, 99, 107, 41, 0],
};
static mut l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lake_withLockFile___redArg___lam__2___closed__0_value: crate::leanh::LeanStringObject<
    11,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [119, 97, 114, 110, 105, 110, 103, 58, 32, 96, 0],
};
static mut l_Lake_withLockFile___redArg___lam__2___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLockFile___redArg___lam__2___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLockFile___redArg___lam__2___closed__1_value: crate::leanh::LeanStringObject<
    43,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 43,
    m_capacity: 43,
    m_length: 42,
    m_data: [
        96, 32, 119, 97, 115, 32, 100, 101, 108, 101, 116, 101, 100, 32, 98, 101, 102, 111, 114,
        101, 32, 116, 104, 101, 32, 108, 111, 99, 107, 32, 119, 97, 115, 32, 114, 101, 108, 101,
        97, 115, 101, 100, 0,
    ],
};
static mut l_Lake_withLockFile___redArg___lam__2___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLockFile___redArg___lam__2___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLockFile___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_withLockFile___redArg___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_withLockFile___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLockFile___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lake_withLockFile___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_instToStringString___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_withLockFile___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_withLockFile___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(
    mut v_lockFile_142_: *mut crate::leanh::LeanObject,
    mut v_____r_143_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_145_: u8 = 0;
    let mut v___x_146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_148_: u32 = 0;
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_155_: u8 = 0;
    let mut v___x_157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_159_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_145_ = 2;
                v___x_146_ = lean_io_prim_handle_mk(v_lockFile_142_, v___x_145_);
                if crate::leanh::lean_obj_tag(v___x_146_) == 0 {
                    v_a_147_ = crate::leanh::lean_ctor_get(v___x_146_, 0);
                    crate::leanh::lean_inc(v_a_147_);
                    crate::leanh::lean_dec_ref_known(v___x_146_, 1);
                    v___x_148_ = lean_io_process_get_pid();
                    v___x_149_ = lean_uint32_to_nat(v___x_148_);
                    v___x_150_ = l_Nat_reprFast(v___x_149_);
                    v___x_151_ = l_IO_FS_Handle_putStrLn(v_a_147_, v___x_150_);
                    crate::leanh::lean_dec(v_a_147_);
                    return v___x_151_;
                } else {
                    v_a_152_ = crate::leanh::lean_ctor_get(v___x_146_, 0);
                    v_isSharedCheck_159_ = (!crate::leanh::lean_is_exclusive(v___x_146_)) as u8;
                    if v_isSharedCheck_159_ == 0 {
                        v___x_154_ = v___x_146_;
                        v_isShared_155_ = v_isSharedCheck_159_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_152_);
                        crate::leanh::lean_dec(v___x_146_);
                        v___x_154_ = crate::leanh::lean_box(0);
                        v_isShared_155_ = v_isSharedCheck_159_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_155_ == 0 {
                    v___x_157_ = v___x_154_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_158_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_158_, 0, v_a_152_);
                    v___x_157_ = v_reuseFailAlloc_158_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_157_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0___boxed(
    mut v_lockFile_160_: *mut crate::leanh::LeanObject,
    mut v_____r_161_: *mut crate::leanh::LeanObject,
    mut v___y_162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_163_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(
        v_lockFile_160_,
        v_____r_161_,
    );
    crate::leanh::lean_dec_ref(v_lockFile_160_);
    return v_res_163_;
}
pub unsafe fn l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(
    mut v_lockFile_166_: *mut crate::leanh::LeanObject,
    mut v_firstTime_167_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_170_: u32 = 0;
    let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: u8 = 0;
    let mut v___y_175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_flush_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_lockFile_166_);
                v___x_185_ = l_System_FilePath_parent(v_lockFile_166_);
                if crate::leanh::lean_obj_tag(v___x_185_) == 1 {
                    v_val_186_ = crate::leanh::lean_ctor_get(v___x_185_, 0);
                    crate::leanh::lean_inc(v_val_186_);
                    crate::leanh::lean_dec_ref_known(v___x_185_, 1);
                    v___x_187_ = l_IO_FS_createDirAll(v_val_186_);
                    if crate::leanh::lean_obj_tag(v___x_187_) == 0 {
                        v_a_188_ = crate::leanh::lean_ctor_get(v___x_187_, 0);
                        crate::leanh::lean_inc(v_a_188_);
                        crate::leanh::lean_dec_ref_known(v___x_187_, 1);
                        v___x_189_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(v_lockFile_166_, v_a_188_);
                        v___y_175_ = v___x_189_;
                        state = 2;
                        continue;
                    } else {
                        v___y_175_ = v___x_187_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_185_);
                    v___x_190_ = crate::leanh::lean_box(0);
                    v___x_191_ =
                        l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___lam__0(
                            v_lockFile_166_,
                            v___x_190_,
                        );
                    v___y_175_ = v___x_191_;
                    state = 2;
                    continue;
                }
            }
            1 => {
                v___x_170_ = 300;
                v___x_171_ = l_IO_sleep(v___x_170_);
                v___x_172_ = 0;
                v_firstTime_167_ = v___x_172_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_175_) == 0 {
                    crate::leanh::lean_dec_ref(v_lockFile_166_);
                    return v___y_175_;
                } else {
                    v_a_176_ = crate::leanh::lean_ctor_get(v___y_175_, 0);
                    if crate::leanh::lean_obj_tag(v_a_176_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___y_175_, 1);
                        if v_firstTime_167_ == 0 {
                            state = 1;
                            continue;
                        } else {
                            v___x_177_ = lean_get_stderr();
                            v___x_178_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__0;
                            v___x_179_ = lean_string_append(v___x_178_, v_lockFile_166_);
                            v___x_180_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___closed__1;
                            v___x_181_ = lean_string_append(v___x_179_, v___x_180_);
                            crate::leanh::lean_inc_ref(v___x_177_);
                            v___x_182_ = l_IO_FS_Stream_putStrLn(v___x_177_, v___x_181_);
                            if crate::leanh::lean_obj_tag(v___x_182_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_182_, 1);
                                v_flush_183_ = crate::leanh::lean_ctor_get(v___x_177_, 0);
                                crate::leanh::lean_inc_ref(v_flush_183_);
                                crate::leanh::lean_dec_ref(v___x_177_);
                                v___x_184_ = crate::leanh::lean_apply_1(
                                    v_flush_183_,
                                    crate::leanh::lean_box(0),
                                );
                                if crate::leanh::lean_obj_tag(v___x_184_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_184_, 1);
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_lockFile_166_);
                                    return v___x_184_;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_177_);
                                crate::leanh::lean_dec_ref(v_lockFile_166_);
                                return v___x_182_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_lockFile_166_);
                        return v___y_175_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop___boxed(
    mut v_lockFile_192_: *mut crate::leanh::LeanObject,
    mut v_firstTime_193_: *mut crate::leanh::LeanObject,
    mut v_a_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_firstTime_boxed_195_: u8 = 0;
    let mut v_res_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_firstTime_boxed_195_ = (crate::leanh::lean_unbox(v_firstTime_193_) as u8);
    v_res_196_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(
        v_lockFile_192_,
        v_firstTime_boxed_195_,
    );
    return v_res_196_;
}
pub unsafe fn l_Lake_busyAcquireLockFile(
    mut v_lockFile_197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_199_: u8 = 0;
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_199_ = 1;
    v___x_200_ = l___private_Lake_Util_Lock_0__Lake_busyAcquireLockFile_busyLoop(
        v_lockFile_197_,
        v___x_199_,
    );
    return v___x_200_;
}
pub unsafe fn l_Lake_busyAcquireLockFile___boxed(
    mut v_lockFile_201_: *mut crate::leanh::LeanObject,
    mut v_a_202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_203_ = l_Lake_busyAcquireLockFile(v_lockFile_201_);
    return v_res_203_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__0(
    mut v_act_204_: *mut crate::leanh::LeanObject,
    mut v_____r_205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_act_204_);
    return v_act_204_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__0___boxed(
    mut v_act_206_: *mut crate::leanh::LeanObject,
    mut v_____r_207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_208_ = l_Lake_withLockFile___redArg___lam__0(v_act_206_, v_____r_207_);
    crate::leanh::lean_dec(v_act_206_);
    return v_res_208_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__1(
    mut v_x_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fst_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fst_210_ = crate::leanh::lean_ctor_get(v_x_209_, 0);
    crate::leanh::lean_inc(v_fst_210_);
    return v_fst_210_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__1___boxed(
    mut v_x_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_212_ = l_Lake_withLockFile___redArg___lam__1(v_x_211_);
    crate::leanh::lean_dec_ref(v_x_211_);
    return v_res_212_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__2(
    mut v_lockFile_215_: *mut crate::leanh::LeanObject,
    mut v___f_216_: *mut crate::leanh::LeanObject,
    mut v_x_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_217_) == 11 {
        let mut v___x_219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v_x_217_, 2);
        v___x_219_ = l_Lake_withLockFile___redArg___lam__2___closed__0;
        v___x_220_ = lean_string_append(v___x_219_, v_lockFile_215_);
        v___x_221_ = l_Lake_withLockFile___redArg___lam__2___closed__1;
        v___x_222_ = lean_string_append(v___x_220_, v___x_221_);
        v___x_223_ = l_IO_eprintln___redArg(v___f_216_, v___x_222_);
        return v___x_223_;
    } else {
        let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___f_216_);
        v___x_224_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_224_, 0, v_x_217_);
        return v___x_224_;
    }
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__2___boxed(
    mut v_lockFile_225_: *mut crate::leanh::LeanObject,
    mut v___f_226_: *mut crate::leanh::LeanObject,
    mut v_x_227_: *mut crate::leanh::LeanObject,
    mut v___y_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_229_ = l_Lake_withLockFile___redArg___lam__2(v_lockFile_225_, v___f_226_, v_x_227_);
    crate::leanh::lean_dec_ref(v_lockFile_225_);
    return v_res_229_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__3(
    mut v___x_230_: *mut crate::leanh::LeanObject,
    mut v_x_231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v___x_230_);
    return v___x_230_;
}
pub unsafe fn l_Lake_withLockFile___redArg___lam__3___boxed(
    mut v___x_232_: *mut crate::leanh::LeanObject,
    mut v_x_233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_234_ = l_Lake_withLockFile___redArg___lam__3(v___x_232_, v_x_233_);
    crate::leanh::lean_dec(v_x_233_);
    crate::leanh::lean_dec(v___x_232_);
    return v_res_234_;
}
pub unsafe fn l_Lake_withLockFile___redArg(
    mut v_inst_237_: *mut crate::leanh::LeanObject,
    mut v_inst_238_: *mut crate::leanh::LeanObject,
    mut v_inst_239_: *mut crate::leanh::LeanObject,
    mut v_lockFile_240_: *mut crate::leanh::LeanObject,
    mut v_act_241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_242_ = crate::leanh::lean_ctor_get(v_inst_237_, 0);
    v_toFunctor_243_ = crate::leanh::lean_ctor_get(v_toApplicative_242_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_243_);
    v_toBind_244_ = crate::leanh::lean_ctor_get(v_inst_237_, 1);
    crate::leanh::lean_inc(v_toBind_244_);
    crate::leanh::lean_dec_ref(v_inst_237_);
    v_map_245_ = crate::leanh::lean_ctor_get(v_toFunctor_243_, 0);
    crate::leanh::lean_inc(v_map_245_);
    crate::leanh::lean_dec_ref(v_toFunctor_243_);
    crate::leanh::lean_inc_ref_n(v_lockFile_240_, 2);
    v___x_246_ = crate::leanh::lean_alloc_closure(
        l_Lake_busyAcquireLockFile___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_246_, 0, v_lockFile_240_);
    crate::leanh::lean_inc(v_inst_239_);
    v___x_247_ = crate::leanh::lean_apply_2(v_inst_239_, crate::leanh::lean_box(0), v___x_246_);
    v___f_248_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_248_, 0, v_act_241_);
    v___f_249_ = l_Lake_withLockFile___redArg___closed__0;
    v___f_250_ = l_Lake_withLockFile___redArg___closed__1;
    v___f_251_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_251_, 0, v_lockFile_240_);
    crate::leanh::lean_closure_set(v___f_251_, 1, v___f_250_);
    v___x_252_ = crate::leanh::lean_apply_4(
        v_toBind_244_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_247_,
        v___f_248_,
    );
    v___x_253_ = crate::leanh::lean_alloc_closure(
        l_IO_FS_removeFile___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_253_, 0, v_lockFile_240_);
    v_this_254_ = crate::leanh::lean_alloc_closure(
        l_instMonadExceptOfEIO___aux__3___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v_this_254_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_this_254_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_this_254_, 2, v___x_253_);
    crate::leanh::lean_closure_set(v_this_254_, 3, v___f_251_);
    v___x_255_ = crate::leanh::lean_apply_2(v_inst_239_, crate::leanh::lean_box(0), v_this_254_);
    v___f_256_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_256_, 0, v___x_255_);
    v_y_257_ = crate::leanh::lean_apply_4(
        v_inst_238_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_252_,
        v___f_256_,
    );
    v___x_258_ = crate::leanh::lean_apply_4(
        v_map_245_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_249_,
        v_y_257_,
    );
    return v___x_258_;
}
pub unsafe fn l_Lake_withLockFile(
    mut v_m_259_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_260_: *mut crate::leanh::LeanObject,
    mut v_inst_261_: *mut crate::leanh::LeanObject,
    mut v_inst_262_: *mut crate::leanh::LeanObject,
    mut v_inst_263_: *mut crate::leanh::LeanObject,
    mut v_lockFile_264_: *mut crate::leanh::LeanObject,
    mut v_act_265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toFunctor_267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_this_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_y_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_266_ = crate::leanh::lean_ctor_get(v_inst_261_, 0);
    v_toFunctor_267_ = crate::leanh::lean_ctor_get(v_toApplicative_266_, 0);
    crate::leanh::lean_inc_ref(v_toFunctor_267_);
    v_toBind_268_ = crate::leanh::lean_ctor_get(v_inst_261_, 1);
    crate::leanh::lean_inc(v_toBind_268_);
    crate::leanh::lean_dec_ref(v_inst_261_);
    v_map_269_ = crate::leanh::lean_ctor_get(v_toFunctor_267_, 0);
    crate::leanh::lean_inc(v_map_269_);
    crate::leanh::lean_dec_ref(v_toFunctor_267_);
    crate::leanh::lean_inc_ref_n(v_lockFile_264_, 2);
    v___x_270_ = crate::leanh::lean_alloc_closure(
        l_Lake_busyAcquireLockFile___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_270_, 0, v_lockFile_264_);
    crate::leanh::lean_inc(v_inst_263_);
    v___x_271_ = crate::leanh::lean_apply_2(v_inst_263_, crate::leanh::lean_box(0), v___x_270_);
    v___f_272_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_272_, 0, v_act_265_);
    v___f_273_ = l_Lake_withLockFile___redArg___closed__0;
    v___f_274_ = l_Lake_withLockFile___redArg___closed__1;
    v___f_275_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__2___boxed as *mut core::ffi::c_void,
        4,
        2,
    );
    crate::leanh::lean_closure_set(v___f_275_, 0, v_lockFile_264_);
    crate::leanh::lean_closure_set(v___f_275_, 1, v___f_274_);
    v___x_276_ = crate::leanh::lean_apply_4(
        v_toBind_268_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_271_,
        v___f_272_,
    );
    v___x_277_ = crate::leanh::lean_alloc_closure(
        l_IO_FS_removeFile___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_277_, 0, v_lockFile_264_);
    v_this_278_ = crate::leanh::lean_alloc_closure(
        l_instMonadExceptOfEIO___aux__3___boxed as *mut core::ffi::c_void,
        5,
        4,
    );
    crate::leanh::lean_closure_set(v_this_278_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_this_278_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v_this_278_, 2, v___x_277_);
    crate::leanh::lean_closure_set(v_this_278_, 3, v___f_275_);
    v___x_279_ = crate::leanh::lean_apply_2(v_inst_263_, crate::leanh::lean_box(0), v_this_278_);
    v___f_280_ = crate::leanh::lean_alloc_closure(
        l_Lake_withLockFile___redArg___lam__3___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_280_, 0, v___x_279_);
    v_y_281_ = crate::leanh::lean_apply_4(
        v_inst_262_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___x_276_,
        v___f_280_,
    );
    v___x_282_ = crate::leanh::lean_apply_4(
        v_map_269_,
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
        v___f_273_,
        v_y_281_,
    );
    return v___x_282_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Lock(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Lock(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Lock(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Lock(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Lock(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Lock(builtin);
}

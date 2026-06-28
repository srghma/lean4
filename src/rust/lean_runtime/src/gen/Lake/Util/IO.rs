// Lean compiler output
// Module: Lake.Util.IO
// Imports: Init.System.IO
use crate::r#gen::Init::System::FilePath::{l_System_FilePath_normalize, l_System_FilePath_parent};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, l_IO_FS_DirEntry_path, l_IO_FS_createDirAll,
    l_IO_FS_instBEqFileType_beq, l_IO_FS_readBinFile, l_IO_FS_writeBinFile,
    l_System_FilePath_pathExists, runtime_initialize_Init_System_IO,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{lean_usize_add, lean_usize_dec_lt};
use crate::lean_imports_rs::Init::Prelude::{lean_nat_dec_eq, lean_string_utf8_byte_size};
use crate::lean_imports_rs::Init::System::IO::{
    lean_io_prim_handle_mk, lean_io_prim_handle_put_str, lean_io_prim_handle_write,
    lean_io_read_dir, lean_io_realpath, lean_io_remove_dir, lean_io_remove_file,
    lean_io_symlink_metadata,
};
pub static l_Lake_resolvePath___closed__0_value: crate::leanh::LeanStringObject<1> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 1,
        m_capacity: 1,
        m_length: 0,
        m_data: [0],
    };
static mut l_Lake_resolvePath___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_resolvePath___closed__0_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lake_createParentDirs(
    mut v_path_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_187_ = l_System_FilePath_parent(v_path_185_);
    if crate::leanh::lean_obj_tag(v___x_187_) == 1 {
        let mut v_val_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_val_188_ = crate::leanh::lean_ctor_get(v___x_187_, 0);
        crate::leanh::lean_inc(v_val_188_);
        crate::leanh::lean_dec_ref_known(v___x_187_, 1);
        v___x_189_ = l_IO_FS_createDirAll(v_val_188_);
        return v___x_189_;
    } else {
        let mut v___x_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_187_);
        v___x_190_ = crate::leanh::lean_box(0);
        v___x_191_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_191_, 0, v___x_190_);
        return v___x_191_;
    }
}
pub unsafe fn l_Lake_createParentDirs___boxed(
    mut v_path_192_: *mut crate::leanh::LeanObject,
    mut v_a_193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_194_ = l_Lake_createParentDirs(v_path_192_);
    return v_res_194_;
}
pub unsafe fn l_Lake_removeFileIfExists(
    mut v_path_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_201_: u8 = 0;
    let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_206_: u8 = 0;
    let mut v_unused_207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_197_ = lean_io_remove_file(v_path_195_);
                if crate::leanh::lean_obj_tag(v___x_197_) == 0 {
                    return v___x_197_;
                } else {
                    v_a_198_ = crate::leanh::lean_ctor_get(v___x_197_, 0);
                    crate::leanh::lean_inc(v_a_198_);
                    if crate::leanh::lean_obj_tag(v_a_198_) == 11 {
                        crate::leanh::lean_dec_ref_known(v_a_198_, 2);
                        v_isSharedCheck_206_ = (!crate::leanh::lean_is_exclusive(v___x_197_)) as u8;
                        if v_isSharedCheck_206_ == 0 {
                            v_unused_207_ = crate::leanh::lean_ctor_get(v___x_197_, 0);
                            crate::leanh::lean_dec(v_unused_207_);
                            v___x_200_ = v___x_197_;
                            v_isShared_201_ = v_isSharedCheck_206_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_197_);
                            v___x_200_ = crate::leanh::lean_box(0);
                            v_isShared_201_ = v_isSharedCheck_206_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_198_);
                        return v___x_197_;
                    }
                }
            }
            1 => {
                v___x_202_ = crate::leanh::lean_box(0);
                if v_isShared_201_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_200_, 0);
                    crate::leanh::lean_ctor_set(v___x_200_, 0, v___x_202_);
                    v___x_204_ = v___x_200_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_205_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
                    v___x_204_ = v_reuseFailAlloc_205_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_204_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_removeFileIfExists___boxed(
    mut v_path_208_: *mut crate::leanh::LeanObject,
    mut v_a_209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_210_ = l_Lake_removeFileIfExists(v_path_208_);
    crate::leanh::lean_dec_ref(v_path_208_);
    return v_res_210_;
}
pub unsafe fn l_Lake_writeFileIfNew(
    mut v_path_211_: *mut crate::leanh::LeanObject,
    mut v_content_212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_214_: u8 = 0;
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_221_: u8 = 0;
    let mut v___x_222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_229_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_214_ = 2;
                v___x_215_ = lean_io_prim_handle_mk(v_path_211_, v___x_214_);
                if crate::leanh::lean_obj_tag(v___x_215_) == 0 {
                    v_a_216_ = crate::leanh::lean_ctor_get(v___x_215_, 0);
                    crate::leanh::lean_inc(v_a_216_);
                    crate::leanh::lean_dec_ref_known(v___x_215_, 1);
                    v___x_217_ = lean_io_prim_handle_put_str(v_a_216_, v_content_212_);
                    crate::leanh::lean_dec(v_a_216_);
                    return v___x_217_;
                } else {
                    v_a_218_ = crate::leanh::lean_ctor_get(v___x_215_, 0);
                    v_isSharedCheck_229_ = (!crate::leanh::lean_is_exclusive(v___x_215_)) as u8;
                    if v_isSharedCheck_229_ == 0 {
                        v___x_220_ = v___x_215_;
                        v_isShared_221_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_218_);
                        crate::leanh::lean_dec(v___x_215_);
                        v___x_220_ = crate::leanh::lean_box(0);
                        v_isShared_221_ = v_isSharedCheck_229_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_218_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_218_, 2);
                    v___x_222_ = crate::leanh::lean_box(0);
                    if v_isShared_221_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_220_, 0);
                        crate::leanh::lean_ctor_set(v___x_220_, 0, v___x_222_);
                        v___x_224_ = v___x_220_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_225_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_225_, 0, v___x_222_);
                        v___x_224_ = v_reuseFailAlloc_225_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_221_ == 0 {
                        v___x_227_ = v___x_220_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_228_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_228_, 0, v_a_218_);
                        v___x_227_ = v_reuseFailAlloc_228_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_224_;
            }
            3 => {
                return v___x_227_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_writeFileIfNew___boxed(
    mut v_path_230_: *mut crate::leanh::LeanObject,
    mut v_content_231_: *mut crate::leanh::LeanObject,
    mut v_a_232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_233_ = l_Lake_writeFileIfNew(v_path_230_, v_content_231_);
    crate::leanh::lean_dec_ref(v_content_231_);
    crate::leanh::lean_dec_ref(v_path_230_);
    return v_res_233_;
}
pub unsafe fn l_Lake_writeBinFileIfNew(
    mut v_path_234_: *mut crate::leanh::LeanObject,
    mut v_content_235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_237_: u8 = 0;
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_244_: u8 = 0;
    let mut v___x_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_252_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_237_ = 2;
                v___x_238_ = lean_io_prim_handle_mk(v_path_234_, v___x_237_);
                if crate::leanh::lean_obj_tag(v___x_238_) == 0 {
                    v_a_239_ = crate::leanh::lean_ctor_get(v___x_238_, 0);
                    crate::leanh::lean_inc(v_a_239_);
                    crate::leanh::lean_dec_ref_known(v___x_238_, 1);
                    v___x_240_ = lean_io_prim_handle_write(v_a_239_, v_content_235_);
                    crate::leanh::lean_dec(v_a_239_);
                    return v___x_240_;
                } else {
                    v_a_241_ = crate::leanh::lean_ctor_get(v___x_238_, 0);
                    v_isSharedCheck_252_ = (!crate::leanh::lean_is_exclusive(v___x_238_)) as u8;
                    if v_isSharedCheck_252_ == 0 {
                        v___x_243_ = v___x_238_;
                        v_isShared_244_ = v_isSharedCheck_252_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_241_);
                        crate::leanh::lean_dec(v___x_238_);
                        v___x_243_ = crate::leanh::lean_box(0);
                        v_isShared_244_ = v_isSharedCheck_252_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_241_) == 0 {
                    crate::leanh::lean_dec_ref_known(v_a_241_, 2);
                    v___x_245_ = crate::leanh::lean_box(0);
                    if v_isShared_244_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_243_, 0);
                        crate::leanh::lean_ctor_set(v___x_243_, 0, v___x_245_);
                        v___x_247_ = v___x_243_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_245_);
                        v___x_247_ = v_reuseFailAlloc_248_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_244_ == 0 {
                        v___x_250_ = v___x_243_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_251_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_241_);
                        v___x_250_ = v_reuseFailAlloc_251_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_247_;
            }
            3 => {
                return v___x_250_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_writeBinFileIfNew___boxed(
    mut v_path_253_: *mut crate::leanh::LeanObject,
    mut v_content_254_: *mut crate::leanh::LeanObject,
    mut v_a_255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_256_ = l_Lake_writeBinFileIfNew(v_path_253_, v_content_254_);
    crate::leanh::lean_dec_ref(v_content_254_);
    crate::leanh::lean_dec_ref(v_path_253_);
    return v_res_256_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(
    mut v_as_257_: *mut crate::leanh::LeanObject,
    mut v_sz_258_: usize,
    mut v_i_259_: usize,
    mut v_b_260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_264_: usize = 0;
    let mut v___x_265_: usize = 0;
    let mut v___x_267_: u8 = 0;
    let mut v___x_268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_274_: u8 = 0;
    let mut v___x_275_: u8 = 0;
    let mut v___x_276_: u8 = 0;
    let mut v___x_277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_282_: u8 = 0;
    let mut v___x_284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_286_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_267_ = lean_usize_dec_lt(v_i_259_, v_sz_258_);
                if v___x_267_ == 0 {
                    v___x_268_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_268_, 0, v_b_260_);
                    return v___x_268_;
                } else {
                    v___x_269_ = crate::leanh::lean_box(0);
                    v_a_270_ = lean_array_uget_borrowed(v_as_257_, v_i_259_);
                    crate::leanh::lean_inc(v_a_270_);
                    v___x_271_ = l_IO_FS_DirEntry_path(v_a_270_);
                    v___x_272_ = lean_io_symlink_metadata(v___x_271_);
                    if crate::leanh::lean_obj_tag(v___x_272_) == 0 {
                        v_a_273_ = crate::leanh::lean_ctor_get(v___x_272_, 0);
                        crate::leanh::lean_inc(v_a_273_);
                        crate::leanh::lean_dec_ref_known(v___x_272_, 1);
                        v_type_274_ = crate::leanh::lean_ctor_get_uint8(
                            v_a_273_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2 + 16) as u32,
                        );
                        crate::leanh::lean_dec(v_a_273_);
                        v___x_275_ = 0;
                        v___x_276_ = l_IO_FS_instBEqFileType_beq(v_type_274_, v___x_275_);
                        if v___x_276_ == 0 {
                            v___x_277_ = l_Lake_removeFileIfExists(v___x_271_);
                            crate::leanh::lean_dec_ref(v___x_271_);
                            if crate::leanh::lean_obj_tag(v___x_277_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_277_, 1);
                                v_a_263_ = v___x_269_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_277_;
                            }
                        } else {
                            v___x_278_ = l_Lake_removeDirAllIfExists(v___x_271_);
                            crate::leanh::lean_dec_ref(v___x_271_);
                            if crate::leanh::lean_obj_tag(v___x_278_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_278_, 1);
                                v_a_263_ = v___x_269_;
                                state = 1;
                                continue;
                            } else {
                                return v___x_278_;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_271_);
                        v_a_279_ = crate::leanh::lean_ctor_get(v___x_272_, 0);
                        v_isSharedCheck_286_ = (!crate::leanh::lean_is_exclusive(v___x_272_)) as u8;
                        if v_isSharedCheck_286_ == 0 {
                            v___x_281_ = v___x_272_;
                            v_isShared_282_ = v_isSharedCheck_286_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_279_);
                            crate::leanh::lean_dec(v___x_272_);
                            v___x_281_ = crate::leanh::lean_box(0);
                            v_isShared_282_ = v_isSharedCheck_286_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_264_ = 1usize;
                v___x_265_ = lean_usize_add(v_i_259_, v___x_264_);
                v_i_259_ = v___x_265_;
                v_b_260_ = v_a_263_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_279_) == 11 {
                    crate::leanh::lean_dec_ref_known(v_a_279_, 2);
                    crate::leanh::lean_del_object(v___x_281_);
                    v_a_263_ = v___x_269_;
                    state = 1;
                    continue;
                } else {
                    if v_isShared_282_ == 0 {
                        v___x_284_ = v___x_281_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_285_, 0, v_a_279_);
                        v___x_284_ = v_reuseFailAlloc_285_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_284_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_removeDirAllIfExists(
    mut v_path_287_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_292_: usize = 0;
    let mut v___x_293_: usize = 0;
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_299_: u8 = 0;
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_303_: u8 = 0;
    let mut v_unused_304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_308_: u8 = 0;
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_316_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_289_ = lean_io_read_dir(v_path_287_);
                if crate::leanh::lean_obj_tag(v___x_289_) == 0 {
                    v_a_290_ = crate::leanh::lean_ctor_get(v___x_289_, 0);
                    crate::leanh::lean_inc(v_a_290_);
                    crate::leanh::lean_dec_ref_known(v___x_289_, 1);
                    v___x_291_ = crate::leanh::lean_box(0);
                    v_sz_292_ = lean_array_size(v_a_290_);
                    v___x_293_ = 0usize;
                    v___x_294_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_a_290_, v_sz_292_, v___x_293_, v___x_291_);
                    crate::leanh::lean_dec(v_a_290_);
                    if crate::leanh::lean_obj_tag(v___x_294_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_294_, 1);
                        v___x_295_ = lean_io_remove_dir(v_path_287_);
                        if crate::leanh::lean_obj_tag(v___x_295_) == 0 {
                            return v___x_295_;
                        } else {
                            v_a_296_ = crate::leanh::lean_ctor_get(v___x_295_, 0);
                            crate::leanh::lean_inc(v_a_296_);
                            if crate::leanh::lean_obj_tag(v_a_296_) == 11 {
                                crate::leanh::lean_dec_ref_known(v_a_296_, 2);
                                v_isSharedCheck_303_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_295_)) as u8;
                                if v_isSharedCheck_303_ == 0 {
                                    v_unused_304_ = crate::leanh::lean_ctor_get(v___x_295_, 0);
                                    crate::leanh::lean_dec(v_unused_304_);
                                    v___x_298_ = v___x_295_;
                                    v_isShared_299_ = v_isSharedCheck_303_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_295_);
                                    v___x_298_ = crate::leanh::lean_box(0);
                                    v_isShared_299_ = v_isSharedCheck_303_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_296_);
                                return v___x_295_;
                            }
                        }
                    } else {
                        return v___x_294_;
                    }
                } else {
                    v_a_305_ = crate::leanh::lean_ctor_get(v___x_289_, 0);
                    v_isSharedCheck_316_ = (!crate::leanh::lean_is_exclusive(v___x_289_)) as u8;
                    if v_isSharedCheck_316_ == 0 {
                        v___x_307_ = v___x_289_;
                        v_isShared_308_ = v_isSharedCheck_316_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_305_);
                        crate::leanh::lean_dec(v___x_289_);
                        v___x_307_ = crate::leanh::lean_box(0);
                        v_isShared_308_ = v_isSharedCheck_316_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_299_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_298_, 0);
                    crate::leanh::lean_ctor_set(v___x_298_, 0, v___x_291_);
                    v___x_301_ = v___x_298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_302_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_291_);
                    v___x_301_ = v_reuseFailAlloc_302_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_301_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_305_) == 11 {
                    crate::leanh::lean_dec_ref_known(v_a_305_, 2);
                    v___x_309_ = crate::leanh::lean_box(0);
                    if v_isShared_308_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_307_, 0);
                        crate::leanh::lean_ctor_set(v___x_307_, 0, v___x_309_);
                        v___x_311_ = v___x_307_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_312_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_312_, 0, v___x_309_);
                        v___x_311_ = v_reuseFailAlloc_312_;
                        state = 4;
                        continue;
                    }
                } else {
                    if v_isShared_308_ == 0 {
                        v___x_314_ = v___x_307_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_315_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_305_);
                        v___x_314_ = v_reuseFailAlloc_315_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_311_;
            }
            5 => {
                return v___x_314_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_removeDirAllIfExists___boxed(
    mut v_path_317_: *mut crate::leanh::LeanObject,
    mut v_a_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_319_ = l_Lake_removeDirAllIfExists(v_path_317_);
    crate::leanh::lean_dec_ref(v_path_317_);
    return v_res_319_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0___boxed(
    mut v_as_320_: *mut crate::leanh::LeanObject,
    mut v_sz_321_: *mut crate::leanh::LeanObject,
    mut v_i_322_: *mut crate::leanh::LeanObject,
    mut v_b_323_: *mut crate::leanh::LeanObject,
    mut v___y_324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_325_: usize = 0;
    let mut v_i_boxed_326_: usize = 0;
    let mut v_res_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_325_ = crate::leanh::lean_unbox_usize(v_sz_321_);
    crate::leanh::lean_dec(v_sz_321_);
    v_i_boxed_326_ = crate::leanh::lean_unbox_usize(v_i_322_);
    crate::leanh::lean_dec(v_i_322_);
    v_res_327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lake_removeDirAllIfExists_spec__0(v_as_320_, v_sz_boxed_325_, v_i_boxed_326_, v_b_323_);
    crate::leanh::lean_dec_ref(v_as_320_);
    return v_res_327_;
}
pub unsafe fn l_Lake_copyFile(
    mut v_src_328_: *mut crate::leanh::LeanObject,
    mut v_dst_329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_337_: u8 = 0;
    let mut v___x_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_341_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_331_ = l_IO_FS_readBinFile(v_src_328_);
                if crate::leanh::lean_obj_tag(v___x_331_) == 0 {
                    v_a_332_ = crate::leanh::lean_ctor_get(v___x_331_, 0);
                    crate::leanh::lean_inc(v_a_332_);
                    crate::leanh::lean_dec_ref_known(v___x_331_, 1);
                    v___x_333_ = l_IO_FS_writeBinFile(v_dst_329_, v_a_332_);
                    crate::leanh::lean_dec(v_a_332_);
                    return v___x_333_;
                } else {
                    v_a_334_ = crate::leanh::lean_ctor_get(v___x_331_, 0);
                    v_isSharedCheck_341_ = (!crate::leanh::lean_is_exclusive(v___x_331_)) as u8;
                    if v_isSharedCheck_341_ == 0 {
                        v___x_336_ = v___x_331_;
                        v_isShared_337_ = v_isSharedCheck_341_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_334_);
                        crate::leanh::lean_dec(v___x_331_);
                        v___x_336_ = crate::leanh::lean_box(0);
                        v_isShared_337_ = v_isSharedCheck_341_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_337_ == 0 {
                    v___x_339_ = v___x_336_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_340_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_340_, 0, v_a_334_);
                    v___x_339_ = v_reuseFailAlloc_340_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_339_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_copyFile___boxed(
    mut v_src_342_: *mut crate::leanh::LeanObject,
    mut v_dst_343_: *mut crate::leanh::LeanObject,
    mut v_a_344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_345_ = l_Lake_copyFile(v_src_342_, v_dst_343_);
    crate::leanh::lean_dec_ref(v_dst_343_);
    crate::leanh::lean_dec_ref(v_src_342_);
    return v_res_345_;
}
pub unsafe fn l_Lake_resolvePath(
    mut v_path_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_349_ = lean_io_realpath(v_path_347_);
    if crate::leanh::lean_obj_tag(v___x_349_) == 0 {
        let mut v_a_350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_351_: u8 = 0;
        v_a_350_ = crate::leanh::lean_ctor_get(v___x_349_, 0);
        crate::leanh::lean_inc(v_a_350_);
        crate::leanh::lean_dec_ref_known(v___x_349_, 1);
        v___x_351_ = l_System_FilePath_pathExists(v_a_350_);
        if v___x_351_ == 0 {
            let mut v___x_352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_a_350_);
            v___x_352_ = l_Lake_resolvePath___closed__0;
            return v___x_352_;
        } else {
            let mut v___x_353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_353_ = l_System_FilePath_normalize(v_a_350_);
            return v___x_353_;
        }
    } else {
        let mut v___x_354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_349_, 1);
        v___x_354_ = l_Lake_resolvePath___closed__0;
        return v___x_354_;
    }
}
pub unsafe fn l_Lake_resolvePath___boxed(
    mut v_path_355_: *mut crate::leanh::LeanObject,
    mut v_a_356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_357_ = l_Lake_resolvePath(v_path_355_);
    return v_res_357_;
}
pub unsafe fn l_Lake_resolvePath_x3f(
    mut v_path_358_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: u8 = 0;
    v___x_360_ = l_Lake_resolvePath(v_path_358_);
    v___x_361_ = lean_string_utf8_byte_size(v___x_360_);
    v___x_362_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_363_ = lean_nat_dec_eq(v___x_361_, v___x_362_);
    if v___x_363_ == 0 {
        let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_364_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_364_, 0, v___x_360_);
        return v___x_364_;
    } else {
        let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_360_);
        v___x_365_ = crate::leanh::lean_box(0);
        return v___x_365_;
    }
}
pub unsafe fn l_Lake_resolvePath_x3f___boxed(
    mut v_path_366_: *mut crate::leanh::LeanObject,
    mut v_a_367_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_368_ = l_Lake_resolvePath_x3f(v_path_366_);
    return v_res_368_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_IO(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_IO(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_IO(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_IO(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lake_Util_IO(builtin);
}

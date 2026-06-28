// Lean compiler output
// Module: Lean.Data.Json.Stream
// Imports: Lean.Data.Json.Parser Lean.Data.Json.Printer
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Lean::Data::Json::Parser::{
    initialize_Lean_Data_Json_Parser, l_Lean_Json_parse, runtime_initialize_Lean_Data_Json_Parser,
};
use crate::r#gen::Lean::Data::Json::Printer::{
    initialize_Lean_Data_Json_Printer, l_Lean_Json_compress,
    runtime_initialize_Lean_Data_Json_Printer,
};
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_validate_utf8;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_usize_of_nat;
use crate::lean_imports_rs::Init::Prelude::lean_string_from_utf8_unchecked;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_box_usize, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
};
pub static l_IO_FS_Stream_readUTF8___closed__0_value: LeanStringObject<14> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [105, 110, 118, 97, 108, 105, 100, 32, 85, 84, 70, 45, 56, 0],
};
static mut l_IO_FS_Stream_readUTF8___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_IO_FS_Stream_readUTF8___closed__0_value) as *mut LeanObject;
static mut l_IO_FS_Stream_readUTF8___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_IO_FS_Stream_readUTF8___closed__1: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_IO_FS_Stream_readUTF8___closed__1() -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    v___x_112_ = l_IO_FS_Stream_readUTF8___closed__0;
    v___x_113_ = lean_mk_io_user_error(v___x_112_);
    return v___x_113_;
}
pub unsafe fn l_IO_FS_Stream_readUTF8(
    mut v_h_114_: *mut LeanObject,
    mut v_nBytes_115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_read_117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_118_: usize = 0;
    let mut v___x_119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_120_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_124_: u8 = 0;
    let mut v___x_125_: u8 = 0;
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_134_: u8 = 0;
    let mut v_a_135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_138_: u8 = 0;
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_read_117_ = lean_ctor_get(v_h_114_, 1);
                lean_inc_ref(v_read_117_);
                lean_dec_ref(v_h_114_);
                v___x_118_ = lean_usize_of_nat(v_nBytes_115_);
                v___x_119_ = lean_box_usize(v___x_118_);
                v___x_120_ = lean_apply_2(v_read_117_, v___x_119_, lean_box(0));
                if lean_obj_tag(v___x_120_) == 0 {
                    v_a_121_ = lean_ctor_get(v___x_120_, 0);
                    v_isSharedCheck_134_ = (!lean_is_exclusive(v___x_120_)) as u8;
                    if v_isSharedCheck_134_ == 0 {
                        v___x_123_ = v___x_120_;
                        v_isShared_124_ = v_isSharedCheck_134_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_121_);
                        lean_dec(v___x_120_);
                        v___x_123_ = lean_box(0);
                        v_isShared_124_ = v_isSharedCheck_134_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_135_ = lean_ctor_get(v___x_120_, 0);
                    v_isSharedCheck_142_ = (!lean_is_exclusive(v___x_120_)) as u8;
                    if v_isSharedCheck_142_ == 0 {
                        v___x_137_ = v___x_120_;
                        v_isShared_138_ = v_isSharedCheck_142_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_135_);
                        lean_dec(v___x_120_);
                        v___x_137_ = lean_box(0);
                        v_isShared_138_ = v_isSharedCheck_142_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_125_ = lean_string_validate_utf8(v_a_121_);
                if v___x_125_ == 0 {
                    lean_dec(v_a_121_);
                    v___x_126_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_IO_FS_Stream_readUTF8___closed__1),
                        core::ptr::addr_of_mut!(l_IO_FS_Stream_readUTF8___closed__1_once),
                        _init_l_IO_FS_Stream_readUTF8___closed__1,
                    );
                    if v_isShared_124_ == 0 {
                        lean_ctor_set_tag(v___x_123_, 1);
                        lean_ctor_set(v___x_123_, 0, v___x_126_);
                        v___x_128_ = v___x_123_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_129_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_129_, 0, v___x_126_);
                        v___x_128_ = v_reuseFailAlloc_129_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_130_ = lean_string_from_utf8_unchecked(v_a_121_);
                    if v_isShared_124_ == 0 {
                        lean_ctor_set(v___x_123_, 0, v___x_130_);
                        v___x_132_ = v___x_123_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_133_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_133_, 0, v___x_130_);
                        v___x_132_ = v_reuseFailAlloc_133_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_128_;
            }
            3 => {
                return v___x_132_;
            }
            4 => {
                if v_isShared_138_ == 0 {
                    v___x_140_ = v___x_137_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_141_, 0, v_a_135_);
                    v___x_140_ = v_reuseFailAlloc_141_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_140_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readUTF8___boxed(
    mut v_h_143_: *mut LeanObject,
    mut v_nBytes_144_: *mut LeanObject,
    mut v_a_145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_146_: *mut LeanObject = core::ptr::null_mut();
    v_res_146_ = l_IO_FS_Stream_readUTF8(v_h_143_, v_nBytes_144_);
    lean_dec(v_nBytes_144_);
    return v_res_146_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(
    mut v_e_147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_152_: u8 = 0;
    let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_157_: u8 = 0;
    let mut v_a_158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_161_: u8 = 0;
    let mut v___x_163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_e_147_) == 0 {
                    v_a_149_ = lean_ctor_get(v_e_147_, 0);
                    v_isSharedCheck_157_ = (!lean_is_exclusive(v_e_147_)) as u8;
                    if v_isSharedCheck_157_ == 0 {
                        v___x_151_ = v_e_147_;
                        v_isShared_152_ = v_isSharedCheck_157_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_149_);
                        lean_dec(v_e_147_);
                        v___x_151_ = lean_box(0);
                        v_isShared_152_ = v_isSharedCheck_157_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_158_ = lean_ctor_get(v_e_147_, 0);
                    v_isSharedCheck_165_ = (!lean_is_exclusive(v_e_147_)) as u8;
                    if v_isSharedCheck_165_ == 0 {
                        v___x_160_ = v_e_147_;
                        v_isShared_161_ = v_isSharedCheck_165_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_158_);
                        lean_dec(v_e_147_);
                        v___x_160_ = lean_box(0);
                        v_isShared_161_ = v_isSharedCheck_165_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_153_ = lean_mk_io_user_error(v_a_149_);
                if v_isShared_152_ == 0 {
                    lean_ctor_set_tag(v___x_151_, 1);
                    lean_ctor_set(v___x_151_, 0, v___x_153_);
                    v___x_155_ = v___x_151_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_153_);
                    v___x_155_ = v_reuseFailAlloc_156_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_155_;
            }
            3 => {
                if v_isShared_161_ == 0 {
                    lean_ctor_set_tag(v___x_160_, 0);
                    v___x_163_ = v___x_160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_164_, 0, v_a_158_);
                    v___x_163_ = v_reuseFailAlloc_164_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg___boxed(
    mut v_e_166_: *mut LeanObject,
    mut v_a_167_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_168_: *mut LeanObject = core::ptr::null_mut();
    v_res_168_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v_e_166_);
    return v_res_168_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(
    mut v_00_u03b1_169_: *mut LeanObject,
    mut v_e_170_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
    v___x_172_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v_e_170_);
    return v___x_172_;
}
pub unsafe fn l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___boxed(
    mut v_00_u03b1_173_: *mut LeanObject,
    mut v_e_174_: *mut LeanObject,
    mut v_a_175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_176_: *mut LeanObject = core::ptr::null_mut();
    v_res_176_ = l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0(v_00_u03b1_173_, v_e_174_);
    return v_res_176_;
}
pub unsafe fn l_IO_FS_Stream_readJson(
    mut v_h_177_: *mut LeanObject,
    mut v_nBytes_178_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_read_180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_181_: usize = 0;
    let mut v___x_182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_187_: u8 = 0;
    let mut v___x_188_: u8 = 0;
    let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_193_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_196_: u8 = 0;
    let mut v_a_197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_200_: u8 = 0;
    let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_204_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_read_180_ = lean_ctor_get(v_h_177_, 1);
                lean_inc_ref(v_read_180_);
                lean_dec_ref(v_h_177_);
                v___x_181_ = lean_usize_of_nat(v_nBytes_178_);
                v___x_182_ = lean_box_usize(v___x_181_);
                v___x_183_ = lean_apply_2(v_read_180_, v___x_182_, lean_box(0));
                if lean_obj_tag(v___x_183_) == 0 {
                    v_a_184_ = lean_ctor_get(v___x_183_, 0);
                    v_isSharedCheck_196_ = (!lean_is_exclusive(v___x_183_)) as u8;
                    if v_isSharedCheck_196_ == 0 {
                        v___x_186_ = v___x_183_;
                        v_isShared_187_ = v_isSharedCheck_196_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_184_);
                        lean_dec(v___x_183_);
                        v___x_186_ = lean_box(0);
                        v_isShared_187_ = v_isSharedCheck_196_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_197_ = lean_ctor_get(v___x_183_, 0);
                    v_isSharedCheck_204_ = (!lean_is_exclusive(v___x_183_)) as u8;
                    if v_isSharedCheck_204_ == 0 {
                        v___x_199_ = v___x_183_;
                        v_isShared_200_ = v_isSharedCheck_204_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_197_);
                        lean_dec(v___x_183_);
                        v___x_199_ = lean_box(0);
                        v_isShared_200_ = v_isSharedCheck_204_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_188_ = lean_string_validate_utf8(v_a_184_);
                if v___x_188_ == 0 {
                    lean_dec(v_a_184_);
                    v___x_189_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_IO_FS_Stream_readUTF8___closed__1),
                        core::ptr::addr_of_mut!(l_IO_FS_Stream_readUTF8___closed__1_once),
                        _init_l_IO_FS_Stream_readUTF8___closed__1,
                    );
                    if v_isShared_187_ == 0 {
                        lean_ctor_set_tag(v___x_186_, 1);
                        lean_ctor_set(v___x_186_, 0, v___x_189_);
                        v___x_191_ = v___x_186_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_189_);
                        v___x_191_ = v_reuseFailAlloc_192_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_186_);
                    v___x_193_ = lean_string_from_utf8_unchecked(v_a_184_);
                    v___x_194_ = l_Lean_Json_parse(v___x_193_);
                    v___x_195_ =
                        l_IO_ofExcept___at___00IO_FS_Stream_readJson_spec__0___redArg(v___x_194_);
                    return v___x_195_;
                }
            }
            2 => {
                return v___x_191_;
            }
            3 => {
                if v_isShared_200_ == 0 {
                    v___x_202_ = v___x_199_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_203_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_203_, 0, v_a_197_);
                    v___x_202_ = v_reuseFailAlloc_203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_202_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_FS_Stream_readJson___boxed(
    mut v_h_205_: *mut LeanObject,
    mut v_nBytes_206_: *mut LeanObject,
    mut v_a_207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_208_: *mut LeanObject = core::ptr::null_mut();
    v_res_208_ = l_IO_FS_Stream_readJson(v_h_205_, v_nBytes_206_);
    lean_dec(v_nBytes_206_);
    return v_res_208_;
}
pub unsafe fn l_IO_FS_Stream_writeJson(
    mut v_h_209_: *mut LeanObject,
    mut v_j_210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_flush_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_putStr_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v_flush_212_ = lean_ctor_get(v_h_209_, 0);
    lean_inc_ref(v_flush_212_);
    v_putStr_213_ = lean_ctor_get(v_h_209_, 4);
    lean_inc_ref(v_putStr_213_);
    lean_dec_ref(v_h_209_);
    v___x_214_ = l_Lean_Json_compress(v_j_210_);
    v___x_215_ = lean_apply_2(v_putStr_213_, v___x_214_, lean_box(0));
    if lean_obj_tag(v___x_215_) == 0 {
        let mut v___x_216_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_215_, 1);
        v___x_216_ = lean_apply_1(v_flush_212_, lean_box(0));
        return v___x_216_;
    } else {
        lean_dec_ref(v_flush_212_);
        return v___x_215_;
    }
}
pub unsafe fn l_IO_FS_Stream_writeJson___boxed(
    mut v_h_217_: *mut LeanObject,
    mut v_j_218_: *mut LeanObject,
    mut v_a_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_220_: *mut LeanObject = core::ptr::null_mut();
    v_res_220_ = l_IO_FS_Stream_writeJson(v_h_217_, v_j_218_);
    return v_res_220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Json_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Json_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Data_Json_Stream(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json_Parser(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_Json_Printer(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Json_Stream(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Json_Stream(builtin);
}

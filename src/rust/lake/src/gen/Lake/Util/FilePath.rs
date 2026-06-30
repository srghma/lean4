// Lean compiler output
// Module: Lake.Util.FilePath
// Imports: Lean.Data.Json Init.Data.String.TakeDrop Init.Data.String.Modify Init.System.Platform
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_sub, lean_string_dec_eq,
    lean_string_memcmp, lean_string_push, lean_string_utf8_byte_size, lean_string_utf8_extract,
    lean_string_utf8_get, lean_string_utf8_get_fast, lean_string_utf8_prev, lean_string_utf8_set,
    lean_uint32_dec_eq,
};
use crate::r#gen::Init::Data::String::Basic::{l_String_Slice_Pos_nextn, l_String_Slice_pos_x21};
use crate::r#gen::Init::Data::String::Modify::{
    initialize_Init_Data_String_Modify, runtime_initialize_Init_Data_String_Modify,
};
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Prelude::{l_Char_utf8Size, l_Lean_Name_str___override};
use crate::r#gen::Init::System::FilePath::{
    l_System_FilePath_components, l_System_FilePath_join, l_System_FilePath_normalize,
    l_System_FilePath_pathSeparator,
};
use crate::r#gen::Init::System::Platform::{
    initialize_Init_System_Platform, l_System_Platform_isWindows,
    runtime_initialize_Init_System_Platform,
};
use crate::r#gen::Lean::Data::Json::{
    initialize_Lean_Data_Json, runtime_initialize_Lean_Data_Json,
};
pub static l_Lake_instToJsonFilePath__lake___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_instToJsonFilePath__lake___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instToJsonFilePath__lake___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonFilePath__lake___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instToJsonFilePath__lake: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instToJsonFilePath__lake___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_joinRelative___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [46, 0],
    };
static mut l_Lake_joinRelative___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_joinRelative___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lake_instDivFilePath__lake___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lake_joinRelative as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_instDivFilePath__lake___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDivFilePath__lake___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instDivFilePath__lake: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDivFilePath__lake___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_instHDivFilePathString__lake: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_instDivFilePath__lake___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(
    mut v___x_166_: *mut leanh::LeanObject,
    mut v_s_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: u8 = 0;
    v___x_168_ = lean_string_utf8_byte_size(v_s_167_);
    v___x_169_ = lean_string_utf8_byte_size(v___x_166_);
    v___x_170_ = lean_nat_dec_le(v___x_169_, v___x_168_);
    if v___x_170_ == 0 {
        let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_s_167_);
        v___x_171_ = leanh::lean_box(0);
        return v___x_171_;
    } else {
        let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: u8 = 0;
        v___x_172_ = leanh::lean_unsigned_to_nat(0);
        v___x_173_ = lean_string_memcmp(v_s_167_, v___x_166_, v___x_172_, v___x_172_, v___x_169_);
        if v___x_173_ == 0 {
            let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v_s_167_);
            v___x_174_ = leanh::lean_box(0);
            return v___x_174_;
        } else {
            let mut v___x_175_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_inc_ref(v_s_167_);
            v___x_175_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_175_, 0, v_s_167_);
            leanh::lean_ctor_set(v___x_175_, 1, v___x_172_);
            leanh::lean_ctor_set(v___x_175_, 2, v___x_168_);
            v___x_176_ = l_String_Slice_pos_x21(v___x_175_, v___x_169_);
            leanh::lean_dec_ref_known(v___x_175_, 3);
            v___x_177_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
            leanh::lean_ctor_set(v___x_177_, 0, v_s_167_);
            leanh::lean_ctor_set(v___x_177_, 1, v___x_176_);
            leanh::lean_ctor_set(v___x_177_, 2, v___x_168_);
            v___x_178_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_178_, 0, v___x_177_);
            return v___x_178_;
        }
    }
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg___boxed(
    mut v___x_179_: *mut leanh::LeanObject,
    mut v_s_180_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_181_ =
        l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(v___x_179_, v_s_180_);
    leanh::lean_dec_ref(v___x_179_);
    return v_res_181_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(
    mut v___x_182_: *mut leanh::LeanObject,
    mut v_s_183_: *mut leanh::LeanObject,
    mut v_pat_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_185_ =
        l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(v___x_182_, v_s_183_);
    return v___x_185_;
}
pub unsafe fn l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___boxed(
    mut v___x_186_: *mut leanh::LeanObject,
    mut v_s_187_: *mut leanh::LeanObject,
    mut v_pat_188_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_189_ =
        l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0(v___x_186_, v_s_187_, v_pat_188_);
    leanh::lean_dec_ref(v_pat_188_);
    leanh::lean_dec_ref(v___x_186_);
    return v_res_189_;
}
pub unsafe fn l_Lake_relPathFrom(
    mut v_root_190_: *mut leanh::LeanObject,
    mut v_path_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_202_: u8 = 0;
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_208_: u8 = 0;
    let mut v_unused_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_path_191_);
                v___x_192_ = l_String_dropPrefix_x3f___at___00Lake_relPathFrom_spec__0___redArg(
                    v_root_190_,
                    v_path_191_,
                );
                if leanh::lean_obj_tag(v___x_192_) == 1 {
                    leanh::lean_dec_ref(v_path_191_);
                    v_val_193_ = leanh::lean_ctor_get(v___x_192_, 0);
                    leanh::lean_inc(v_val_193_);
                    leanh::lean_dec_ref_known(v___x_192_, 1);
                    v_str_194_ = leanh::lean_ctor_get(v_val_193_, 0);
                    leanh::lean_inc_ref(v_str_194_);
                    v_startInclusive_195_ = leanh::lean_ctor_get(v_val_193_, 1);
                    leanh::lean_inc(v_startInclusive_195_);
                    v_endExclusive_196_ = leanh::lean_ctor_get(v_val_193_, 2);
                    leanh::lean_inc(v_endExclusive_196_);
                    v___x_197_ = leanh::lean_unsigned_to_nat(1);
                    v___x_198_ = leanh::lean_unsigned_to_nat(0);
                    v___x_199_ = l_String_Slice_Pos_nextn(v_val_193_, v___x_198_, v___x_197_);
                    v_isSharedCheck_208_ = (!leanh::lean_is_exclusive(v_val_193_)) as u8;
                    if v_isSharedCheck_208_ == 0 {
                        v_unused_209_ = leanh::lean_ctor_get(v_val_193_, 2);
                        leanh::lean_dec(v_unused_209_);
                        v_unused_210_ = leanh::lean_ctor_get(v_val_193_, 1);
                        leanh::lean_dec(v_unused_210_);
                        v_unused_211_ = leanh::lean_ctor_get(v_val_193_, 0);
                        leanh::lean_dec(v_unused_211_);
                        v___x_201_ = v_val_193_;
                        v_isShared_202_ = v_isSharedCheck_208_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_val_193_);
                        v___x_201_ = leanh::lean_box(0);
                        v_isShared_202_ = v_isSharedCheck_208_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_192_);
                    return v_path_191_;
                }
            }
            1 => {
                v___x_203_ = lean_nat_add(v_startInclusive_195_, v___x_199_);
                leanh::lean_dec(v___x_199_);
                leanh::lean_dec(v_startInclusive_195_);
                if v_isShared_202_ == 0 {
                    leanh::lean_ctor_set(v___x_201_, 1, v___x_203_);
                    v___x_205_ = v___x_201_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_207_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_207_, 0, v_str_194_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_207_, 1, v___x_203_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_207_, 2, v_endExclusive_196_);
                    v___x_205_ = v_reuseFailAlloc_207_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_206_ = l_String_Slice_toString(v___x_205_);
                leanh::lean_dec_ref(v___x_205_);
                return v___x_206_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_relPathFrom___boxed(
    mut v_root_212_: *mut leanh::LeanObject,
    mut v_path_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_214_ = l_Lake_relPathFrom(v_root_212_, v_path_213_);
    leanh::lean_dec_ref(v_root_212_);
    return v_res_214_;
}
pub unsafe fn l_String_mapAux___at___00Lake_mkRelPathString_spec__0(
    mut v_s_215_: *mut leanh::LeanObject,
    mut v_p_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_218_: u32 = 0;
    let mut v___x_219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_224_: u8 = 0;
    let mut v___x_225_: u32 = 0;
    let mut v___x_226_: u32 = 0;
    let mut v___x_227_: u8 = 0;
    let mut v___x_228_: u32 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_223_ = lean_string_utf8_byte_size(v_s_215_);
                v___x_224_ = lean_nat_dec_eq(v_p_216_, v___x_223_);
                if v___x_224_ == 0 {
                    v___x_225_ = lean_string_utf8_get_fast(v_s_215_, v_p_216_);
                    v___x_226_ = 92;
                    v___x_227_ = lean_uint32_dec_eq(v___x_225_, v___x_226_);
                    if v___x_227_ == 0 {
                        v___y_218_ = v___x_225_;
                        state = 1;
                        continue;
                    } else {
                        v___x_228_ = 47;
                        v___y_218_ = v___x_228_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_p_216_);
                    return v_s_215_;
                }
            }
            1 => {
                leanh::lean_inc(v_p_216_);
                v___x_219_ = lean_string_utf8_set(v_s_215_, v_p_216_, v___y_218_);
                v___x_220_ = l_Char_utf8Size(v___y_218_);
                v___x_221_ = lean_nat_add(v_p_216_, v___x_220_);
                leanh::lean_dec(v___x_220_);
                leanh::lean_dec(v_p_216_);
                v_s_215_ = v___x_219_;
                v_p_216_ = v___x_221_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_mkRelPathString(
    mut v_path_229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_230_: u8 = 0;
    v___x_230_ = l_System_Platform_isWindows;
    if v___x_230_ == 0 {
        return v_path_229_;
    } else {
        let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_231_ = leanh::lean_unsigned_to_nat(0);
        v___x_232_ = l_String_mapAux___at___00Lake_mkRelPathString_spec__0(v_path_229_, v___x_231_);
        return v___x_232_;
    }
}
pub unsafe fn l_Lake_instToJsonFilePath__lake___lam__0(
    mut v_path_233_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_234_ = l_Lake_mkRelPathString(v_path_233_);
    v___x_235_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_235_, 0, v___x_234_);
    return v___x_235_;
}
pub unsafe fn l_Lake_joinRelative(
    mut v_a_239_: *mut leanh::LeanObject,
    mut v_b_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_242_: u8 = 0;
    v___x_241_ = l_Lake_joinRelative___closed__0;
    v___x_242_ = lean_string_dec_eq(v_b_240_, v___x_241_);
    if v___x_242_ == 0 {
        let mut v___x_243_: u8 = 0;
        v___x_243_ = lean_string_dec_eq(v_a_239_, v___x_241_);
        if v___x_243_ == 0 {
            let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_244_ = l_System_FilePath_join(v_a_239_, v_b_240_);
            return v___x_244_;
        } else {
            leanh::lean_dec_ref(v_a_239_);
            return v_b_240_;
        }
    } else {
        leanh::lean_dec_ref(v_b_240_);
        return v_a_239_;
    }
}
pub unsafe fn l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(
    mut v_s_248_: *mut leanh::LeanObject,
    mut v_i_249_: *mut leanh::LeanObject,
    mut v_e_250_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: u8 = 0;
    let mut v_i_x27_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_254_: u32 = 0;
    let mut v___x_255_: u32 = 0;
    let mut v___x_256_: u8 = 0;
    let mut v___x_257_: u32 = 0;
    let mut v___x_258_: u8 = 0;
    let mut v___x_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_251_ = leanh::lean_unsigned_to_nat(0);
                v___x_252_ = lean_nat_dec_eq(v_i_249_, v___x_251_);
                if v___x_252_ == 0 {
                    v_i_x27_253_ = lean_string_utf8_prev(v_s_248_, v_i_249_);
                    leanh::lean_dec(v_i_249_);
                    v_c_254_ = lean_string_utf8_get(v_s_248_, v_i_x27_253_);
                    v___x_255_ = l_System_FilePath_pathSeparator;
                    v___x_256_ = lean_uint32_dec_eq(v_c_254_, v___x_255_);
                    if v___x_256_ == 0 {
                        v___x_257_ = 46;
                        v___x_258_ = lean_uint32_dec_eq(v_c_254_, v___x_257_);
                        if v___x_258_ == 0 {
                            v_i_249_ = v_i_x27_253_;
                            state = 0;
                            continue;
                        } else {
                            leanh::lean_dec(v_e_250_);
                            leanh::lean_inc(v_i_x27_253_);
                            v_i_249_ = v_i_x27_253_;
                            v_e_250_ = v_i_x27_253_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_i_x27_253_);
                        v___x_261_ = lean_string_utf8_extract(v_s_248_, v___x_251_, v_e_250_);
                        leanh::lean_dec(v_e_250_);
                        return v___x_261_;
                    }
                } else {
                    leanh::lean_dec(v_i_249_);
                    v___x_262_ = lean_string_utf8_extract(v_s_248_, v___x_251_, v_e_250_);
                    leanh::lean_dec(v_e_250_);
                    return v___x_262_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts___boxed(
    mut v_s_263_: *mut leanh::LeanObject,
    mut v_i_264_: *mut leanh::LeanObject,
    mut v_e_265_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_266_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(
        v_s_263_, v_i_264_, v_e_265_,
    );
    leanh::lean_dec_ref(v_s_263_);
    return v_res_266_;
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_268_: u32 = 0;
    let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_268_ = l_System_FilePath_pathSeparator;
    v___x_269_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__0;
    v___x_270_ = lean_string_push(v___x_269_, v___x_268_);
    return v___x_270_;
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_271_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
    v___x_272_ = lean_string_utf8_byte_size(v___x_271_);
    return v___x_272_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(
    mut v_s_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: u8 = 0;
    let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: u8 = 0;
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_288_: u8 = 0;
    let mut v___x_289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_293_: u8 = 0;
    let mut v_unused_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_274_ = leanh::lean_ctor_get(v_s_273_, 0);
                v_startInclusive_275_ = leanh::lean_ctor_get(v_s_273_, 1);
                v_endExclusive_276_ = leanh::lean_ctor_get(v_s_273_, 2);
                v___x_277_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
                v___x_278_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__2);
                v___x_279_ = lean_nat_sub(v_endExclusive_276_, v_startInclusive_275_);
                v___x_280_ = lean_nat_dec_le(v___x_278_, v___x_279_);
                if v___x_280_ == 0 {
                    leanh::lean_dec(v___x_279_);
                    return v_s_273_;
                } else {
                    v___x_281_ = leanh::lean_unsigned_to_nat(0);
                    v___x_282_ = lean_nat_sub(v___x_279_, v___x_278_);
                    leanh::lean_dec(v___x_279_);
                    v___x_283_ = lean_nat_add(v_startInclusive_275_, v___x_282_);
                    v___x_284_ = lean_string_memcmp(
                        v_str_274_, v___x_277_, v___x_283_, v___x_281_, v___x_278_,
                    );
                    leanh::lean_dec(v___x_283_);
                    if v___x_284_ == 0 {
                        leanh::lean_dec(v___x_282_);
                        return v_s_273_;
                    } else {
                        leanh::lean_inc(v_startInclusive_275_);
                        leanh::lean_inc_ref(v_str_274_);
                        v___x_285_ = l_String_Slice_pos_x21(v_s_273_, v___x_282_);
                        leanh::lean_dec(v___x_282_);
                        v_isSharedCheck_293_ = (!leanh::lean_is_exclusive(v_s_273_)) as u8;
                        if v_isSharedCheck_293_ == 0 {
                            v_unused_294_ = leanh::lean_ctor_get(v_s_273_, 2);
                            leanh::lean_dec(v_unused_294_);
                            v_unused_295_ = leanh::lean_ctor_get(v_s_273_, 1);
                            leanh::lean_dec(v_unused_295_);
                            v_unused_296_ = leanh::lean_ctor_get(v_s_273_, 0);
                            leanh::lean_dec(v_unused_296_);
                            v___x_287_ = v_s_273_;
                            v_isShared_288_ = v_isSharedCheck_293_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_s_273_);
                            v___x_287_ = leanh::lean_box(0);
                            v_isShared_288_ = v_isSharedCheck_293_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_289_ = lean_nat_add(v_startInclusive_275_, v___x_285_);
                leanh::lean_dec(v___x_285_);
                if v_isShared_288_ == 0 {
                    leanh::lean_ctor_set(v___x_287_, 2, v___x_289_);
                    v___x_291_ = v___x_287_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_292_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_292_, 0, v_str_274_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_292_, 1, v_startInclusive_275_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_292_, 2, v___x_289_);
                    v___x_291_ = v_reuseFailAlloc_292_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_291_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(
    mut v_s_297_: *mut leanh::LeanObject,
    mut v_pat_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = leanh::lean_unsigned_to_nat(0);
    v___x_300_ = lean_string_utf8_byte_size(v_s_297_);
    v___x_301_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_301_, 0, v_s_297_);
    leanh::lean_ctor_set(v___x_301_, 1, v___x_299_);
    leanh::lean_ctor_set(v___x_301_, 2, v___x_300_);
    v___x_302_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v___x_301_);
    return v___x_302_;
}
pub unsafe fn l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0___boxed(
    mut v_s_303_: *mut leanh::LeanObject,
    mut v_pat_304_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_305_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_s_303_, v_pat_304_);
    leanh::lean_dec_ref(v_pat_304_);
    return v_res_305_;
}
pub unsafe fn l_List_foldl___at___00Lake_modOfFilePath_spec__1(
    mut v_x_306_: *mut leanh::LeanObject,
    mut v_x_307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_head_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_307_) == 0 {
                    return v_x_306_;
                } else {
                    v_head_308_ = leanh::lean_ctor_get(v_x_307_, 0);
                    leanh::lean_inc(v_head_308_);
                    v_tail_309_ = leanh::lean_ctor_get(v_x_307_, 1);
                    leanh::lean_inc(v_tail_309_);
                    leanh::lean_dec_ref_known(v_x_307_, 2);
                    v___x_310_ = l_Lean_Name_str___override(v_x_306_, v_head_308_);
                    v_x_306_ = v___x_310_;
                    v_x_307_ = v_tail_309_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_modOfFilePath(
    mut v_path_312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_path_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_313_ = l_System_FilePath_normalize(v_path_312_);
    v___x_314_ = lean_string_utf8_byte_size(v___x_313_);
    v_path_315_ = l___private_Lake_Util_FilePath_0__Lake_modOfFilePath_removeExts(
        v___x_313_, v___x_314_, v___x_314_,
    );
    leanh::lean_dec_ref(v___x_313_);
    v___x_316_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg___closed__1);
    v_path_317_ = l_String_dropSuffix___at___00Lake_modOfFilePath_spec__0(v_path_315_, v___x_316_);
    v_str_318_ = leanh::lean_ctor_get(v_path_317_, 0);
    leanh::lean_inc_ref(v_str_318_);
    v_startInclusive_319_ = leanh::lean_ctor_get(v_path_317_, 1);
    leanh::lean_inc(v_startInclusive_319_);
    v_endExclusive_320_ = leanh::lean_ctor_get(v_path_317_, 2);
    leanh::lean_inc(v_endExclusive_320_);
    leanh::lean_dec_ref(v_path_317_);
    v___x_321_ = leanh::lean_box(0);
    v___x_322_ = lean_string_utf8_extract(v_str_318_, v_startInclusive_319_, v_endExclusive_320_);
    leanh::lean_dec(v_endExclusive_320_);
    leanh::lean_dec(v_startInclusive_319_);
    leanh::lean_dec_ref(v_str_318_);
    v___x_323_ = l_System_FilePath_components(v___x_322_);
    v___x_324_ = l_List_foldl___at___00Lake_modOfFilePath_spec__1(v___x_321_, v___x_323_);
    return v___x_324_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(
    mut v_pat_325_: *mut leanh::LeanObject,
    mut v_s_326_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_327_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_327_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___redArg(v_s_326_);
    return v___x_327_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0___boxed(
    mut v_pat_328_: *mut leanh::LeanObject,
    mut v_s_329_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_330_ = l_String_Slice_dropSuffix___at___00String_dropSuffix___at___00Lake_modOfFilePath_spec__0_spec__0(v_pat_328_, v_s_329_);
    leanh::lean_dec_ref(v_pat_328_);
    return v_res_330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_FilePath(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_FilePath(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_FilePath(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_Json(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Modify(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_System_Platform(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_FilePath(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_FilePath(builtin);
}
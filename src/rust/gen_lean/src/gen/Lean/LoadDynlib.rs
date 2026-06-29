// Lean compiler output
// Module: Lean.LoadDynlib
// Imports: Init.System.IO Init.Data.String.TakeDrop Init.Data.ToString.Macro
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::Slice::l_String_Slice_toString;
use crate::r#gen::Init::Data::String::TakeDrop::{
    initialize_Init_Data_String_TakeDrop, runtime_initialize_Init_Data_String_TakeDrop,
};
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::System::FilePath::l_System_FilePath_fileStem;
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::ffi::lean_string_append;
use crate::ffi::lean_string_memcmp;
use crate::ffi::{
    lean_nat_add, lean_nat_dec_le, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::ffi::{lean_io_realpath, lean_runtime_mark_persistent};
use crate::ffi::{
    lean_dynlib_get, lean_dynlib_load, lean_dynlib_symbol_run_as_init,
};
pub static mut l___private_Lean_LoadDynlib_0__Lean_DynlibImpl: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value:
    crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [95, 115, 104, 97, 114, 101, 100, 0],
};
static mut l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [108, 105, 98, 0]};
static mut l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_loadPlugin___closed__0_value: crate::leanh::LeanStringObject<46> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 46,
        m_capacity: 46,
        m_length: 45,
        m_data: [
            101, 114, 114, 111, 114, 32, 108, 111, 97, 100, 105, 110, 103, 32, 112, 108, 117, 103,
            105, 110, 44, 32, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 114, 32, 110, 111,
            116, 32, 102, 111, 117, 110, 100, 32, 39, 0,
        ],
    };
static mut l_Lean_loadPlugin___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_loadPlugin___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_loadPlugin___closed__1_value: crate::leanh::LeanStringObject<2> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [39, 0],
    };
static mut l_Lean_loadPlugin___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_loadPlugin___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_loadPlugin___closed__2_value: crate::leanh::LeanStringObject<35> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 35,
        m_capacity: 35,
        m_length: 34,
        m_data: [
            108, 101, 97, 110, 95, 105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 114, 117,
            110, 116, 105, 109, 101, 95, 102, 111, 114, 95, 112, 108, 117, 103, 105, 110, 0,
        ],
    };
static mut l_Lean_loadPlugin___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_loadPlugin___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_loadPlugin___closed__3_value: crate::leanh::LeanStringObject<12> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 12,
        m_capacity: 12,
        m_length: 11,
        m_data: [105, 110, 105, 116, 105, 97, 108, 105, 122, 101, 95, 0],
    };
static mut l_Lean_loadPlugin___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_loadPlugin___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_loadPlugin___closed__4_value: crate::leanh::LeanStringObject<38> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 38,
        m_capacity: 38,
        m_length: 37,
        m_data: [
            101, 114, 114, 111, 114, 44, 32, 112, 108, 117, 103, 105, 110, 32, 104, 97, 115, 32,
            105, 110, 118, 97, 108, 105, 100, 32, 102, 105, 108, 101, 32, 110, 97, 109, 101, 32,
            39, 0,
        ],
    };
static mut l_Lean_loadPlugin___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_loadPlugin___closed__4_value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl() -> *mut crate::leanh::LeanObject
{
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = crate::leanh::lean_box(0);
    return v___x_214_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(
    mut v_dynlib_215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_216_ = crate::leanh::lean_box(0);
    return v___x_216_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl___boxed(
    mut v_dynlib_217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_218_ = l___private_Lean_LoadDynlib_0__Lean_Dynlib_SymbolImpl(v_dynlib_217_);
    crate::leanh::lean_dec(v_dynlib_217_);
    return v_res_218_;
}
pub unsafe fn l_Lean_Dynlib_load___boxed(
    mut v_path_221_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_222_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_223_ = lean_dynlib_load(v_path_221_);
    crate::leanh::lean_dec_ref(v_path_221_);
    return v_res_223_;
}
pub unsafe fn l_Lean_Dynlib_get_x3f___boxed(
    mut v_dynlib_226_: *mut crate::leanh::LeanObject,
    mut v_sym_227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_228_ = lean_dynlib_get(v_dynlib_226_, v_sym_227_);
    crate::leanh::lean_dec_ref(v_sym_227_);
    crate::leanh::lean_dec(v_dynlib_226_);
    return v_res_228_;
}
pub unsafe fn l_Lean_Dynlib_Symbol_runAsInit___boxed(
    mut v_dynlib_232_: *mut crate::leanh::LeanObject,
    mut v_sym_233_: *mut crate::leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ = lean_dynlib_symbol_run_as_init(v_dynlib_232_, v_sym_233_);
    crate::leanh::lean_dec(v_sym_233_);
    crate::leanh::lean_dec(v_dynlib_232_);
    return v_res_235_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(
    mut v_dynlib_236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_238_ = lean_runtime_mark_persistent(v_dynlib_236_);
    return v___x_238_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1___boxed(
    mut v_dynlib_239_: *mut crate::leanh::LeanObject,
    mut v_a_240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_241_ = l___private_Lean_LoadDynlib_0__Lean_loadDynlib_unsafe__1(v_dynlib_239_);
    return v_res_241_;
}
pub unsafe fn lean_load_dynlib(
    mut v_path_242_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_248_: u8 = 0;
    let mut v___x_249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_254_: u8 = 0;
    let mut v_a_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_262_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_244_ = lean_dynlib_load(v_path_242_);
                crate::leanh::lean_dec_ref(v_path_242_);
                if crate::leanh::lean_obj_tag(v___x_244_) == 0 {
                    v_a_245_ = crate::leanh::lean_ctor_get(v___x_244_, 0);
                    v_isSharedCheck_254_ = (!crate::leanh::lean_is_exclusive(v___x_244_)) as u8;
                    if v_isSharedCheck_254_ == 0 {
                        v___x_247_ = v___x_244_;
                        v_isShared_248_ = v_isSharedCheck_254_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_245_);
                        crate::leanh::lean_dec(v___x_244_);
                        v___x_247_ = crate::leanh::lean_box(0);
                        v_isShared_248_ = v_isSharedCheck_254_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_255_ = crate::leanh::lean_ctor_get(v___x_244_, 0);
                    v_isSharedCheck_262_ = (!crate::leanh::lean_is_exclusive(v___x_244_)) as u8;
                    if v_isSharedCheck_262_ == 0 {
                        v___x_257_ = v___x_244_;
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_255_);
                        crate::leanh::lean_dec(v___x_244_);
                        v___x_257_ = crate::leanh::lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_249_ = lean_runtime_mark_persistent(v_a_245_);
                crate::leanh::lean_dec(v___x_249_);
                v___x_250_ = crate::leanh::lean_box(0);
                if v_isShared_248_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_247_, 0, v___x_250_);
                    v___x_252_ = v___x_247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_253_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
                    v___x_252_ = v_reuseFailAlloc_253_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_252_;
            }
            3 => {
                if v_isShared_258_ == 0 {
                    v___x_260_ = v___x_257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_261_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
                    v___x_260_ = v_reuseFailAlloc_261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_260_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_loadDynlib___boxed(
    mut v_path_263_: *mut crate::leanh::LeanObject,
    mut v_a_264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_265_ = lean_load_dynlib(v_path_263_);
    return v_res_265_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(
    mut v_dynlib_266_: *mut crate::leanh::LeanObject,
    mut v_init_267_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_269_ = lean_dynlib_symbol_run_as_init(v_dynlib_266_, v_init_267_);
    return v___x_269_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4___boxed(
    mut v_dynlib_270_: *mut crate::leanh::LeanObject,
    mut v_init_271_: *mut crate::leanh::LeanObject,
    mut v_a_272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_273_ =
        l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__4(v_dynlib_270_, v_init_271_);
    crate::leanh::lean_dec(v_init_271_);
    crate::leanh::lean_dec(v_dynlib_270_);
    return v_res_273_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__9(
    mut v_dynlib_274_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_276_ = lean_runtime_mark_persistent(v_dynlib_274_);
    return v___x_276_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__9___boxed(
    mut v_dynlib_277_: *mut crate::leanh::LeanObject,
    mut v_a_278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_279_ = l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__9(v_dynlib_277_);
    return v_res_279_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__12(
    mut v_dynlib_280_: *mut crate::leanh::LeanObject,
    mut v_sym_281_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = lean_dynlib_symbol_run_as_init(v_dynlib_280_, v_sym_281_);
    return v___x_283_;
}
pub unsafe fn l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__12___boxed(
    mut v_dynlib_284_: *mut crate::leanh::LeanObject,
    mut v_sym_285_: *mut crate::leanh::LeanObject,
    mut v_a_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_287_ =
        l___private_Lean_LoadDynlib_0__Lean_loadPlugin_unsafe__12(v_dynlib_284_, v_sym_285_);
    crate::leanh::lean_dec(v_sym_285_);
    crate::leanh::lean_dec(v_dynlib_284_);
    return v_res_287_;
}
pub unsafe fn _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_289_ = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0;
    v___x_290_ = lean_string_utf8_byte_size(v___x_289_);
    return v___x_290_;
}
pub unsafe fn l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(
    mut v_s_291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_298_: u8 = 0;
    let mut v___x_299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_302_: u8 = 0;
    let mut v___x_303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_306_: u8 = 0;
    let mut v___x_307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_311_: u8 = 0;
    let mut v_unused_312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_292_ = crate::leanh::lean_ctor_get(v_s_291_, 0);
                v_startInclusive_293_ = crate::leanh::lean_ctor_get(v_s_291_, 1);
                v_endExclusive_294_ = crate::leanh::lean_ctor_get(v_s_291_, 2);
                v___x_295_ = l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__0;
                v___x_296_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1_once
                    ),
                    _init_l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1___closed__1,
                );
                v___x_297_ = lean_nat_sub(v_endExclusive_294_, v_startInclusive_293_);
                v___x_298_ = lean_nat_dec_le(v___x_296_, v___x_297_);
                if v___x_298_ == 0 {
                    crate::leanh::lean_dec(v___x_297_);
                    return v_s_291_;
                } else {
                    v___x_299_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_300_ = lean_nat_sub(v___x_297_, v___x_296_);
                    crate::leanh::lean_dec(v___x_297_);
                    v___x_301_ = lean_nat_add(v_startInclusive_293_, v___x_300_);
                    v___x_302_ = lean_string_memcmp(
                        v_str_292_, v___x_295_, v___x_301_, v___x_299_, v___x_296_,
                    );
                    crate::leanh::lean_dec(v___x_301_);
                    if v___x_302_ == 0 {
                        crate::leanh::lean_dec(v___x_300_);
                        return v_s_291_;
                    } else {
                        crate::leanh::lean_inc(v_startInclusive_293_);
                        crate::leanh::lean_inc_ref(v_str_292_);
                        v___x_303_ = l_String_Slice_pos_x21(v_s_291_, v___x_300_);
                        crate::leanh::lean_dec(v___x_300_);
                        v_isSharedCheck_311_ = (!crate::leanh::lean_is_exclusive(v_s_291_)) as u8;
                        if v_isSharedCheck_311_ == 0 {
                            v_unused_312_ = crate::leanh::lean_ctor_get(v_s_291_, 2);
                            crate::leanh::lean_dec(v_unused_312_);
                            v_unused_313_ = crate::leanh::lean_ctor_get(v_s_291_, 1);
                            crate::leanh::lean_dec(v_unused_313_);
                            v_unused_314_ = crate::leanh::lean_ctor_get(v_s_291_, 0);
                            crate::leanh::lean_dec(v_unused_314_);
                            v___x_305_ = v_s_291_;
                            v_isShared_306_ = v_isSharedCheck_311_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_291_);
                            v___x_305_ = crate::leanh::lean_box(0);
                            v_isShared_306_ = v_isSharedCheck_311_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_307_ = lean_nat_add(v_startInclusive_293_, v___x_303_);
                crate::leanh::lean_dec(v___x_303_);
                if v_isShared_306_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_305_, 2, v___x_307_);
                    v___x_309_ = v___x_305_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_310_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_310_, 0, v_str_292_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_310_, 1, v_startInclusive_293_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_310_, 2, v___x_307_);
                    v___x_309_ = v_reuseFailAlloc_310_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
    v___x_317_ = lean_string_utf8_byte_size(v___x_316_);
    return v___x_317_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(
    mut v_s_318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_325_: u8 = 0;
    let mut v___x_326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_327_: u8 = 0;
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_331_: u8 = 0;
    let mut v___x_332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_336_: u8 = 0;
    let mut v_unused_337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_319_ = crate::leanh::lean_ctor_get(v_s_318_, 0);
                v_startInclusive_320_ = crate::leanh::lean_ctor_get(v_s_318_, 1);
                v_endExclusive_321_ = crate::leanh::lean_ctor_get(v_s_318_, 2);
                v___x_322_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
                v___x_323_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1_once), _init_l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__1);
                v___x_324_ = lean_nat_sub(v_endExclusive_321_, v_startInclusive_320_);
                v___x_325_ = lean_nat_dec_le(v___x_323_, v___x_324_);
                crate::leanh::lean_dec(v___x_324_);
                if v___x_325_ == 0 {
                    return v_s_318_;
                } else {
                    v___x_326_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_327_ = lean_string_memcmp(
                        v_str_319_,
                        v___x_322_,
                        v_startInclusive_320_,
                        v___x_326_,
                        v___x_323_,
                    );
                    if v___x_327_ == 0 {
                        return v_s_318_;
                    } else {
                        crate::leanh::lean_inc(v_endExclusive_321_);
                        crate::leanh::lean_inc(v_startInclusive_320_);
                        crate::leanh::lean_inc_ref(v_str_319_);
                        v___x_328_ = l_String_Slice_pos_x21(v_s_318_, v___x_323_);
                        v_isSharedCheck_336_ = (!crate::leanh::lean_is_exclusive(v_s_318_)) as u8;
                        if v_isSharedCheck_336_ == 0 {
                            v_unused_337_ = crate::leanh::lean_ctor_get(v_s_318_, 2);
                            crate::leanh::lean_dec(v_unused_337_);
                            v_unused_338_ = crate::leanh::lean_ctor_get(v_s_318_, 1);
                            crate::leanh::lean_dec(v_unused_338_);
                            v_unused_339_ = crate::leanh::lean_ctor_get(v_s_318_, 0);
                            crate::leanh::lean_dec(v_unused_339_);
                            v___x_330_ = v_s_318_;
                            v_isShared_331_ = v_isSharedCheck_336_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_s_318_);
                            v___x_330_ = crate::leanh::lean_box(0);
                            v_isShared_331_ = v_isSharedCheck_336_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_332_ = lean_nat_add(v_startInclusive_320_, v___x_328_);
                crate::leanh::lean_dec(v___x_328_);
                crate::leanh::lean_dec(v_startInclusive_320_);
                if v_isShared_331_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_330_, 1, v___x_332_);
                    v___x_334_ = v___x_330_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_335_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_335_, 0, v_str_319_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_335_, 1, v___x_332_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_335_, 2, v_endExclusive_321_);
                    v___x_334_ = v_reuseFailAlloc_335_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(
    mut v_s_340_: *mut crate::leanh::LeanObject,
    mut v_pat_341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_342_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_343_ = lean_string_utf8_byte_size(v_s_340_);
    v___x_344_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_344_, 0, v_s_340_);
    crate::leanh::lean_ctor_set(v___x_344_, 1, v___x_342_);
    crate::leanh::lean_ctor_set(v___x_344_, 2, v___x_343_);
    v___x_345_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v___x_344_);
    return v___x_345_;
}
pub unsafe fn l_String_dropPrefix___at___00Lean_loadPlugin_spec__0___boxed(
    mut v_s_346_: *mut crate::leanh::LeanObject,
    mut v_pat_347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_348_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(v_s_346_, v_pat_347_);
    crate::leanh::lean_dec_ref(v_pat_347_);
    return v_res_348_;
}
pub unsafe fn lean_load_plugin(
    mut v_path_354_: *mut crate::leanh::LeanObject,
    mut v_initFn_x3f_355_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_374_: u8 = 0;
    let mut v_a_376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_386_: u8 = 0;
    let mut v___x_388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_390_: u8 = 0;
    let mut v___x_391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_408_: u8 = 0;
    let mut v_a_409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v___x_414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_416_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_370_ = lean_io_realpath(v_path_354_);
                if crate::leanh::lean_obj_tag(v___x_370_) == 0 {
                    v_a_371_ = crate::leanh::lean_ctor_get(v___x_370_, 0);
                    v_isSharedCheck_408_ = (!crate::leanh::lean_is_exclusive(v___x_370_)) as u8;
                    if v_isSharedCheck_408_ == 0 {
                        v___x_373_ = v___x_370_;
                        v_isShared_374_ = v_isSharedCheck_408_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_371_);
                        crate::leanh::lean_dec(v___x_370_);
                        v___x_373_ = crate::leanh::lean_box(0);
                        v_isShared_374_ = v_isSharedCheck_408_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_initFn_x3f_355_);
                    v_a_409_ = crate::leanh::lean_ctor_get(v___x_370_, 0);
                    v_isSharedCheck_416_ = (!crate::leanh::lean_is_exclusive(v___x_370_)) as u8;
                    if v_isSharedCheck_416_ == 0 {
                        v___x_411_ = v___x_370_;
                        v_isShared_412_ = v_isSharedCheck_416_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_409_);
                        crate::leanh::lean_dec(v___x_370_);
                        v___x_411_ = crate::leanh::lean_box(0);
                        v_isShared_412_ = v_isSharedCheck_416_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_360_ = lean_dynlib_get(v___y_358_, v___y_359_);
                if crate::leanh::lean_obj_tag(v___x_360_) == 1 {
                    crate::leanh::lean_dec_ref(v___y_359_);
                    v_val_361_ = crate::leanh::lean_ctor_get(v___x_360_, 0);
                    crate::leanh::lean_inc(v_val_361_);
                    crate::leanh::lean_dec_ref_known(v___x_360_, 1);
                    crate::leanh::lean_inc(v___y_358_);
                    v___x_362_ = lean_runtime_mark_persistent(v___y_358_);
                    crate::leanh::lean_dec(v___x_362_);
                    v___x_363_ = lean_dynlib_symbol_run_as_init(v___y_358_, v_val_361_);
                    crate::leanh::lean_dec(v_val_361_);
                    crate::leanh::lean_dec(v___y_358_);
                    return v___x_363_;
                } else {
                    crate::leanh::lean_dec(v___x_360_);
                    crate::leanh::lean_dec(v___y_358_);
                    v___x_364_ = l_Lean_loadPlugin___closed__0;
                    v___x_365_ = lean_string_append(v___x_364_, v___y_359_);
                    crate::leanh::lean_dec_ref(v___y_359_);
                    v___x_366_ = l_Lean_loadPlugin___closed__1;
                    v___x_367_ = lean_string_append(v___x_365_, v___x_366_);
                    v___x_368_ = lean_mk_io_user_error(v___x_367_);
                    v___x_369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_369_, 0, v___x_368_);
                    return v___x_369_;
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_initFn_x3f_355_) == 0 {
                    crate::leanh::lean_inc(v_a_371_);
                    v___x_391_ = l_System_FilePath_fileStem(v_a_371_);
                    if crate::leanh::lean_obj_tag(v___x_391_) == 1 {
                        crate::leanh::lean_del_object(v___x_373_);
                        v_val_392_ = crate::leanh::lean_ctor_get(v___x_391_, 0);
                        crate::leanh::lean_inc(v_val_392_);
                        crate::leanh::lean_dec_ref_known(v___x_391_, 1);
                        v___x_393_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg___closed__0;
                        v___x_394_ = l_String_dropPrefix___at___00Lean_loadPlugin_spec__0(
                            v_val_392_, v___x_393_,
                        );
                        v___x_395_ =
                            l_String_Slice_dropSuffix___at___00Lean_loadPlugin_spec__1(v___x_394_);
                        v___x_396_ = l_Lean_loadPlugin___closed__3;
                        v___x_397_ = l_String_Slice_toString(v___x_395_);
                        crate::leanh::lean_dec_ref(v___x_395_);
                        v___x_398_ = lean_string_append(v___x_396_, v___x_397_);
                        crate::leanh::lean_dec_ref(v___x_397_);
                        v_a_376_ = v___x_398_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_391_);
                        v___x_399_ = l_Lean_loadPlugin___closed__4;
                        v___x_400_ = lean_string_append(v___x_399_, v_a_371_);
                        crate::leanh::lean_dec(v_a_371_);
                        v___x_401_ = l_Lean_loadPlugin___closed__1;
                        v___x_402_ = lean_string_append(v___x_400_, v___x_401_);
                        v___x_403_ = lean_mk_io_user_error(v___x_402_);
                        if v_isShared_374_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_373_, 1);
                            crate::leanh::lean_ctor_set(v___x_373_, 0, v___x_403_);
                            v___x_405_ = v___x_373_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_406_, 0, v___x_403_);
                            v___x_405_ = v_reuseFailAlloc_406_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_373_);
                    v_val_407_ = crate::leanh::lean_ctor_get(v_initFn_x3f_355_, 0);
                    crate::leanh::lean_inc(v_val_407_);
                    crate::leanh::lean_dec_ref_known(v_initFn_x3f_355_, 1);
                    v_a_376_ = v_val_407_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_377_ = lean_dynlib_load(v_a_371_);
                crate::leanh::lean_dec(v_a_371_);
                if crate::leanh::lean_obj_tag(v___x_377_) == 0 {
                    v_a_378_ = crate::leanh::lean_ctor_get(v___x_377_, 0);
                    crate::leanh::lean_inc(v_a_378_);
                    crate::leanh::lean_dec_ref_known(v___x_377_, 1);
                    v___x_379_ = l_Lean_loadPlugin___closed__2;
                    v___x_380_ = lean_dynlib_get(v_a_378_, v___x_379_);
                    if crate::leanh::lean_obj_tag(v___x_380_) == 1 {
                        v_val_381_ = crate::leanh::lean_ctor_get(v___x_380_, 0);
                        crate::leanh::lean_inc(v_val_381_);
                        crate::leanh::lean_dec_ref_known(v___x_380_, 1);
                        v___x_382_ = lean_dynlib_symbol_run_as_init(v_a_378_, v_val_381_);
                        crate::leanh::lean_dec(v_val_381_);
                        if crate::leanh::lean_obj_tag(v___x_382_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_382_, 1);
                            v___y_358_ = v_a_378_;
                            v___y_359_ = v_a_376_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_378_);
                            crate::leanh::lean_dec_ref(v_a_376_);
                            return v___x_382_;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_380_);
                        v___y_358_ = v_a_378_;
                        v___y_359_ = v_a_376_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_a_376_);
                    v_a_383_ = crate::leanh::lean_ctor_get(v___x_377_, 0);
                    v_isSharedCheck_390_ = (!crate::leanh::lean_is_exclusive(v___x_377_)) as u8;
                    if v_isSharedCheck_390_ == 0 {
                        v___x_385_ = v___x_377_;
                        v_isShared_386_ = v_isSharedCheck_390_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_383_);
                        crate::leanh::lean_dec(v___x_377_);
                        v___x_385_ = crate::leanh::lean_box(0);
                        v_isShared_386_ = v_isSharedCheck_390_;
                        state = 4;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_386_ == 0 {
                    v___x_388_ = v___x_385_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_389_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_389_, 0, v_a_383_);
                    v___x_388_ = v_reuseFailAlloc_389_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_388_;
            }
            6 => {
                return v___x_405_;
            }
            7 => {
                if v_isShared_412_ == 0 {
                    v___x_414_ = v___x_411_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_409_);
                    v___x_414_ = v_reuseFailAlloc_415_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_loadPlugin___boxed(
    mut v_path_417_: *mut crate::leanh::LeanObject,
    mut v_initFn_x3f_418_: *mut crate::leanh::LeanObject,
    mut v_a_419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_420_ = lean_load_plugin(v_path_417_, v_initFn_x3f_418_);
    return v_res_420_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(
    mut v_pat_421_: *mut crate::leanh::LeanObject,
    mut v_s_422_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_423_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___redArg(v_s_422_);
    return v___x_423_;
}
pub unsafe fn l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0___boxed(
    mut v_pat_424_: *mut crate::leanh::LeanObject,
    mut v_s_425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_426_ = l_String_Slice_dropPrefix___at___00String_dropPrefix___at___00Lean_loadPlugin_spec__0_spec__0(v_pat_424_, v_s_425_);
    crate::leanh::lean_dec_ref(v_pat_424_);
    return v_res_426_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_LoadDynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l___private_Lean_LoadDynlib_0__Lean_DynlibImpl =
        _init_l___private_Lean_LoadDynlib_0__Lean_DynlibImpl();
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_LoadDynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_LoadDynlib(builtin: u8) -> *mut crate::leanh::LeanObject {
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
    res = initialize_Init_Data_String_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_LoadDynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_LoadDynlib(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_LoadDynlib(builtin);
}

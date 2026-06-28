// Lean compiler output
// Module: Std.Time.Zoned.Database.Windows
// Imports: Init.Data.SInt.Basic Std.Time.Zoned.Database.Basic Init.While
use crate::r#gen::Init::Data::Rat::Basic::l_Rat_ofInt;
use crate::r#gen::Init::Data::SInt::Basic::{
    initialize_Init_Data_SInt_Basic, runtime_initialize_Init_Data_SInt_Basic,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
use crate::r#gen::Init::While::{initialize_Init_While, runtime_initialize_Init_While};
use crate::r#gen::Std::Time::Zoned::Database::Basic::{
    initialize_Std_Time_Zoned_Database_Basic, runtime_initialize_Std_Time_Zoned_Database_Basic,
};
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Data::SInt::Basic::{
    lean_int64_dec_le, lean_int64_neg, lean_int64_of_nat, lean_int64_to_int_sint,
};
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_box_uint64, lean_cstr_to_nat,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent,
    lean_obj_once, lean_obj_tag, lean_uint64_once, lean_unbox, lean_unbox_uint64,
    lean_unsigned_to_nat,
};
static mut l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0: u64 = 0;
static mut l_Std_Time_Database_Windows_getZoneRules___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_Windows_getZoneRules___closed__0: u64 = 0;
static mut l_Std_Time_Database_Windows_getZoneRules___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_Windows_getZoneRules___closed__1: u64 = 0;
pub static l_Std_Time_Database_Windows_getZoneRules___closed__2_value: LeanArrayObject<0> =
    LeanArrayObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Std_Time_Database_Windows_getZoneRules___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_Windows_getZoneRules___closed__2_value)
        as *mut LeanObject;
pub static mut l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Std_Time_Database_Windows_getZoneRules___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_Windows_getZoneRules___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_Time_Database_Windows_getZoneRules___closed__4_value: LeanStringObject<43> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 43,
        m_capacity: 43,
        m_length: 42,
        m_data: [
            99, 97, 110, 110, 111, 116, 32, 102, 105, 110, 100, 32, 102, 105, 114, 115, 116, 32,
            116, 114, 97, 110, 115, 105, 116, 105, 111, 110, 32, 105, 110, 32, 122, 111, 110, 101,
            32, 114, 117, 108, 101, 115, 0,
        ],
    };
static mut l_Std_Time_Database_Windows_getZoneRules___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_Windows_getZoneRules___closed__4_value)
        as *mut LeanObject;
static mut l_Std_Time_Database_Windows_getZoneRules___closed__5_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Std_Time_Database_Windows_getZoneRules___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Std_Time_Database_WindowsDb_default: *mut LeanObject = core::ptr::null_mut();
pub static l_Std_Time_Database_WindowsDb_inst___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Database_WindowsDb_inst___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 3,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_WindowsDb_inst___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__0_value) as *mut LeanObject;
pub static l_Std_Time_Database_WindowsDb_inst___closed__1_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Std_Time_Database_WindowsDb_inst___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_Time_Database_WindowsDb_inst___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__1_value) as *mut LeanObject;
pub static l_Std_Time_Database_WindowsDb_inst___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__0_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__1_value)
                as *mut LeanObject,
        ],
    };
static mut l_Std_Time_Database_WindowsDb_inst___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__2_value) as *mut LeanObject;
pub static mut l_Std_Time_Database_WindowsDb_inst: *mut LeanObject =
    core::ptr::addr_of!(l_Std_Time_Database_WindowsDb_inst___closed__2_value) as *mut LeanObject;
pub unsafe fn l_Std_Time_Database_Windows_getNextTransition___boxed(
    mut v_a_00___x40___internal___hyg_216_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_217_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_218_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_219_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_2__boxed_220_: u64 = 0;
    let mut v_a_00___x40___internal___hyg_3__boxed_221_: u8 = 0;
    let mut v_res_222_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_2__boxed_220_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_217_);
    lean_dec_ref(v_a_00___x40___internal___hyg_217_);
    v_a_00___x40___internal___hyg_3__boxed_221_ =
        (lean_unbox(v_a_00___x40___internal___hyg_218_) as u8);
    v_res_222_ = lean_windows_get_next_transition(
        v_a_00___x40___internal___hyg_216_,
        v_a_00___x40___internal___hyg_2__boxed_220_,
        v_a_00___x40___internal___hyg_3__boxed_221_,
    );
    lean_dec_ref(v_a_00___x40___internal___hyg_216_);
    return v_res_222_;
}
pub unsafe fn l_Std_Time_Database_Windows_getLocalTimeZoneIdentifierAt___boxed(
    mut v_a_00___x40___internal___hyg_225_: *mut LeanObject,
    mut v_a_00___x40___internal___hyg_226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_227_: u64 = 0;
    let mut v_res_228_: *mut LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_227_ =
        lean_unbox_uint64(v_a_00___x40___internal___hyg_225_);
    lean_dec_ref(v_a_00___x40___internal___hyg_225_);
    v_res_228_ = lean_get_windows_local_timezone_id_at(v_a_00___x40___internal___hyg_1__boxed_227_);
    return v_res_228_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(
    mut v_res_229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_offset_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_abbreviation_232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isDST_233_: u8 = 0;
    let mut v___x_234_: u8 = 0;
    let mut v___x_235_: u8 = 0;
    let mut v___x_236_: *mut LeanObject = core::ptr::null_mut();
    v_offset_230_ = lean_ctor_get(v_res_229_, 0);
    v_name_231_ = lean_ctor_get(v_res_229_, 1);
    v_abbreviation_232_ = lean_ctor_get(v_res_229_, 2);
    v_isDST_233_ = lean_ctor_get_uint8(
        v_res_229_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
    );
    v___x_234_ = 0;
    v___x_235_ = 1;
    lean_inc_ref(v_name_231_);
    lean_inc_ref(v_abbreviation_232_);
    lean_inc(v_offset_230_);
    v___x_236_ = lean_alloc_ctor(0, 3, (3) as u32);
    lean_ctor_set(v___x_236_, 0, v_offset_230_);
    lean_ctor_set(v___x_236_, 1, v_abbreviation_232_);
    lean_ctor_set(v___x_236_, 2, v_name_231_);
    lean_ctor_set_uint8(
        v___x_236_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v_isDST_233_,
    );
    lean_ctor_set_uint8(
        v___x_236_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 1) as u32,
        v___x_234_,
    );
    lean_ctor_set_uint8(
        v___x_236_,
        (core::mem::size_of::<*mut LeanObject>() * 3 + 2) as u32,
        v___x_235_,
    );
    return v___x_236_;
}
pub unsafe fn l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime___boxed(
    mut v_res_237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_238_: *mut LeanObject = core::ptr::null_mut();
    v_res_238_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_res_237_);
    lean_dec_ref(v_res_237_);
    return v_res_238_;
}
pub unsafe fn _init_l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0()
-> u64 {
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_240_: u64 = 0;
    v___x_239_ = lean_cstr_to_nat(b"32503690800\0".as_ptr().cast());
    v___x_240_ = lean_int64_of_nat(v___x_239_);
    return v___x_240_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(
    mut v_id_241_: *mut LeanObject,
    mut v_a_242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fst_244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_248_: u8 = 0;
    let mut v___x_249_: u8 = 0;
    let mut v___x_250_: u64 = 0;
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_255_: u8 = 0;
    let mut v_val_256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_261_: u8 = 0;
    let mut v___x_262_: u64 = 0;
    let mut v___x_263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_274_: u64 = 0;
    let mut v___x_275_: u64 = 0;
    let mut v___x_276_: u8 = 0;
    let mut v___x_277_: u64 = 0;
    let mut v___x_278_: u64 = 0;
    let mut v___x_279_: u8 = 0;
    let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_284_: u8 = 0;
    let mut v___x_286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_291_: u8 = 0;
    let mut v_a_292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_295_: u8 = 0;
    let mut v___x_297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_299_: u8 = 0;
    let mut v_isSharedCheck_300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_244_ = lean_ctor_get(v_a_242_, 0);
                v_snd_245_ = lean_ctor_get(v_a_242_, 1);
                v_isSharedCheck_300_ = (!lean_is_exclusive(v_a_242_)) as u8;
                if v_isSharedCheck_300_ == 0 {
                    v___x_247_ = v_a_242_;
                    v_isShared_248_ = v_isSharedCheck_300_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snd_245_);
                    lean_inc(v_fst_244_);
                    lean_dec(v_a_242_);
                    v___x_247_ = lean_box(0);
                    v_isShared_248_ = v_isSharedCheck_300_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_249_ = 0;
                v___x_250_ = lean_unbox_uint64(v_fst_244_);
                v___x_251_ = lean_windows_get_next_transition(v_id_241_, v___x_250_, v___x_249_);
                if lean_obj_tag(v___x_251_) == 0 {
                    v_a_252_ = lean_ctor_get(v___x_251_, 0);
                    v_isSharedCheck_291_ = (!lean_is_exclusive(v___x_251_)) as u8;
                    if v_isSharedCheck_291_ == 0 {
                        v___x_254_ = v___x_251_;
                        v_isShared_255_ = v_isSharedCheck_291_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_252_);
                        lean_dec(v___x_251_);
                        v___x_254_ = lean_box(0);
                        v_isShared_255_ = v_isSharedCheck_291_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_247_);
                    lean_dec(v_snd_245_);
                    lean_dec(v_fst_244_);
                    v_a_292_ = lean_ctor_get(v___x_251_, 0);
                    v_isSharedCheck_299_ = (!lean_is_exclusive(v___x_251_)) as u8;
                    if v_isSharedCheck_299_ == 0 {
                        v___x_294_ = v___x_251_;
                        v_isShared_295_ = v_isSharedCheck_299_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_292_);
                        lean_dec(v___x_251_);
                        v___x_294_ = lean_box(0);
                        v_isShared_295_ = v_isSharedCheck_299_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_252_) == 1 {
                    v_val_256_ = lean_ctor_get(v_a_252_, 0);
                    lean_inc(v_val_256_);
                    lean_dec_ref_known(v_a_252_, 1);
                    v_fst_257_ = lean_ctor_get(v_val_256_, 0);
                    v_snd_258_ = lean_ctor_get(v_val_256_, 1);
                    v_isSharedCheck_284_ = (!lean_is_exclusive(v_val_256_)) as u8;
                    if v_isSharedCheck_284_ == 0 {
                        v___x_260_ = v_val_256_;
                        v_isShared_261_ = v_isSharedCheck_284_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_snd_258_);
                        lean_inc(v_fst_257_);
                        lean_dec(v_val_256_);
                        v___x_260_ = lean_box(0);
                        v_isShared_261_ = v_isSharedCheck_284_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_252_);
                    if v_isShared_248_ == 0 {
                        v___x_286_ = v___x_247_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_290_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_290_, 0, v_fst_244_);
                        lean_ctor_set(v_reuseFailAlloc_290_, 1, v_snd_245_);
                        v___x_286_ = v_reuseFailAlloc_290_;
                        state = 8;
                        continue;
                    }
                }
            }
            3 => {
                v___x_262_ = lean_unbox_uint64(v_fst_244_);
                v___x_263_ = lean_int64_to_int_sint(v___x_262_);
                v___x_264_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_258_);
                lean_dec(v_snd_258_);
                v___x_265_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_265_, 0, v___x_263_);
                lean_ctor_set(v___x_265_, 1, v___x_264_);
                v___x_266_ = lean_array_push(v_snd_245_, v___x_265_);
                v___x_274_ = lean_unbox_uint64(v_fst_257_);
                v___x_275_ = lean_unbox_uint64(v_fst_244_);
                v___x_276_ = lean_int64_dec_le(v___x_274_, v___x_275_);
                if v___x_276_ == 0 {
                    v___x_277_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0_once), _init_l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___closed__0);
                    v___x_278_ = lean_unbox_uint64(v_fst_257_);
                    v___x_279_ = lean_int64_dec_le(v___x_277_, v___x_278_);
                    if v___x_279_ == 0 {
                        lean_del_object(v___x_260_);
                        lean_del_object(v___x_254_);
                        lean_dec(v_fst_244_);
                        if v_isShared_248_ == 0 {
                            lean_ctor_set(v___x_247_, 1, v___x_266_);
                            lean_ctor_set(v___x_247_, 0, v_fst_257_);
                            v___x_281_ = v___x_247_;
                            state = 7;
                            continue;
                        } else {
                            v_reuseFailAlloc_283_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_283_, 0, v_fst_257_);
                            lean_ctor_set(v_reuseFailAlloc_283_, 1, v___x_266_);
                            v___x_281_ = v_reuseFailAlloc_283_;
                            state = 7;
                            continue;
                        }
                    } else {
                        lean_dec(v_fst_257_);
                        lean_del_object(v___x_247_);
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v_fst_257_);
                    lean_del_object(v___x_247_);
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_261_ == 0 {
                    lean_ctor_set(v___x_260_, 1, v___x_266_);
                    lean_ctor_set(v___x_260_, 0, v_fst_244_);
                    v___x_269_ = v___x_260_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_273_, 0, v_fst_244_);
                    lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_266_);
                    v___x_269_ = v_reuseFailAlloc_273_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_255_ == 0 {
                    lean_ctor_set(v___x_254_, 0, v___x_269_);
                    v___x_271_ = v___x_254_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_269_);
                    v___x_271_ = v_reuseFailAlloc_272_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_271_;
            }
            7 => {
                v_a_242_ = v___x_281_;
                state = 0;
                continue;
            }
            8 => {
                if v_isShared_255_ == 0 {
                    lean_ctor_set(v___x_254_, 0, v___x_286_);
                    v___x_288_ = v___x_254_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_289_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_289_, 0, v___x_286_);
                    v___x_288_ = v_reuseFailAlloc_289_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_288_;
            }
            10 => {
                if v_isShared_295_ == 0 {
                    v___x_297_ = v___x_294_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_298_, 0, v_a_292_);
                    v___x_297_ = v_reuseFailAlloc_298_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_297_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg___boxed(
    mut v_id_301_: *mut LeanObject,
    mut v_a_302_: *mut LeanObject,
    mut v___y_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_304_: *mut LeanObject = core::ptr::null_mut();
    v_res_304_ = l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_301_, v_a_302_);
    lean_dec_ref(v_id_301_);
    return v_res_304_;
}
pub unsafe fn _init_l_Std_Time_Database_Windows_getZoneRules___closed__0() -> u64 {
    let mut v___x_305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_306_: u64 = 0;
    v___x_305_ = lean_unsigned_to_nat(2147483648);
    v___x_306_ = lean_int64_of_nat(v___x_305_);
    return v___x_306_;
}
pub unsafe fn _init_l_Std_Time_Database_Windows_getZoneRules___closed__1() -> u64 {
    let mut v___x_307_: u64 = 0;
    let mut v_start_308_: u64 = 0;
    v___x_307_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__0),
        core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__0_once),
        _init_l_Std_Time_Database_Windows_getZoneRules___closed__0,
    );
    v_start_308_ = lean_int64_neg(v___x_307_);
    return v_start_308_;
}
pub unsafe fn _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1()
-> *mut LeanObject {
    let mut v___x_311_: u64 = 0;
    let mut v___x_312_: *mut LeanObject = core::ptr::null_mut();
    v___x_311_ = lean_uint64_once(
        core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__1),
        core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__1_once),
        _init_l_Std_Time_Database_Windows_getZoneRules___closed__1,
    );
    v___x_312_ = lean_box_uint64(v___x_311_);
    return v___x_312_;
}
pub unsafe fn _init_l_Std_Time_Database_Windows_getZoneRules___closed__3() -> *mut LeanObject {
    let mut v_transitions_313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_315_: *mut LeanObject = core::ptr::null_mut();
    v_transitions_313_ = l_Std_Time_Database_Windows_getZoneRules___closed__2;
    v___x_314_ = l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1;
    v___x_315_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_315_, 0, v___x_314_);
    lean_ctor_set(v___x_315_, 1, v_transitions_313_);
    return v___x_315_;
}
pub unsafe fn _init_l_Std_Time_Database_Windows_getZoneRules___closed__5() -> *mut LeanObject {
    let mut v___x_317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_318_: *mut LeanObject = core::ptr::null_mut();
    v___x_317_ = l_Std_Time_Database_Windows_getZoneRules___closed__4;
    v___x_318_ = lean_mk_io_user_error(v___x_317_);
    return v___x_318_;
}
pub unsafe fn l_Std_Time_Database_Windows_getZoneRules(
    mut v_id_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_start_321_: u64 = 0;
    let mut v___x_322_: u8 = 0;
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v_val_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_334_: u8 = 0;
    let mut v_snd_335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_339_: u8 = 0;
    let mut v___x_340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_347_: u8 = 0;
    let mut v_unused_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_349_: u8 = 0;
    let mut v_a_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_357_: u8 = 0;
    let mut v___x_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_start_321_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_Database_Windows_getZoneRules___closed__1_once
                    ),
                    _init_l_Std_Time_Database_Windows_getZoneRules___closed__1,
                );
                v___x_322_ = 1;
                v___x_323_ = lean_windows_get_next_transition(v_id_319_, v_start_321_, v___x_322_);
                if lean_obj_tag(v___x_323_) == 0 {
                    v_a_324_ = lean_ctor_get(v___x_323_, 0);
                    v_isSharedCheck_362_ = (!lean_is_exclusive(v___x_323_)) as u8;
                    if v_isSharedCheck_362_ == 0 {
                        v___x_326_ = v___x_323_;
                        v_isShared_327_ = v_isSharedCheck_362_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_324_);
                        lean_dec(v___x_323_);
                        v___x_326_ = lean_box(0);
                        v_isShared_327_ = v_isSharedCheck_362_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_363_ = lean_ctor_get(v___x_323_, 0);
                    v_isSharedCheck_370_ = (!lean_is_exclusive(v___x_323_)) as u8;
                    if v_isSharedCheck_370_ == 0 {
                        v___x_365_ = v___x_323_;
                        v_isShared_366_ = v_isSharedCheck_370_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_363_);
                        lean_dec(v___x_323_);
                        v___x_365_ = lean_box(0);
                        v_isShared_366_ = v_isSharedCheck_370_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_324_) == 1 {
                    lean_del_object(v___x_326_);
                    v_val_328_ = lean_ctor_get(v_a_324_, 0);
                    lean_inc(v_val_328_);
                    lean_dec_ref_known(v_a_324_, 1);
                    v___x_329_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_Windows_getZoneRules___closed__3
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_Windows_getZoneRules___closed__3_once
                        ),
                        _init_l_Std_Time_Database_Windows_getZoneRules___closed__3,
                    );
                    v___x_330_ = l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_319_, v___x_329_);
                    if lean_obj_tag(v___x_330_) == 0 {
                        v_a_331_ = lean_ctor_get(v___x_330_, 0);
                        v_isSharedCheck_349_ = (!lean_is_exclusive(v___x_330_)) as u8;
                        if v_isSharedCheck_349_ == 0 {
                            v___x_333_ = v___x_330_;
                            v_isShared_334_ = v_isSharedCheck_349_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_331_);
                            lean_dec(v___x_330_);
                            v___x_333_ = lean_box(0);
                            v_isShared_334_ = v_isSharedCheck_349_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_328_);
                        v_a_350_ = lean_ctor_get(v___x_330_, 0);
                        v_isSharedCheck_357_ = (!lean_is_exclusive(v___x_330_)) as u8;
                        if v_isSharedCheck_357_ == 0 {
                            v___x_352_ = v___x_330_;
                            v_isShared_353_ = v_isSharedCheck_357_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_350_);
                            lean_dec(v___x_330_);
                            v___x_352_ = lean_box(0);
                            v_isShared_353_ = v_isSharedCheck_357_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_324_);
                    v___x_358_ = lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_Windows_getZoneRules___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Std_Time_Database_Windows_getZoneRules___closed__5_once
                        ),
                        _init_l_Std_Time_Database_Windows_getZoneRules___closed__5,
                    );
                    if v_isShared_327_ == 0 {
                        lean_ctor_set_tag(v___x_326_, 1);
                        lean_ctor_set(v___x_326_, 0, v___x_358_);
                        v___x_360_ = v___x_326_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_361_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
                        v___x_360_ = v_reuseFailAlloc_361_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v_snd_335_ = lean_ctor_get(v_val_328_, 1);
                lean_inc(v_snd_335_);
                lean_dec(v_val_328_);
                v_snd_336_ = lean_ctor_get(v_a_331_, 1);
                v_isSharedCheck_347_ = (!lean_is_exclusive(v_a_331_)) as u8;
                if v_isSharedCheck_347_ == 0 {
                    v_unused_348_ = lean_ctor_get(v_a_331_, 0);
                    lean_dec(v_unused_348_);
                    v___x_338_ = v_a_331_;
                    v_isShared_339_ = v_isSharedCheck_347_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_336_);
                    lean_dec(v_a_331_);
                    v___x_338_ = lean_box(0);
                    v_isShared_339_ = v_isSharedCheck_347_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_340_ = l___private_Std_Time_Zoned_Database_Windows_0__Std_Time_Database_Windows_getZoneRules_toLocalTime(v_snd_335_);
                lean_dec(v_snd_335_);
                if v_isShared_339_ == 0 {
                    lean_ctor_set(v___x_338_, 0, v___x_340_);
                    v___x_342_ = v___x_338_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_346_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_346_, 0, v___x_340_);
                    lean_ctor_set(v_reuseFailAlloc_346_, 1, v_snd_336_);
                    v___x_342_ = v_reuseFailAlloc_346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_334_ == 0 {
                    lean_ctor_set(v___x_333_, 0, v___x_342_);
                    v___x_344_ = v___x_333_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_345_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_345_, 0, v___x_342_);
                    v___x_344_ = v_reuseFailAlloc_345_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_344_;
            }
            6 => {
                if v_isShared_353_ == 0 {
                    v___x_355_ = v___x_352_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_356_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_356_, 0, v_a_350_);
                    v___x_355_ = v_reuseFailAlloc_356_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_355_;
            }
            8 => {
                return v___x_360_;
            }
            9 => {
                if v_isShared_366_ == 0 {
                    v___x_368_ = v___x_365_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
                    v___x_368_ = v_reuseFailAlloc_369_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_Windows_getZoneRules___boxed(
    mut v_id_371_: *mut LeanObject,
    mut v_a_372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_373_: *mut LeanObject = core::ptr::null_mut();
    v_res_373_ = l_Std_Time_Database_Windows_getZoneRules(v_id_371_);
    lean_dec_ref(v_id_371_);
    return v_res_373_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0_spec__0(
    mut v_a_374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    v___x_375_ = lean_nat_to_int(v_a_374_);
    return v___x_375_;
}
pub unsafe fn l_Nat_cast___at___00Std_Time_Database_Windows_getZoneRules_spec__0(
    mut v_a_376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_378_: *mut LeanObject = core::ptr::null_mut();
    v___x_377_ = lean_nat_to_int(v_a_376_);
    v___x_378_ = l_Rat_ofInt(v___x_377_);
    return v___x_378_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(
    mut v_id_379_: *mut LeanObject,
    mut v_inst_380_: *mut LeanObject,
    mut v_a_381_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_383_: *mut LeanObject = core::ptr::null_mut();
    v___x_383_ = l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___redArg(v_id_379_, v_a_381_);
    return v___x_383_;
}
pub unsafe fn l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1___boxed(
    mut v_id_384_: *mut LeanObject,
    mut v_inst_385_: *mut LeanObject,
    mut v_a_386_: *mut LeanObject,
    mut v___y_387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_388_: *mut LeanObject = core::ptr::null_mut();
    v_res_388_ = l___private_Init_While_0__whileM_erased___at___00Std_Time_Database_Windows_getZoneRules_spec__1(v_id_384_, v_inst_385_, v_a_386_);
    lean_dec_ref(v_id_384_);
    return v_res_388_;
}
pub unsafe fn l_Std_Time_Database_WindowsDb_toCtorIdx(
    mut v_x_389_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    v___x_390_ = lean_unsigned_to_nat(0);
    return v___x_390_;
}
pub unsafe fn _init_l_Std_Time_Database_WindowsDb_default() -> *mut LeanObject {
    let mut v___x_391_: *mut LeanObject = core::ptr::null_mut();
    v___x_391_ = lean_box(0);
    return v___x_391_;
}
pub unsafe fn l_Std_Time_Database_WindowsDb_inst___lam__0(
    mut v_x_392_: *mut LeanObject,
    mut v_id_393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    v___x_395_ = l_Std_Time_Database_Windows_getZoneRules(v_id_393_);
    return v___x_395_;
}
pub unsafe fn l_Std_Time_Database_WindowsDb_inst___lam__0___boxed(
    mut v_x_396_: *mut LeanObject,
    mut v_id_397_: *mut LeanObject,
    mut v___y_398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_399_: *mut LeanObject = core::ptr::null_mut();
    v_res_399_ = l_Std_Time_Database_WindowsDb_inst___lam__0(v_x_396_, v_id_397_);
    lean_dec_ref(v_id_397_);
    return v_res_399_;
}
pub unsafe fn l_Std_Time_Database_WindowsDb_inst___lam__1(
    mut v_x_400_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_402_: u64 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_405_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_409_: u8 = 0;
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_413_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_402_ = lean_uint64_once(
                    core::ptr::addr_of_mut!(l_Std_Time_Database_Windows_getZoneRules___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Std_Time_Database_Windows_getZoneRules___closed__1_once
                    ),
                    _init_l_Std_Time_Database_Windows_getZoneRules___closed__1,
                );
                v___x_403_ = lean_get_windows_local_timezone_id_at(v___x_402_);
                if lean_obj_tag(v___x_403_) == 0 {
                    v_a_404_ = lean_ctor_get(v___x_403_, 0);
                    lean_inc(v_a_404_);
                    lean_dec_ref_known(v___x_403_, 1);
                    v___x_405_ = l_Std_Time_Database_Windows_getZoneRules(v_a_404_);
                    lean_dec(v_a_404_);
                    return v___x_405_;
                } else {
                    v_a_406_ = lean_ctor_get(v___x_403_, 0);
                    v_isSharedCheck_413_ = (!lean_is_exclusive(v___x_403_)) as u8;
                    if v_isSharedCheck_413_ == 0 {
                        v___x_408_ = v___x_403_;
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_406_);
                        lean_dec(v___x_403_);
                        v___x_408_ = lean_box(0);
                        v_isShared_409_ = v_isSharedCheck_413_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_409_ == 0 {
                    v___x_411_ = v___x_408_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_406_);
                    v___x_411_ = v_reuseFailAlloc_412_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_411_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_Time_Database_WindowsDb_inst___lam__1___boxed(
    mut v_x_414_: *mut LeanObject,
    mut v___y_415_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_416_: *mut LeanObject = core::ptr::null_mut();
    v_res_416_ = l_Std_Time_Database_WindowsDb_inst___lam__1(v_x_414_);
    return v_res_416_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Std_Time_Zoned_Database_Windows(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1 =
        _init_l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1();
    lean_mark_persistent(l_Std_Time_Database_Windows_getZoneRules___closed__3___boxed__const__1);
    l_Std_Time_Database_WindowsDb_default = _init_l_Std_Time_Database_WindowsDb_default();
    lean_mark_persistent(l_Std_Time_Database_WindowsDb_default);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Std_Time_Zoned_Database_Windows(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Std_Time_Zoned_Database_Windows(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_SInt_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Std_Time_Zoned_Database_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_While(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Std_Time_Zoned_Database_Windows(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Std_Time_Zoned_Database_Windows(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Std_Time_Zoned_Database_Windows(builtin);
}

// Lean compiler output
// Module: Lean.InternalExceptionId
// Imports: Init.System.IO Init.Data.ToString.Name Init.Data.ToString.Macro
use crate::ffi::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_array_uget_borrowed, lean_name_eq,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take, lean_string_append, lean_usize_add, lean_usize_dec_eq, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::ToString::Macro::{
    initialize_Init_Data_ToString_Macro, runtime_initialize_Init_Data_ToString_Macro,
};
use crate::r#gen::Init::Data::ToString::Name::{
    initialize_Init_Data_ToString_Name,
    l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
    runtime_initialize_Init_Data_ToString_Name,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Init::System::IOError::lean_mk_io_user_error;
pub static mut l_Lean_instInhabitedInternalExceptionId_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_instInhabitedInternalExceptionId: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_instBEqInternalExceptionId___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_instBEqInternalExceptionId_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_instBEqInternalExceptionId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqInternalExceptionId___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_instBEqInternalExceptionId: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_instBEqInternalExceptionId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static mut l_Lean_internalExceptionsRef: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_registerInternalExceptionId___closed__0_value: leanh::LeanStringObject<
    33,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 33,
    m_capacity: 33,
    m_length: 32,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120,
        99, 101, 112, 116, 105, 111, 110, 32, 105, 100, 44, 32, 39, 0,
    ],
};
static mut l_Lean_registerInternalExceptionId___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInternalExceptionId___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_registerInternalExceptionId___closed__1_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        39, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101, 101, 110, 32, 117,
        115, 101, 100, 0,
    ],
};
static mut l_Lean_registerInternalExceptionId___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_registerInternalExceptionId___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_InternalExceptionId_toString___closed__0_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32,
        35, 0,
    ],
};
static mut l_Lean_InternalExceptionId_toString___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_InternalExceptionId_toString___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_InternalExceptionId_getName___closed__0_value: leanh::LeanStringObject<
    30,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 30,
    m_capacity: 30,
    m_length: 29,
    m_data: [
        105, 110, 118, 97, 108, 105, 100, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 120,
        99, 101, 112, 116, 105, 111, 110, 32, 105, 100, 0,
    ],
};
static mut l_Lean_InternalExceptionId_getName___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_InternalExceptionId_getName___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_InternalExceptionId_getName___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_InternalExceptionId_getName___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn _init_l_Lean_instInhabitedInternalExceptionId_default()
-> *mut leanh::LeanObject {
    let mut v___x_94_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_94_ = leanh::lean_unsigned_to_nat(0);
    return v___x_94_;
}
pub unsafe fn _init_l_Lean_instInhabitedInternalExceptionId() -> *mut leanh::LeanObject {
    let mut v___x_95_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_95_ = leanh::lean_unsigned_to_nat(0);
    return v___x_95_;
}
pub unsafe fn l_Lean_instBEqInternalExceptionId_beq(
    mut v_x_96_: *mut leanh::LeanObject,
    mut v_x_97_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_98_: u8 = 0;
    v___x_98_ = lean_nat_dec_eq(v_x_96_, v_x_97_);
    return v___x_98_;
}
pub unsafe fn l_Lean_instBEqInternalExceptionId_beq___boxed(
    mut v_x_99_: *mut leanh::LeanObject,
    mut v_x_100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_101_: u8 = 0;
    let mut v_r_102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_101_ = l_Lean_instBEqInternalExceptionId_beq(v_x_99_, v_x_100_);
    leanh::lean_dec(v_x_100_);
    leanh::lean_dec(v_x_99_);
    v_r_102_ = leanh::lean_box((v_res_101_) as usize);
    return v_r_102_;
}
pub unsafe fn l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_108_ = l___private_Lean_InternalExceptionId_0__Lean_initFn___closed__0_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_;
    v___x_109_ = lean_st_mk_ref(v___x_108_);
    v___x_110_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_110_, 0, v___x_109_);
    return v___x_110_;
}
pub unsafe fn l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2____boxed(
    mut v_a_111_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_112_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_112_ = l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
    return v_res_112_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(
    mut v_a_113_: *mut leanh::LeanObject,
    mut v_as_114_: *mut leanh::LeanObject,
    mut v_i_115_: usize,
    mut v_stop_116_: usize,
) -> u8 {
    let mut v___x_117_: u8 = 0;
    let mut v___x_118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_119_: u8 = 0;
    let mut v___x_120_: usize = 0;
    let mut v___x_121_: usize = 0;
    let mut v___x_123_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_117_ = lean_usize_dec_eq(v_i_115_, v_stop_116_);
                if v___x_117_ == 0 {
                    v___x_118_ = lean_array_uget_borrowed(v_as_114_, v_i_115_);
                    v___x_119_ = lean_name_eq(v_a_113_, v___x_118_);
                    if v___x_119_ == 0 {
                        v___x_120_ = 1usize;
                        v___x_121_ = lean_usize_add(v_i_115_, v___x_120_);
                        v_i_115_ = v___x_121_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_119_;
                    }
                } else {
                    v___x_123_ = 0;
                    return v___x_123_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0___boxed(
    mut v_a_124_: *mut leanh::LeanObject,
    mut v_as_125_: *mut leanh::LeanObject,
    mut v_i_126_: *mut leanh::LeanObject,
    mut v_stop_127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_128_: usize = 0;
    let mut v_stop_boxed_129_: usize = 0;
    let mut v_res_130_: u8 = 0;
    let mut v_r_131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_128_ = leanh::lean_unbox_usize(v_i_126_);
    leanh::lean_dec(v_i_126_);
    v_stop_boxed_129_ = leanh::lean_unbox_usize(v_stop_127_);
    leanh::lean_dec(v_stop_127_);
    v_res_130_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(v_a_124_, v_as_125_, v_i_boxed_128_, v_stop_boxed_129_);
    leanh::lean_dec_ref(v_as_125_);
    leanh::lean_dec(v_a_124_);
    v_r_131_ = leanh::lean_box((v_res_130_) as usize);
    return v_r_131_;
}
pub unsafe fn l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(
    mut v_as_132_: *mut leanh::LeanObject,
    mut v_a_133_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_136_: u8 = 0;
    v___x_134_ = leanh::lean_unsigned_to_nat(0);
    v___x_135_ = lean_array_get_size(v_as_132_);
    v___x_136_ = lean_nat_dec_lt(v___x_134_, v___x_135_);
    if v___x_136_ == 0 {
        return v___x_136_;
    } else {
        if v___x_136_ == 0 {
            return v___x_136_;
        } else {
            let mut v___x_137_: usize = 0;
            let mut v___x_138_: usize = 0;
            let mut v___x_139_: u8 = 0;
            v___x_137_ = 0usize;
            v___x_138_ = lean_usize_of_nat(v___x_135_);
            v___x_139_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00Lean_registerInternalExceptionId_spec__0_spec__0(v_a_133_, v_as_132_, v___x_137_, v___x_138_);
            return v___x_139_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0___boxed(
    mut v_as_140_: *mut leanh::LeanObject,
    mut v_a_141_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_142_: u8 = 0;
    let mut v_r_143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_142_ =
        l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(v_as_140_, v_a_141_);
    leanh::lean_dec(v_a_141_);
    leanh::lean_dec_ref(v_as_140_);
    v_r_143_ = leanh::lean_box((v_res_142_) as usize);
    return v_r_143_;
}
pub unsafe fn l_Lean_registerInternalExceptionId(
    mut v_name_146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_150_: u8 = 0;
    v___x_148_ = l_Lean_internalExceptionsRef;
    v___x_149_ = lean_st_ref_get(v___x_148_);
    v___x_150_ =
        l_Array_contains___at___00Lean_registerInternalExceptionId_spec__0(v___x_149_, v_name_146_);
    if v___x_150_ == 0 {
        let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_152_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_154_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_155_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_151_ = lean_st_ref_take(v___x_148_);
        v___x_152_ = lean_array_push(v___x_151_, v_name_146_);
        v___x_153_ = lean_st_ref_set(v___x_148_, v___x_152_);
        v___x_154_ = lean_array_get_size(v___x_149_);
        leanh::lean_dec(v___x_149_);
        v___x_155_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_155_, 0, v___x_154_);
        return v___x_155_;
    } else {
        let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_160_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_149_);
        v___x_156_ = l_Lean_registerInternalExceptionId___closed__0;
        v___x_157_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
            v_name_146_,
            v___x_150_,
        );
        v___x_158_ = lean_string_append(v___x_156_, v___x_157_);
        leanh::lean_dec_ref(v___x_157_);
        v___x_159_ = l_Lean_registerInternalExceptionId___closed__1;
        v___x_160_ = lean_string_append(v___x_158_, v___x_159_);
        v___x_161_ = lean_mk_io_user_error(v___x_160_);
        v___x_162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_162_, 0, v___x_161_);
        return v___x_162_;
    }
}
pub unsafe fn l_Lean_registerInternalExceptionId___boxed(
    mut v_name_163_: *mut leanh::LeanObject,
    mut v_a_164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_165_ = l_Lean_registerInternalExceptionId(v_name_163_);
    return v_res_165_;
}
pub unsafe fn l_Lean_InternalExceptionId_toString(
    mut v_id_167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_168_ = l_Lean_InternalExceptionId_toString___closed__0;
    v___x_169_ = l_Nat_reprFast(v_id_167_);
    v___x_170_ = lean_string_append(v___x_168_, v___x_169_);
    leanh::lean_dec_ref(v___x_169_);
    return v___x_170_;
}
pub unsafe fn _init_l_Lean_InternalExceptionId_getName___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_172_ = l_Lean_InternalExceptionId_getName___closed__0;
    v___x_173_ = lean_mk_io_user_error(v___x_172_);
    return v___x_173_;
}
pub unsafe fn l_Lean_InternalExceptionId_getName(
    mut v_id_174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: u8 = 0;
    v___x_176_ = l_Lean_internalExceptionsRef;
    v___x_177_ = lean_st_ref_get(v___x_176_);
    v___x_178_ = lean_array_get_size(v___x_177_);
    v___x_179_ = lean_nat_dec_lt(v_id_174_, v___x_178_);
    if v___x_179_ == 0 {
        let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_181_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_177_);
        v___x_180_ = leanh::lean_obj_once(
            core::ptr::addr_of_mut!(l_Lean_InternalExceptionId_getName___closed__1),
            core::ptr::addr_of_mut!(l_Lean_InternalExceptionId_getName___closed__1_once),
            _init_l_Lean_InternalExceptionId_getName___closed__1,
        );
        v___x_181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_181_, 0, v___x_180_);
        return v___x_181_;
    } else {
        let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_182_ = lean_array_fget(v___x_177_, v_id_174_);
        leanh::lean_dec(v___x_177_);
        v___x_183_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_183_, 0, v___x_182_);
        return v___x_183_;
    }
}
pub unsafe fn l_Lean_InternalExceptionId_getName___boxed(
    mut v_id_184_: *mut leanh::LeanObject,
    mut v_a_185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_186_ = l_Lean_InternalExceptionId_getName(v_id_184_);
    leanh::lean_dec(v_id_184_);
    return v_res_186_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_InternalExceptionId(
    builtin: u8,
) -> *mut leanh::LeanObject {
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
    res = runtime_initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_instInhabitedInternalExceptionId_default =
        _init_l_Lean_instInhabitedInternalExceptionId_default();
    leanh::lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId_default);
    l_Lean_instInhabitedInternalExceptionId = _init_l_Lean_instInhabitedInternalExceptionId();
    leanh::lean_mark_persistent(l_Lean_instInhabitedInternalExceptionId);
    res = l___private_Lean_InternalExceptionId_0__Lean_initFn_00___x40_Lean_InternalExceptionId_3474817028____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_internalExceptionsRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_internalExceptionsRef);
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_InternalExceptionId(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_InternalExceptionId(builtin: u8) -> *mut leanh::LeanObject {
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
    res = initialize_Init_Data_ToString_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_ToString_Macro(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_InternalExceptionId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_InternalExceptionId(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_InternalExceptionId(builtin);
}
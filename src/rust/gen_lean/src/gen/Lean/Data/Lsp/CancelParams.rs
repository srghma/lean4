// Lean compiler output
// Module: Lean.Data.Lsp.CancelParams
// Imports: Lean.Data.JsonRpc
use crate::ffi::{lean_array_to_list, lean_string_append};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getObjValD, l_Lean_Json_mkObj};
use crate::r#gen::Lean::Data::JsonRpc::{
    initialize_Lean_Data_JsonRpc, l_Lean_JsonRpc_instBEqRequestID_beq,
    l_Lean_JsonRpc_instInhabitedRequestID_default, runtime_initialize_Lean_Data_JsonRpc,
};
pub static mut l_Lean_Lsp_instInhabitedCancelParams_default: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Lsp_instInhabitedCancelParams: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instBEqCancelParams___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instBEqCancelParams_beq___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instBEqCancelParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instBEqCancelParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instBEqCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [105, 100, 0],
};
static mut l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instToJsonCancelParams___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Lsp_instToJsonCancelParams_toJson as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Lsp_instToJsonCancelParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instToJsonCancelParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instToJsonCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [97, 32, 114, 101, 113, 117, 101, 115, 116, 32, 105, 100, 32, 110, 101, 101, 100, 115, 32, 116, 111, 32, 98, 101, 32, 97, 32, 110, 117, 109, 98, 101, 114, 32, 111, 114, 32, 97, 32, 115, 116, 114, 105, 110, 103, 0]};
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__0_value) as *mut leanh::LeanObject] };
static mut l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [76, 115, 112, 0],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [67, 97, 110, 99, 101, 108, 80, 97, 114, 97, 109, 115, 0],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__0_value)
            as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__1_value)
            as *mut leanh::LeanObject,
        6773744487318448338 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__2_value)
            as *mut leanh::LeanObject,
        16807982367663498804 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
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
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0_value)
            as *mut leanh::LeanObject,
        6041859491766292191 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10_value:
    leanh::LeanStringObject<3> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [58, 32, 0],
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Lsp_instFromJsonCancelParams___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Lsp_instFromJsonCancelParams_fromJson as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Lsp_instFromJsonCancelParams___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Lsp_instFromJsonCancelParams: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Lsp_instFromJsonCancelParams___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn _init_l_Lean_Lsp_instInhabitedCancelParams_default() -> *mut leanh::LeanObject
{
    let mut v___x_137_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_137_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
    return v___x_137_;
}
pub unsafe fn _init_l_Lean_Lsp_instInhabitedCancelParams() -> *mut leanh::LeanObject {
    let mut v___x_138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_138_ = l_Lean_JsonRpc_instInhabitedRequestID_default;
    return v___x_138_;
}
pub unsafe fn l_Lean_Lsp_instBEqCancelParams_beq(
    mut v_x_139_: *mut leanh::LeanObject,
    mut v_x_140_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_141_: u8 = 0;
    v___x_141_ = l_Lean_JsonRpc_instBEqRequestID_beq(v_x_139_, v_x_140_);
    return v___x_141_;
}
pub unsafe fn l_Lean_Lsp_instBEqCancelParams_beq___boxed(
    mut v_x_142_: *mut leanh::LeanObject,
    mut v_x_143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_144_: u8 = 0;
    let mut v_r_145_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_144_ = l_Lean_Lsp_instBEqCancelParams_beq(v_x_142_, v_x_143_);
    leanh::lean_dec(v_x_143_);
    leanh::lean_dec(v_x_142_);
    v_r_145_ = leanh::lean_box((v_res_144_) as usize);
    return v_r_145_;
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(
    mut v_a_148_: *mut leanh::LeanObject,
    mut v_a_149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_148_) == 0 {
                    v___x_150_ = lean_array_to_list(v_a_149_);
                    return v___x_150_;
                } else {
                    v_head_151_ = leanh::lean_ctor_get(v_a_148_, 0);
                    leanh::lean_inc(v_head_151_);
                    v_tail_152_ = leanh::lean_ctor_get(v_a_148_, 1);
                    leanh::lean_inc(v_tail_152_);
                    leanh::lean_dec_ref_known(v_a_148_, 2);
                    v___x_153_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_149_,
                        v_head_151_,
                    );
                    v_a_148_ = v_tail_152_;
                    v_a_149_ = v___x_153_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Lsp_instToJsonCancelParams_toJson(
    mut v_x_158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_172_: u8 = 0;
    let mut v___x_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_176_: u8 = 0;
    let mut v_n_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_180_: u8 = 0;
    let mut v___x_182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_184_: u8 = 0;
    let mut v___x_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_159_ = l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0;
                match leanh::lean_obj_tag(v_x_158_) {
                    0 => {
                        v_s_169_ = leanh::lean_ctor_get(v_x_158_, 0);
                        v_isSharedCheck_176_ = (!leanh::lean_is_exclusive(v_x_158_)) as u8;
                        if v_isSharedCheck_176_ == 0 {
                            v___x_171_ = v_x_158_;
                            v_isShared_172_ = v_isSharedCheck_176_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_169_);
                            leanh::lean_dec(v_x_158_);
                            v___x_171_ = leanh::lean_box(0);
                            v_isShared_172_ = v_isSharedCheck_176_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        v_n_177_ = leanh::lean_ctor_get(v_x_158_, 0);
                        v_isSharedCheck_184_ = (!leanh::lean_is_exclusive(v_x_158_)) as u8;
                        if v_isSharedCheck_184_ == 0 {
                            v___x_179_ = v_x_158_;
                            v_isShared_180_ = v_isSharedCheck_184_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_177_);
                            leanh::lean_dec(v_x_158_);
                            v___x_179_ = leanh::lean_box(0);
                            v_isShared_180_ = v_isSharedCheck_184_;
                            state = 4;
                            continue;
                        }
                    }
                    _ => {
                        v___x_185_ = leanh::lean_box(0);
                        v___y_161_ = v___x_185_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_162_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_162_, 0, v___x_159_);
                leanh::lean_ctor_set(v___x_162_, 1, v___y_161_);
                v___x_163_ = leanh::lean_box(0);
                v___x_164_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_164_, 0, v___x_162_);
                leanh::lean_ctor_set(v___x_164_, 1, v___x_163_);
                v___x_165_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_165_, 0, v___x_164_);
                leanh::lean_ctor_set(v___x_165_, 1, v___x_163_);
                v___x_166_ = l_Lean_Lsp_instToJsonCancelParams_toJson___closed__1;
                v___x_167_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Lsp_instToJsonCancelParams_toJson_spec__0(v___x_165_, v___x_166_);
                v___x_168_ = l_Lean_Json_mkObj(v___x_167_);
                leanh::lean_dec(v___x_167_);
                return v___x_168_;
            }
            2 => {
                if v_isShared_172_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_171_, 3);
                    v___x_174_ = v___x_171_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_175_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_175_, 0, v_s_169_);
                    v___x_174_ = v_reuseFailAlloc_175_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___y_161_ = v___x_174_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_180_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_179_, 2);
                    v___x_182_ = v___x_179_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_183_ = leanh::lean_alloc_ctor(2, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_183_, 0, v_n_177_);
                    v___x_182_ = v_reuseFailAlloc_183_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___y_161_ = v___x_182_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(
    mut v_j_191_: *mut leanh::LeanObject,
    mut v_k_192_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_s_194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_197_: u8 = 0;
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_202_: u8 = 0;
    let mut v_n_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_206_: u8 = 0;
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_211_: u8 = 0;
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_193_ = l_Lean_Json_getObjValD(v_j_191_, v_k_192_);
                match leanh::lean_obj_tag(v___x_193_) {
                    3 => {
                        v_s_194_ = leanh::lean_ctor_get(v___x_193_, 0);
                        v_isSharedCheck_202_ = (!leanh::lean_is_exclusive(v___x_193_)) as u8;
                        if v_isSharedCheck_202_ == 0 {
                            v___x_196_ = v___x_193_;
                            v_isShared_197_ = v_isSharedCheck_202_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_s_194_);
                            leanh::lean_dec(v___x_193_);
                            v___x_196_ = leanh::lean_box(0);
                            v_isShared_197_ = v_isSharedCheck_202_;
                            state = 1;
                            continue;
                        }
                    }
                    2 => {
                        v_n_203_ = leanh::lean_ctor_get(v___x_193_, 0);
                        v_isSharedCheck_211_ = (!leanh::lean_is_exclusive(v___x_193_)) as u8;
                        if v_isSharedCheck_211_ == 0 {
                            v___x_205_ = v___x_193_;
                            v_isShared_206_ = v_isSharedCheck_211_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_n_203_);
                            leanh::lean_dec(v___x_193_);
                            v___x_205_ = leanh::lean_box(0);
                            v_isShared_206_ = v_isSharedCheck_211_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        leanh::lean_dec(v___x_193_);
                        v___x_212_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___closed__1;
                        return v___x_212_;
                    }
                }
            }
            1 => {
                if v_isShared_197_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_196_, 0);
                    v___x_199_ = v___x_196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_201_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_201_, 0, v_s_194_);
                    v___x_199_ = v_reuseFailAlloc_201_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_200_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_200_, 0, v___x_199_);
                return v___x_200_;
            }
            3 => {
                if v_isShared_206_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_205_, 1);
                    v___x_208_ = v___x_205_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_210_, 0, v_n_203_);
                    v___x_208_ = v_reuseFailAlloc_210_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_209_, 0, v___x_208_);
                return v___x_209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0___boxed(
    mut v_j_213_: *mut leanh::LeanObject,
    mut v_k_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ =
        l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(
            v_j_213_, v_k_214_,
        );
    leanh::lean_dec_ref(v_k_214_);
    return v_res_215_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_223_: u8 = 0;
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_223_ = 1;
    v___x_224_ = l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__3;
    v___x_225_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_224_, v___x_223_);
    return v___x_225_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_229_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_227_ = l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__5;
    v___x_228_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4_once),
        _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__4,
    );
    v___x_229_ = lean_string_append(v___x_228_, v___x_227_);
    return v___x_229_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_232_: u8 = 0;
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_232_ = 1;
    v___x_233_ = l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__7;
    v___x_234_ =
        l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v___x_233_, v___x_232_);
    return v___x_234_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_235_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8_once),
        _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__8,
    );
    v___x_236_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6_once),
        _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__6,
    );
    v___x_237_ = lean_string_append(v___x_236_, v___x_235_);
    return v___x_237_;
}
pub unsafe fn _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__10;
    v___x_240_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9_once),
        _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__9,
    );
    v___x_241_ = lean_string_append(v___x_240_, v___x_239_);
    return v___x_241_;
}
pub unsafe fn l_Lean_Lsp_instFromJsonCancelParams_fromJson(
    mut v_json_242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_248_: u8 = 0;
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_254_: u8 = 0;
    let mut v_a_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_262_: u8 = 0;
    let mut v_a_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_266_: u8 = 0;
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_270_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_243_ = l_Lean_Lsp_instToJsonCancelParams_toJson___closed__0;
                v___x_244_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Lsp_instFromJsonCancelParams_fromJson_spec__0(v_json_242_, v___x_243_);
                if leanh::lean_obj_tag(v___x_244_) == 0 {
                    v_a_245_ = leanh::lean_ctor_get(v___x_244_, 0);
                    v_isSharedCheck_254_ = (!leanh::lean_is_exclusive(v___x_244_)) as u8;
                    if v_isSharedCheck_254_ == 0 {
                        v___x_247_ = v___x_244_;
                        v_isShared_248_ = v_isSharedCheck_254_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_245_);
                        leanh::lean_dec(v___x_244_);
                        v___x_247_ = leanh::lean_box(0);
                        v_isShared_248_ = v_isSharedCheck_254_;
                        state = 1;
                        continue;
                    }
                } else {
                    if leanh::lean_obj_tag(v___x_244_) == 0 {
                        v_a_255_ = leanh::lean_ctor_get(v___x_244_, 0);
                        v_isSharedCheck_262_ = (!leanh::lean_is_exclusive(v___x_244_)) as u8;
                        if v_isSharedCheck_262_ == 0 {
                            v___x_257_ = v___x_244_;
                            v_isShared_258_ = v_isSharedCheck_262_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_255_);
                            leanh::lean_dec(v___x_244_);
                            v___x_257_ = leanh::lean_box(0);
                            v_isShared_258_ = v_isSharedCheck_262_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_263_ = leanh::lean_ctor_get(v___x_244_, 0);
                        v_isSharedCheck_270_ = (!leanh::lean_is_exclusive(v___x_244_)) as u8;
                        if v_isSharedCheck_270_ == 0 {
                            v___x_265_ = v___x_244_;
                            v_isShared_266_ = v_isSharedCheck_270_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_263_);
                            leanh::lean_dec(v___x_244_);
                            v___x_265_ = leanh::lean_box(0);
                            v_isShared_266_ = v_isSharedCheck_270_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_249_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11_once
                    ),
                    _init_l_Lean_Lsp_instFromJsonCancelParams_fromJson___closed__11,
                );
                v___x_250_ = lean_string_append(v___x_249_, v_a_245_);
                leanh::lean_dec(v_a_245_);
                if v_isShared_248_ == 0 {
                    leanh::lean_ctor_set(v___x_247_, 0, v___x_250_);
                    v___x_252_ = v___x_247_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_253_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_250_);
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
                    leanh::lean_ctor_set_tag(v___x_257_, 0);
                    v___x_260_ = v___x_257_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
                    v___x_260_ = v_reuseFailAlloc_261_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_260_;
            }
            5 => {
                if v_isShared_266_ == 0 {
                    v___x_268_ = v___x_265_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_269_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_269_, 0, v_a_263_);
                    v___x_268_ = v_reuseFailAlloc_269_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_268_;
            }
            _ => {}
        }
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Lsp_CancelParams(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_JsonRpc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Lsp_instInhabitedCancelParams_default =
        _init_l_Lean_Lsp_instInhabitedCancelParams_default();
    leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedCancelParams_default);
    l_Lean_Lsp_instInhabitedCancelParams = _init_l_Lean_Lsp_instInhabitedCancelParams();
    leanh::lean_mark_persistent(l_Lean_Lsp_instInhabitedCancelParams);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Lsp_CancelParams(
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
pub unsafe fn initialize_Lean_Data_Lsp_CancelParams(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_JsonRpc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Lsp_CancelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Lsp_CancelParams(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Lsp_CancelParams(builtin);
}
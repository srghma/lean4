// Lean compiler output
// Module: Lean.Widget.Types
// Imports: Lean.Server.Rpc.Basic
use crate::ffi::{lean_array_to_list, lean_uint64_to_nat};
use crate::r#gen::Init::Data::Array::Basic::l_List_foldl___at___00Array_appendList_spec__0___redArg;
use crate::r#gen::Init::Data::ToString::Name::l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0;
use crate::r#gen::Lean::Data::Json::Basic::{l_Lean_Json_getObjValD, l_Lean_Json_mkObj};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_Name_fromJson_x3f, l_Lean_bignumToJson, l_UInt64_fromJson_x3f,
};
use crate::r#gen::Lean::Server::Rpc::Basic::{
    initialize_Lean_Server_Rpc_Basic, runtime_initialize_Lean_Server_Rpc_Basic,
};
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [105, 100, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [106, 97, 118, 97, 115, 99, 114, 105, 112, 116, 72, 97, 115, 104, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [112, 114, 111, 112, 115, 0]};
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instFromJsonRpcEncodablePacket_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instFromJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__value) as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instToJsonRpcEncodablePacket_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Widget_instToJsonRpcEncodablePacket___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__value) as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableWidgetInstance___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableWidgetInstance___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableWidgetInstance___closed__1_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Widget_instRpcEncodableWidgetInstance___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Widget_instRpcEncodableWidgetInstance___closed__2_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Widget_instRpcEncodableWidgetInstance___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Widget_instRpcEncodableWidgetInstance: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Widget_instRpcEncodableWidgetInstance___closed__2_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0(
    mut v_j_155_: *mut leanh::LeanObject,
    mut v_k_156_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_157_ = l_Lean_Json_getObjValD(v_j_155_, v_k_156_);
    v___x_158_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_158_, 0, v___x_157_);
    return v___x_158_;
}
pub unsafe fn l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0___boxed(
    mut v_j_159_: *mut leanh::LeanObject,
    mut v_k_160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_161_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_161_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0(v_j_159_, v_k_160_);
    leanh::lean_dec_ref(v_k_160_);
    return v_res_161_;
}
pub unsafe fn l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_(
    mut v_json_165_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_177_: u8 = 0;
    let mut v___x_178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_182_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_166_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
                leanh::lean_inc_n(v_json_165_, 2);
                v___x_167_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0(v_json_165_, v___x_166_);
                v_a_168_ = leanh::lean_ctor_get(v___x_167_, 0);
                leanh::lean_inc(v_a_168_);
                leanh::lean_dec_ref(v___x_167_);
                v___x_169_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
                v___x_170_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0(v_json_165_, v___x_169_);
                v_a_171_ = leanh::lean_ctor_get(v___x_170_, 0);
                leanh::lean_inc(v_a_171_);
                leanh::lean_dec_ref(v___x_170_);
                v___x_172_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
                v___x_173_ = l_Lean_Json_getObjValAs_x3f___at___00Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14__spec__0(v_json_165_, v___x_172_);
                v_a_174_ = leanh::lean_ctor_get(v___x_173_, 0);
                v_isSharedCheck_182_ = (!leanh::lean_is_exclusive(v___x_173_)) as u8;
                if v_isSharedCheck_182_ == 0 {
                    v___x_176_ = v___x_173_;
                    v_isShared_177_ = v_isSharedCheck_182_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_174_);
                    leanh::lean_dec(v___x_173_);
                    v___x_176_ = leanh::lean_box(0);
                    v_isShared_177_ = v_isSharedCheck_182_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_178_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_178_, 0, v_a_168_);
                leanh::lean_ctor_set(v___x_178_, 1, v_a_171_);
                leanh::lean_ctor_set(v___x_178_, 2, v_a_174_);
                if v_isShared_177_ == 0 {
                    leanh::lean_ctor_set(v___x_176_, 0, v___x_178_);
                    v___x_180_ = v___x_176_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_181_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_181_, 0, v___x_178_);
                    v___x_180_ = v_reuseFailAlloc_181_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__spec__0(
    mut v_a_185_: *mut leanh::LeanObject,
    mut v_a_186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_185_) == 0 {
                    v___x_187_ = lean_array_to_list(v_a_186_);
                    return v___x_187_;
                } else {
                    v_head_188_ = leanh::lean_ctor_get(v_a_185_, 0);
                    leanh::lean_inc(v_head_188_);
                    v_tail_189_ = leanh::lean_ctor_get(v_a_185_, 1);
                    leanh::lean_inc(v_tail_189_);
                    leanh::lean_dec_ref_known(v_a_185_, 2);
                    v___x_190_ = l_List_foldl___at___00Array_appendList_spec__0___redArg(
                        v_a_186_,
                        v_head_188_,
                    );
                    v_a_185_ = v_tail_189_;
                    v_a_186_ = v___x_190_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_(
    mut v_x_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_props_197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_id_195_ = leanh::lean_ctor_get(v_x_194_, 0);
    v_javascriptHash_196_ = leanh::lean_ctor_get(v_x_194_, 1);
    v_props_197_ = leanh::lean_ctor_get(v_x_194_, 2);
    v___x_198_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
    leanh::lean_inc(v_id_195_);
    v___x_199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_199_, 0, v___x_198_);
    leanh::lean_ctor_set(v___x_199_, 1, v_id_195_);
    v___x_200_ = leanh::lean_box(0);
    v___x_201_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_201_, 0, v___x_199_);
    leanh::lean_ctor_set(v___x_201_, 1, v___x_200_);
    v___x_202_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__1_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
    leanh::lean_inc(v_javascriptHash_196_);
    v___x_203_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_203_, 0, v___x_202_);
    leanh::lean_ctor_set(v___x_203_, 1, v_javascriptHash_196_);
    v___x_204_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_204_, 0, v___x_203_);
    leanh::lean_ctor_set(v___x_204_, 1, v___x_200_);
    v___x_205_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson___closed__2_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_;
    leanh::lean_inc(v_props_197_);
    v___x_206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_206_, 0, v___x_205_);
    leanh::lean_ctor_set(v___x_206_, 1, v_props_197_);
    v___x_207_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_207_, 0, v___x_206_);
    leanh::lean_ctor_set(v___x_207_, 1, v___x_200_);
    v___x_208_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_208_, 0, v___x_207_);
    leanh::lean_ctor_set(v___x_208_, 1, v___x_200_);
    v___x_209_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_209_, 0, v___x_204_);
    leanh::lean_ctor_set(v___x_209_, 1, v___x_208_);
    v___x_210_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_210_, 0, v___x_201_);
    leanh::lean_ctor_set(v___x_210_, 1, v___x_209_);
    v___x_211_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson___closed__0_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_;
    v___x_212_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go___at___00Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32__spec__0(v___x_210_, v___x_211_);
    v___x_213_ = l_Lean_Json_mkObj(v___x_212_);
    leanh::lean_dec(v___x_212_);
    return v___x_213_;
}
pub unsafe fn l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32____boxed(
    mut v_x_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_(v_x_214_);
    leanh::lean_dec_ref(v_x_214_);
    return v_res_215_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableWidgetInstance_enc_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(
    mut v_a_218_: *mut leanh::LeanObject,
    mut v_a_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_id_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_221_: u64 = 0;
    let mut v_props_222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_228_: u8 = 0;
    let mut v___x_229_: u8 = 0;
    let mut v___x_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_239_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_id_220_ = leanh::lean_ctor_get(v_a_218_, 0);
                leanh::lean_inc(v_id_220_);
                v_javascriptHash_221_ = leanh::lean_ctor_get_uint64(
                    v_a_218_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                );
                v_props_222_ = leanh::lean_ctor_get(v_a_218_, 1);
                leanh::lean_inc_ref(v_props_222_);
                leanh::lean_dec_ref(v_a_218_);
                v___x_223_ = leanh::lean_apply_1(v_props_222_, v_a_219_);
                v_fst_224_ = leanh::lean_ctor_get(v___x_223_, 0);
                v_snd_225_ = leanh::lean_ctor_get(v___x_223_, 1);
                v_isSharedCheck_239_ = (!leanh::lean_is_exclusive(v___x_223_)) as u8;
                if v_isSharedCheck_239_ == 0 {
                    v___x_227_ = v___x_223_;
                    v_isShared_228_ = v_isSharedCheck_239_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_225_);
                    leanh::lean_inc(v_fst_224_);
                    leanh::lean_dec(v___x_223_);
                    v___x_227_ = leanh::lean_box(0);
                    v_isShared_228_ = v_isSharedCheck_239_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_229_ = 1;
                v___x_230_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v_id_220_, v___x_229_,
                );
                v___x_231_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_231_, 0, v___x_230_);
                v___x_232_ = lean_uint64_to_nat(v_javascriptHash_221_);
                v___x_233_ = l_Lean_bignumToJson(v___x_232_);
                v___x_234_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_234_, 0, v___x_231_);
                leanh::lean_ctor_set(v___x_234_, 1, v___x_233_);
                leanh::lean_ctor_set(v___x_234_, 2, v_fst_224_);
                v___x_235_ = l_Lean_Widget_instToJsonRpcEncodablePacket_toJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_32_(v___x_234_);
                leanh::lean_dec_ref_known(v___x_234_, 3);
                if v_isShared_228_ == 0 {
                    leanh::lean_ctor_set(v___x_227_, 0, v___x_235_);
                    v___x_237_ = v___x_227_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_238_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_235_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_238_, 1, v_snd_225_);
                    v___x_237_ = v_reuseFailAlloc_238_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_237_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0___redArg(
    mut v_x_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_240_);
    return v_x_240_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0___redArg___boxed(
    mut v_x_241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_242_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0___redArg(v_x_241_);
    leanh::lean_dec_ref(v_x_241_);
    return v_res_242_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0(
    mut v_00_u03b1_243_: *mut leanh::LeanObject,
    mut v_x_244_: *mut leanh::LeanObject,
    mut v___y_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_x_244_);
    return v_x_244_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0___boxed(
    mut v_00_u03b1_246_: *mut leanh::LeanObject,
    mut v_x_247_: *mut leanh::LeanObject,
    mut v___y_248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_249_ = l_MonadExcept_ofExcept___at___00Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1__spec__0(v_00_u03b1_246_, v_x_247_, v___y_248_);
    leanh::lean_dec_ref(v___y_248_);
    leanh::lean_dec_ref(v_x_247_);
    return v_res_249_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(
    mut v_props_250_: *mut leanh::LeanObject,
    mut v___y_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_252_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_252_, 0, v_props_250_);
    leanh::lean_ctor_set(v___x_252_, 1, v___y_251_);
    return v___x_252_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(
    mut v_j_253_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_258_: u8 = 0;
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_262_: u8 = 0;
    let mut v_a_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_javascriptHash_265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_props_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_271_: u8 = 0;
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_275_: u8 = 0;
    let mut v_a_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_281_: u8 = 0;
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_285_: u8 = 0;
    let mut v_a_286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_289_: u8 = 0;
    let mut v___f_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: u64 = 0;
    let mut v___x_294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_296_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_254_ = l_Lean_Widget_instFromJsonRpcEncodablePacket_fromJson_00___x40_Lean_Widget_Types_3328362917____hygCtx___hyg_14_(v_j_253_);
                if leanh::lean_obj_tag(v___x_254_) == 0 {
                    v_a_255_ = leanh::lean_ctor_get(v___x_254_, 0);
                    v_isSharedCheck_262_ = (!leanh::lean_is_exclusive(v___x_254_)) as u8;
                    if v_isSharedCheck_262_ == 0 {
                        v___x_257_ = v___x_254_;
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_255_);
                        leanh::lean_dec(v___x_254_);
                        v___x_257_ = leanh::lean_box(0);
                        v_isShared_258_ = v_isSharedCheck_262_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_263_ = leanh::lean_ctor_get(v___x_254_, 0);
                    leanh::lean_inc(v_a_263_);
                    leanh::lean_dec_ref_known(v___x_254_, 1);
                    v_id_264_ = leanh::lean_ctor_get(v_a_263_, 0);
                    leanh::lean_inc(v_id_264_);
                    v_javascriptHash_265_ = leanh::lean_ctor_get(v_a_263_, 1);
                    leanh::lean_inc(v_javascriptHash_265_);
                    v_props_266_ = leanh::lean_ctor_get(v_a_263_, 2);
                    leanh::lean_inc(v_props_266_);
                    leanh::lean_dec(v_a_263_);
                    v___x_267_ = l_Lean_Name_fromJson_x3f(v_id_264_);
                    if leanh::lean_obj_tag(v___x_267_) == 0 {
                        leanh::lean_dec(v_props_266_);
                        leanh::lean_dec(v_javascriptHash_265_);
                        v_a_268_ = leanh::lean_ctor_get(v___x_267_, 0);
                        v_isSharedCheck_275_ = (!leanh::lean_is_exclusive(v___x_267_)) as u8;
                        if v_isSharedCheck_275_ == 0 {
                            v___x_270_ = v___x_267_;
                            v_isShared_271_ = v_isSharedCheck_275_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_268_);
                            leanh::lean_dec(v___x_267_);
                            v___x_270_ = leanh::lean_box(0);
                            v_isShared_271_ = v_isSharedCheck_275_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_276_ = leanh::lean_ctor_get(v___x_267_, 0);
                        leanh::lean_inc(v_a_276_);
                        leanh::lean_dec_ref_known(v___x_267_, 1);
                        v___x_277_ = l_UInt64_fromJson_x3f(v_javascriptHash_265_);
                        if leanh::lean_obj_tag(v___x_277_) == 0 {
                            leanh::lean_dec(v_a_276_);
                            leanh::lean_dec(v_props_266_);
                            v_a_278_ = leanh::lean_ctor_get(v___x_277_, 0);
                            v_isSharedCheck_285_ =
                                (!leanh::lean_is_exclusive(v___x_277_)) as u8;
                            if v_isSharedCheck_285_ == 0 {
                                v___x_280_ = v___x_277_;
                                v_isShared_281_ = v_isSharedCheck_285_;
                                state = 5;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_278_);
                                leanh::lean_dec(v___x_277_);
                                v___x_280_ = leanh::lean_box(0);
                                v_isShared_281_ = v_isSharedCheck_285_;
                                state = 5;
                                continue;
                            }
                        } else {
                            v_a_286_ = leanh::lean_ctor_get(v___x_277_, 0);
                            v_isSharedCheck_296_ =
                                (!leanh::lean_is_exclusive(v___x_277_)) as u8;
                            if v_isSharedCheck_296_ == 0 {
                                v___x_288_ = v___x_277_;
                                v_isShared_289_ = v_isSharedCheck_296_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_286_);
                                leanh::lean_dec(v___x_277_);
                                v___x_288_ = leanh::lean_box(0);
                                v_isShared_289_ = v_isSharedCheck_296_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if v_isShared_258_ == 0 {
                    v___x_260_ = v___x_257_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_261_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_261_, 0, v_a_255_);
                    v___x_260_ = v_reuseFailAlloc_261_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_260_;
            }
            3 => {
                if v_isShared_271_ == 0 {
                    v___x_273_ = v___x_270_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_274_, 0, v_a_268_);
                    v___x_273_ = v_reuseFailAlloc_274_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_273_;
            }
            5 => {
                if v_isShared_281_ == 0 {
                    v___x_283_ = v___x_280_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_284_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_284_, 0, v_a_278_);
                    v___x_283_ = v_reuseFailAlloc_284_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_283_;
            }
            7 => {
                v___f_290_ = leanh::lean_alloc_closure(l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg___lam__0_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_ as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_290_, 0, v_props_266_);
                v___x_291_ = leanh::lean_alloc_ctor(0, 2, (8) as u32);
                leanh::lean_ctor_set(v___x_291_, 0, v_a_276_);
                leanh::lean_ctor_set(v___x_291_, 1, v___f_290_);
                v___x_292_ = leanh::lean_unbox_uint64(v_a_286_);
                leanh::lean_dec(v_a_286_);
                leanh::lean_ctor_set_uint64(
                    v___x_291_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v___x_292_,
                );
                if v_isShared_289_ == 0 {
                    leanh::lean_ctor_set(v___x_288_, 0, v___x_291_);
                    v___x_294_ = v___x_288_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_295_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
                    v___x_294_ = v_reuseFailAlloc_295_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_294_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(
    mut v_j_297_: *mut leanh::LeanObject,
    mut v_a_298_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_299_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec___redArg_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_j_297_);
    return v___x_299_;
}
pub unsafe fn l_Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1____boxed(
    mut v_j_300_: *mut leanh::LeanObject,
    mut v_a_301_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_302_ = l_Lean_Widget_instRpcEncodableWidgetInstance_dec_00___x40_Lean_Widget_Types_2243429567____hygCtx___hyg_1_(v_j_300_, v_a_301_);
    leanh::lean_dec_ref(v_a_301_);
    return v_res_302_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Widget_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Server_Rpc_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Widget_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Widget_Types(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Server_Rpc_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Widget_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Widget_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Widget_Types(builtin);
}
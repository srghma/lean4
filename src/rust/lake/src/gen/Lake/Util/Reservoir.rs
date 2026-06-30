// Lean compiler output
// Module: Lake.Util.Reservoir
// Imports: Lake.Util.JsonObject
use crate::ffi::lean_string_append;
use crate::r#gen::Lake::Util::JsonObject::{
    initialize_Lake_Util_JsonObject, l_Lake_JsonObject_fromJson_x3f, l_Lake_JsonObject_getJson_x3f,
    runtime_initialize_Lake_Util_JsonObject,
};
use crate::r#gen::Lean::Data::Json::Basic::{
    l_Lean_Json_getNat_x3f, l_Lean_Json_getObj_x3f, l_Lean_Json_getStr_x3f,
};
use crate::r#gen::Lean::Data::Json::FromToJson::Basic::{
    l_Lean_instFromJsonJson___lam__0, l_Option_fromJson_x3f___redArg,
};
pub static l_Lake_Reservoir_lakeHeaders___closed__0_value: leanh::LeanStringObject<30> =
    leanh::LeanStringObject {
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
            88, 45, 82, 101, 115, 101, 114, 118, 111, 105, 114, 45, 65, 112, 105, 45, 86, 101, 114,
            115, 105, 111, 110, 58, 49, 46, 48, 46, 48, 0,
        ],
    };
static mut l_Lake_Reservoir_lakeHeaders___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Reservoir_lakeHeaders___closed__1_value: leanh::LeanStringObject<34> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 34,
        m_capacity: 34,
        m_length: 33,
        m_data: [
            88, 45, 76, 97, 107, 101, 45, 82, 101, 103, 105, 115, 116, 114, 121, 45, 65, 112, 105,
            45, 86, 101, 114, 115, 105, 111, 110, 58, 48, 46, 49, 46, 48, 0,
        ],
    };
static mut l_Lake_Reservoir_lakeHeaders___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_Reservoir_lakeHeaders___closed__2_value: leanh::LeanArrayObject<2> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 2,
        m_capacity: 2,
        m_data: [
            core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Lake_Reservoir_lakeHeaders___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Lake_Reservoir_lakeHeaders: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value:
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
    m_data: [100, 97, 116, 97, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [100, 97, 116, 97, 58, 32, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 6,
    m_capacity: 6,
    m_length: 5,
    m_data: [101, 114, 114, 111, 114, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lake_JsonObject_fromJson_x3f as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [101, 114, 114, 111, 114, 58, 32, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [115, 116, 97, 116, 117, 115, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value:
    leanh::LeanStringObject<27> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 115, 116, 97, 116, 117, 115, 0,
    ],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value:
    leanh::LeanStringObject<9> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [115, 116, 97, 116, 117, 115, 58, 32, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 101, 115, 115, 97, 103, 101, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value:
    leanh::LeanStringObject<28> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100, 58,
        32, 109, 101, 115, 115, 97, 103, 101, 0,
    ],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value)
        as *mut leanh::LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value:
    leanh::LeanStringObject<10> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [109, 101, 115, 115, 97, 103, 101, 58, 32, 0],
};
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___redArg(
    mut v_x_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_267_) == 0 {
        let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_268_ = leanh::lean_unsigned_to_nat(0);
        return v___x_268_;
    } else {
        let mut v___x_269_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_269_ = leanh::lean_unsigned_to_nat(1);
        return v___x_269_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___redArg___boxed(
    mut v_x_270_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_270_);
    leanh::lean_dec_ref(v_x_270_);
    return v_res_271_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx(
    mut v_00_u03b1_272_: *mut leanh::LeanObject,
    mut v_x_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_273_);
    return v___x_274_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___boxed(
    mut v_00_u03b1_275_: *mut leanh::LeanObject,
    mut v_x_276_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_277_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Lake_ReservoirResp_ctorIdx(v_00_u03b1_275_, v_x_276_);
    leanh::lean_dec_ref(v_x_276_);
    return v_res_277_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim___redArg(
    mut v_t_278_: *mut leanh::LeanObject,
    mut v_k_279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_278_) == 0 {
        let mut v_a_280_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_a_280_ = leanh::lean_ctor_get(v_t_278_, 0);
        leanh::lean_inc(v_a_280_);
        leanh::lean_dec_ref_known(v_t_278_, 1);
        v___x_281_ = leanh::lean_apply_1(v_k_279_, v_a_280_);
        return v___x_281_;
    } else {
        let mut v_status_282_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_message_283_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_status_282_ = leanh::lean_ctor_get(v_t_278_, 0);
        leanh::lean_inc(v_status_282_);
        v_message_283_ = leanh::lean_ctor_get(v_t_278_, 1);
        leanh::lean_inc_ref(v_message_283_);
        leanh::lean_dec_ref_known(v_t_278_, 2);
        v___x_284_ = leanh::lean_apply_2(v_k_279_, v_status_282_, v_message_283_);
        return v___x_284_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim(
    mut v_00_u03b1_285_: *mut leanh::LeanObject,
    mut v_motive_286_: *mut leanh::LeanObject,
    mut v_ctorIdx_287_: *mut leanh::LeanObject,
    mut v_t_288_: *mut leanh::LeanObject,
    mut v_h_289_: *mut leanh::LeanObject,
    mut v_k_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_291_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_288_, v_k_290_);
    return v___x_291_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim___boxed(
    mut v_00_u03b1_292_: *mut leanh::LeanObject,
    mut v_motive_293_: *mut leanh::LeanObject,
    mut v_ctorIdx_294_: *mut leanh::LeanObject,
    mut v_t_295_: *mut leanh::LeanObject,
    mut v_h_296_: *mut leanh::LeanObject,
    mut v_k_297_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Lake_ReservoirResp_ctorElim(
        v_00_u03b1_292_,
        v_motive_293_,
        v_ctorIdx_294_,
        v_t_295_,
        v_h_296_,
        v_k_297_,
    );
    leanh::lean_dec(v_ctorIdx_294_);
    return v_res_298_;
}
pub unsafe fn l_Lake_ReservoirResp_data_elim___redArg(
    mut v_t_299_: *mut leanh::LeanObject,
    mut v_data_300_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_301_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_299_, v_data_300_);
    return v___x_301_;
}
pub unsafe fn l_Lake_ReservoirResp_data_elim(
    mut v_00_u03b1_302_: *mut leanh::LeanObject,
    mut v_motive_303_: *mut leanh::LeanObject,
    mut v_t_304_: *mut leanh::LeanObject,
    mut v_h_305_: *mut leanh::LeanObject,
    mut v_data_306_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_304_, v_data_306_);
    return v___x_307_;
}
pub unsafe fn l_Lake_ReservoirResp_error_elim___redArg(
    mut v_t_308_: *mut leanh::LeanObject,
    mut v_error_309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_310_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_308_, v_error_309_);
    return v___x_310_;
}
pub unsafe fn l_Lake_ReservoirResp_error_elim(
    mut v_00_u03b1_311_: *mut leanh::LeanObject,
    mut v_motive_312_: *mut leanh::LeanObject,
    mut v_t_313_: *mut leanh::LeanObject,
    mut v_h_314_: *mut leanh::LeanObject,
    mut v_error_315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_316_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_313_, v_error_315_);
    return v___x_316_;
}
pub unsafe fn l_Lake_ReservoirResp_fromJson_x3f___redArg(
    mut v_inst_333_: *mut leanh::LeanObject,
    mut v_val_334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_340_: u8 = 0;
    let mut v___x_341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_349_: u8 = 0;
    let mut v_a_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_isSharedCheck_361_: u8 = 0;
    let mut v___x_362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_370_: u8 = 0;
    let mut v_a_371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_374_: u8 = 0;
    let mut v___x_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_379_: u8 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v___x_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_397_: u8 = 0;
    let mut v_a_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut v_a_406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_421_: u8 = 0;
    let mut v_a_422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut v_a_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_440_: u8 = 0;
    let mut v___x_441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_446_: u8 = 0;
    let mut v_a_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_454_: u8 = 0;
    let mut v_a_455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v___x_465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_470_: u8 = 0;
    let mut v_a_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut v_a_479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v___x_488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v___x_494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_a_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_val_334_);
                v___x_380_ = l_Lean_Json_getObj_x3f(v_val_334_);
                if leanh::lean_obj_tag(v___x_380_) == 1 {
                    v_a_381_ = leanh::lean_ctor_get(v___x_380_, 0);
                    leanh::lean_inc(v_a_381_);
                    leanh::lean_dec_ref_known(v___x_380_, 1);
                    v___f_382_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0;
                    v___x_407_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3;
                    v___x_408_ = l_Lake_JsonObject_getJson_x3f(v_a_381_, v___x_407_);
                    if leanh::lean_obj_tag(v___x_408_) == 0 {
                        state = 12;
                        continue;
                    } else {
                        v_val_409_ = leanh::lean_ctor_get(v___x_408_, 0);
                        leanh::lean_inc(v_val_409_);
                        leanh::lean_dec_ref_known(v___x_408_, 1);
                        v___x_410_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4;
                        v___x_411_ = l_Option_fromJson_x3f___redArg(v___x_410_, v_val_409_);
                        if leanh::lean_obj_tag(v___x_411_) == 0 {
                            leanh::lean_dec(v_a_381_);
                            leanh::lean_dec(v_val_334_);
                            leanh::lean_dec_ref(v_inst_333_);
                            v_a_412_ = leanh::lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_421_ =
                                (!leanh::lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_421_ == 0 {
                                v___x_414_ = v___x_411_;
                                v_isShared_415_ = v_isSharedCheck_421_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_412_);
                                leanh::lean_dec(v___x_411_);
                                v___x_414_ = leanh::lean_box(0);
                                v_isShared_415_ = v_isSharedCheck_421_;
                                state = 17;
                                continue;
                            }
                        } else {
                            if leanh::lean_obj_tag(v___x_411_) == 0 {
                                leanh::lean_dec(v_a_381_);
                                leanh::lean_dec(v_val_334_);
                                leanh::lean_dec_ref(v_inst_333_);
                                v_a_422_ = leanh::lean_ctor_get(v___x_411_, 0);
                                v_isSharedCheck_429_ =
                                    (!leanh::lean_is_exclusive(v___x_411_)) as u8;
                                if v_isSharedCheck_429_ == 0 {
                                    v___x_424_ = v___x_411_;
                                    v_isShared_425_ = v_isSharedCheck_429_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_422_);
                                    leanh::lean_dec(v___x_411_);
                                    v___x_424_ = leanh::lean_box(0);
                                    v_isShared_425_ = v_isSharedCheck_429_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                v_a_430_ = leanh::lean_ctor_get(v___x_411_, 0);
                                leanh::lean_inc(v_a_430_);
                                leanh::lean_dec_ref_known(v___x_411_, 1);
                                if leanh::lean_obj_tag(v_a_430_) == 1 {
                                    leanh::lean_dec(v_a_381_);
                                    leanh::lean_dec(v_val_334_);
                                    leanh::lean_dec_ref(v_inst_333_);
                                    v_val_431_ = leanh::lean_ctor_get(v_a_430_, 0);
                                    leanh::lean_inc(v_val_431_);
                                    leanh::lean_dec_ref_known(v_a_430_, 1);
                                    v___x_432_ =
                                        l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
                                    v___x_433_ =
                                        l_Lake_JsonObject_getJson_x3f(v_val_431_, v___x_432_);
                                    if leanh::lean_obj_tag(v___x_433_) == 0 {
                                        leanh::lean_dec(v_val_431_);
                                        v___x_434_ =
                                            l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8;
                                        return v___x_434_;
                                    } else {
                                        v_val_435_ = leanh::lean_ctor_get(v___x_433_, 0);
                                        leanh::lean_inc(v_val_435_);
                                        leanh::lean_dec_ref_known(v___x_433_, 1);
                                        v___x_436_ = l_Lean_Json_getNat_x3f(v_val_435_);
                                        if leanh::lean_obj_tag(v___x_436_) == 0 {
                                            leanh::lean_dec(v_val_431_);
                                            v_a_437_ = leanh::lean_ctor_get(v___x_436_, 0);
                                            v_isSharedCheck_446_ =
                                                (!leanh::lean_is_exclusive(v___x_436_))
                                                    as u8;
                                            if v_isSharedCheck_446_ == 0 {
                                                v___x_439_ = v___x_436_;
                                                v_isShared_440_ = v_isSharedCheck_446_;
                                                state = 21;
                                                continue;
                                            } else {
                                                leanh::lean_inc(v_a_437_);
                                                leanh::lean_dec(v___x_436_);
                                                v___x_439_ = leanh::lean_box(0);
                                                v_isShared_440_ = v_isSharedCheck_446_;
                                                state = 21;
                                                continue;
                                            }
                                        } else {
                                            if leanh::lean_obj_tag(v___x_436_) == 0 {
                                                leanh::lean_dec(v_val_431_);
                                                v_a_447_ =
                                                    leanh::lean_ctor_get(v___x_436_, 0);
                                                v_isSharedCheck_454_ =
                                                    (!leanh::lean_is_exclusive(v___x_436_))
                                                        as u8;
                                                if v_isSharedCheck_454_ == 0 {
                                                    v___x_449_ = v___x_436_;
                                                    v_isShared_450_ = v_isSharedCheck_454_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    leanh::lean_inc(v_a_447_);
                                                    leanh::lean_dec(v___x_436_);
                                                    v___x_449_ = leanh::lean_box(0);
                                                    v_isShared_450_ = v_isSharedCheck_454_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                v_a_455_ =
                                                    leanh::lean_ctor_get(v___x_436_, 0);
                                                leanh::lean_inc(v_a_455_);
                                                leanh::lean_dec_ref_known(v___x_436_, 1);
                                                v___x_456_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
                                                v___x_457_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_val_431_, v___x_456_,
                                                );
                                                leanh::lean_dec(v_val_431_);
                                                if leanh::lean_obj_tag(v___x_457_) == 0 {
                                                    leanh::lean_dec(v_a_455_);
                                                    v___x_458_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12;
                                                    return v___x_458_;
                                                } else {
                                                    v_val_459_ =
                                                        leanh::lean_ctor_get(v___x_457_, 0);
                                                    leanh::lean_inc(v_val_459_);
                                                    leanh::lean_dec_ref_known(v___x_457_, 1);
                                                    v___x_460_ = l_Lean_Json_getStr_x3f(v_val_459_);
                                                    if leanh::lean_obj_tag(v___x_460_) == 0 {
                                                        leanh::lean_dec(v_a_455_);
                                                        v_a_461_ = leanh::lean_ctor_get(
                                                            v___x_460_, 0,
                                                        );
                                                        v_isSharedCheck_470_ =
                                                            (!leanh::lean_is_exclusive(
                                                                v___x_460_,
                                                            ))
                                                                as u8;
                                                        if v_isSharedCheck_470_ == 0 {
                                                            v___x_463_ = v___x_460_;
                                                            v_isShared_464_ = v_isSharedCheck_470_;
                                                            state = 25;
                                                            continue;
                                                        } else {
                                                            leanh::lean_inc(v_a_461_);
                                                            leanh::lean_dec(v___x_460_);
                                                            v___x_463_ = leanh::lean_box(0);
                                                            v_isShared_464_ = v_isSharedCheck_470_;
                                                            state = 25;
                                                            continue;
                                                        }
                                                    } else {
                                                        if leanh::lean_obj_tag(v___x_460_)
                                                            == 0
                                                        {
                                                            leanh::lean_dec(v_a_455_);
                                                            v_a_471_ = leanh::lean_ctor_get(
                                                                v___x_460_, 0,
                                                            );
                                                            v_isSharedCheck_478_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_460_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_478_ == 0 {
                                                                v___x_473_ = v___x_460_;
                                                                v_isShared_474_ =
                                                                    v_isSharedCheck_478_;
                                                                state = 27;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_471_);
                                                                leanh::lean_dec(v___x_460_);
                                                                v___x_473_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_474_ =
                                                                    v_isSharedCheck_478_;
                                                                state = 27;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_479_ = leanh::lean_ctor_get(
                                                                v___x_460_, 0,
                                                            );
                                                            v_isSharedCheck_487_ =
                                                                (!leanh::lean_is_exclusive(
                                                                    v___x_460_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_487_ == 0 {
                                                                v___x_481_ = v___x_460_;
                                                                v_isShared_482_ =
                                                                    v_isSharedCheck_487_;
                                                                state = 29;
                                                                continue;
                                                            } else {
                                                                leanh::lean_inc(v_a_479_);
                                                                leanh::lean_dec(v___x_460_);
                                                                v___x_481_ =
                                                                    leanh::lean_box(0);
                                                                v_isShared_482_ =
                                                                    v_isSharedCheck_487_;
                                                                state = 29;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    leanh::lean_dec(v_a_430_);
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_380_);
                    v___x_488_ = leanh::lean_apply_1(v_inst_333_, v_val_334_);
                    if leanh::lean_obj_tag(v___x_488_) == 0 {
                        v_a_489_ = leanh::lean_ctor_get(v___x_488_, 0);
                        v_isSharedCheck_496_ = (!leanh::lean_is_exclusive(v___x_488_)) as u8;
                        if v_isSharedCheck_496_ == 0 {
                            v___x_491_ = v___x_488_;
                            v_isShared_492_ = v_isSharedCheck_496_;
                            state = 31;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_489_);
                            leanh::lean_dec(v___x_488_);
                            v___x_491_ = leanh::lean_box(0);
                            v_isShared_492_ = v_isSharedCheck_496_;
                            state = 31;
                            continue;
                        }
                    } else {
                        v_a_497_ = leanh::lean_ctor_get(v___x_488_, 0);
                        v_isSharedCheck_505_ = (!leanh::lean_is_exclusive(v___x_488_)) as u8;
                        if v_isSharedCheck_505_ == 0 {
                            v___x_499_ = v___x_488_;
                            v_isShared_500_ = v_isSharedCheck_505_;
                            state = 33;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_497_);
                            leanh::lean_dec(v___x_488_);
                            v___x_499_ = leanh::lean_box(0);
                            v_isShared_500_ = v_isSharedCheck_505_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_336_) == 1 {
                    leanh::lean_dec(v_val_334_);
                    v_val_337_ = leanh::lean_ctor_get(v_a_336_, 0);
                    v_isSharedCheck_361_ = (!leanh::lean_is_exclusive(v_a_336_)) as u8;
                    if v_isSharedCheck_361_ == 0 {
                        v___x_339_ = v_a_336_;
                        v_isShared_340_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_337_);
                        leanh::lean_dec(v_a_336_);
                        v___x_339_ = leanh::lean_box(0);
                        v_isShared_340_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_336_);
                    v___x_362_ = leanh::lean_apply_1(v_inst_333_, v_val_334_);
                    if leanh::lean_obj_tag(v___x_362_) == 0 {
                        v_a_363_ = leanh::lean_ctor_get(v___x_362_, 0);
                        v_isSharedCheck_370_ = (!leanh::lean_is_exclusive(v___x_362_)) as u8;
                        if v_isSharedCheck_370_ == 0 {
                            v___x_365_ = v___x_362_;
                            v_isShared_366_ = v_isSharedCheck_370_;
                            state = 8;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_363_);
                            leanh::lean_dec(v___x_362_);
                            v___x_365_ = leanh::lean_box(0);
                            v_isShared_366_ = v_isSharedCheck_370_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_371_ = leanh::lean_ctor_get(v___x_362_, 0);
                        v_isSharedCheck_379_ = (!leanh::lean_is_exclusive(v___x_362_)) as u8;
                        if v_isSharedCheck_379_ == 0 {
                            v___x_373_ = v___x_362_;
                            v_isShared_374_ = v_isSharedCheck_379_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_371_);
                            leanh::lean_dec(v___x_362_);
                            v___x_373_ = leanh::lean_box(0);
                            v_isShared_374_ = v_isSharedCheck_379_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_341_ = leanh::lean_apply_1(v_inst_333_, v_val_337_);
                if leanh::lean_obj_tag(v___x_341_) == 0 {
                    leanh::lean_del_object(v___x_339_);
                    v_a_342_ = leanh::lean_ctor_get(v___x_341_, 0);
                    v_isSharedCheck_349_ = (!leanh::lean_is_exclusive(v___x_341_)) as u8;
                    if v_isSharedCheck_349_ == 0 {
                        v___x_344_ = v___x_341_;
                        v_isShared_345_ = v_isSharedCheck_349_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_342_);
                        leanh::lean_dec(v___x_341_);
                        v___x_344_ = leanh::lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_349_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_350_ = leanh::lean_ctor_get(v___x_341_, 0);
                    v_isSharedCheck_360_ = (!leanh::lean_is_exclusive(v___x_341_)) as u8;
                    if v_isSharedCheck_360_ == 0 {
                        v___x_352_ = v___x_341_;
                        v_isShared_353_ = v_isSharedCheck_360_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_350_);
                        leanh::lean_dec(v___x_341_);
                        v___x_352_ = leanh::lean_box(0);
                        v_isShared_353_ = v_isSharedCheck_360_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_345_ == 0 {
                    v___x_347_ = v___x_344_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_348_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
                    v___x_347_ = v_reuseFailAlloc_348_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_347_;
            }
            5 => {
                if v_isShared_340_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_339_, 0);
                    leanh::lean_ctor_set(v___x_339_, 0, v_a_350_);
                    v___x_355_ = v___x_339_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_350_);
                    v___x_355_ = v_reuseFailAlloc_359_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_353_ == 0 {
                    leanh::lean_ctor_set(v___x_352_, 0, v___x_355_);
                    v___x_357_ = v___x_352_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
                    v___x_357_ = v_reuseFailAlloc_358_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_357_;
            }
            8 => {
                if v_isShared_366_ == 0 {
                    v___x_368_ = v___x_365_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_369_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
                    v___x_368_ = v_reuseFailAlloc_369_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_368_;
            }
            10 => {
                v___x_375_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_375_, 0, v_a_371_);
                if v_isShared_374_ == 0 {
                    leanh::lean_ctor_set(v___x_373_, 0, v___x_375_);
                    v___x_377_ = v___x_373_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
                    v___x_377_ = v_reuseFailAlloc_378_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_377_;
            }
            12 => {
                v___x_384_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1;
                v___x_385_ = l_Lake_JsonObject_getJson_x3f(v_a_381_, v___x_384_);
                leanh::lean_dec(v_a_381_);
                if leanh::lean_obj_tag(v___x_385_) == 0 {
                    v_a_336_ = v___x_385_;
                    state = 1;
                    continue;
                } else {
                    v_val_386_ = leanh::lean_ctor_get(v___x_385_, 0);
                    leanh::lean_inc(v_val_386_);
                    leanh::lean_dec_ref_known(v___x_385_, 1);
                    v___x_387_ = l_Option_fromJson_x3f___redArg(v___f_382_, v_val_386_);
                    if leanh::lean_obj_tag(v___x_387_) == 0 {
                        leanh::lean_dec(v_val_334_);
                        leanh::lean_dec_ref(v_inst_333_);
                        v_a_388_ = leanh::lean_ctor_get(v___x_387_, 0);
                        v_isSharedCheck_397_ = (!leanh::lean_is_exclusive(v___x_387_)) as u8;
                        if v_isSharedCheck_397_ == 0 {
                            v___x_390_ = v___x_387_;
                            v_isShared_391_ = v_isSharedCheck_397_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_388_);
                            leanh::lean_dec(v___x_387_);
                            v___x_390_ = leanh::lean_box(0);
                            v_isShared_391_ = v_isSharedCheck_397_;
                            state = 13;
                            continue;
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_387_) == 0 {
                            leanh::lean_dec(v_val_334_);
                            leanh::lean_dec_ref(v_inst_333_);
                            v_a_398_ = leanh::lean_ctor_get(v___x_387_, 0);
                            v_isSharedCheck_405_ =
                                (!leanh::lean_is_exclusive(v___x_387_)) as u8;
                            if v_isSharedCheck_405_ == 0 {
                                v___x_400_ = v___x_387_;
                                v_isShared_401_ = v_isSharedCheck_405_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_398_);
                                leanh::lean_dec(v___x_387_);
                                v___x_400_ = leanh::lean_box(0);
                                v_isShared_401_ = v_isSharedCheck_405_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_406_ = leanh::lean_ctor_get(v___x_387_, 0);
                            leanh::lean_inc(v_a_406_);
                            leanh::lean_dec_ref_known(v___x_387_, 1);
                            v_a_336_ = v_a_406_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            13 => {
                v___x_392_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2;
                v___x_393_ = lean_string_append(v___x_392_, v_a_388_);
                leanh::lean_dec(v_a_388_);
                if v_isShared_391_ == 0 {
                    leanh::lean_ctor_set(v___x_390_, 0, v___x_393_);
                    v___x_395_ = v___x_390_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_396_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
                    v___x_395_ = v_reuseFailAlloc_396_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_395_;
            }
            15 => {
                if v_isShared_401_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_400_, 0);
                    v___x_403_ = v___x_400_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
                    v___x_403_ = v_reuseFailAlloc_404_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_403_;
            }
            17 => {
                v___x_416_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5;
                v___x_417_ = lean_string_append(v___x_416_, v_a_412_);
                leanh::lean_dec(v_a_412_);
                if v_isShared_415_ == 0 {
                    leanh::lean_ctor_set(v___x_414_, 0, v___x_417_);
                    v___x_419_ = v___x_414_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_420_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
                    v___x_419_ = v_reuseFailAlloc_420_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_419_;
            }
            19 => {
                if v_isShared_425_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_424_, 0);
                    v___x_427_ = v___x_424_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_428_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
                    v___x_427_ = v_reuseFailAlloc_428_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_427_;
            }
            21 => {
                v___x_441_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9;
                v___x_442_ = lean_string_append(v___x_441_, v_a_437_);
                leanh::lean_dec(v_a_437_);
                if v_isShared_440_ == 0 {
                    leanh::lean_ctor_set(v___x_439_, 0, v___x_442_);
                    v___x_444_ = v___x_439_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_445_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
                    v___x_444_ = v_reuseFailAlloc_445_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_444_;
            }
            23 => {
                if v_isShared_450_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_449_, 0);
                    v___x_452_ = v___x_449_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
                    v___x_452_ = v_reuseFailAlloc_453_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_452_;
            }
            25 => {
                v___x_465_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13;
                v___x_466_ = lean_string_append(v___x_465_, v_a_461_);
                leanh::lean_dec(v_a_461_);
                if v_isShared_464_ == 0 {
                    leanh::lean_ctor_set(v___x_463_, 0, v___x_466_);
                    v___x_468_ = v___x_463_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_469_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
                    v___x_468_ = v_reuseFailAlloc_469_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_468_;
            }
            27 => {
                if v_isShared_474_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_473_, 0);
                    v___x_476_ = v___x_473_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_476_;
            }
            29 => {
                v___x_483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_483_, 0, v_a_455_);
                leanh::lean_ctor_set(v___x_483_, 1, v_a_479_);
                if v_isShared_482_ == 0 {
                    leanh::lean_ctor_set(v___x_481_, 0, v___x_483_);
                    v___x_485_ = v___x_481_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
                    v___x_485_ = v_reuseFailAlloc_486_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_485_;
            }
            31 => {
                if v_isShared_492_ == 0 {
                    v___x_494_ = v___x_491_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_495_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
                    v___x_494_ = v_reuseFailAlloc_495_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_494_;
            }
            33 => {
                v___x_501_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_501_, 0, v_a_497_);
                if v_isShared_500_ == 0 {
                    leanh::lean_ctor_set(v___x_499_, 0, v___x_501_);
                    v___x_503_ = v___x_499_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
                    v___x_503_ = v_reuseFailAlloc_504_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_503_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lake_ReservoirResp_fromJson_x3f(
    mut v_00_u03b1_506_: *mut leanh::LeanObject,
    mut v_inst_507_: *mut leanh::LeanObject,
    mut v_val_508_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_507_, v_val_508_);
    return v___x_509_;
}
pub unsafe fn l_Lake_instFromJsonReservoirResp___redArg(
    mut v_inst_510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_511_ = leanh::lean_alloc_closure(
        l_Lake_ReservoirResp_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_511_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_511_, 1, v_inst_510_);
    return v___x_511_;
}
pub unsafe fn l_Lake_instFromJsonReservoirResp(
    mut v_00_u03b1_512_: *mut leanh::LeanObject,
    mut v_inst_513_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_514_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_514_ = leanh::lean_alloc_closure(
        l_Lake_ReservoirResp_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_514_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_514_, 1, v_inst_513_);
    return v___x_514_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Reservoir(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Reservoir(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Reservoir(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_JsonObject(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Reservoir(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Reservoir(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lake_Util_Reservoir(builtin);
}
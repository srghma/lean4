// Lean compiler output
// Module: Lake.Util.Reservoir
// Imports: Lake.Util.JsonObject
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
use crate::lean_imports_rs::Init::Data::String::Defs::lean_string_append;
use crate::lean_imports_rs::Init::Prelude::{lean_array_push, lean_mk_empty_array_with_capacity};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set, lean_ctor_set_tag,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lake_Reservoir_lakeHeaders___closed__0_value: LeanStringObject<30> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Reservoir_lakeHeaders___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__0_value) as *mut LeanObject;
pub static l_Lake_Reservoir_lakeHeaders___closed__1_value: LeanStringObject<34> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_Reservoir_lakeHeaders___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__1_value) as *mut LeanObject;
pub static l_Lake_Reservoir_lakeHeaders___closed__2_value: LeanArrayObject<2> = LeanArrayObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut LeanObject>() * 2) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 2,
    m_capacity: 2,
    m_data: [
        core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Lake_Reservoir_lakeHeaders___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__2_value) as *mut LeanObject;
pub static mut l_Lake_Reservoir_lakeHeaders: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_Reservoir_lakeHeaders___closed__2_value) as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_instFromJsonJson___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__1_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__2_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value: LeanClosureObject<0> =
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
        m_fun: l_Lake_JsonObject_fromJson_x3f as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__5_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value: LeanStringObject<7> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value: LeanStringObject<27> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 27,
        m_capacity: 27,
        m_length: 26,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 115, 116, 97, 116, 117, 115, 0,
        ],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__9_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value: LeanStringObject<28> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 28,
        m_capacity: 28,
        m_length: 27,
        m_data: [
            112, 114, 111, 112, 101, 114, 116, 121, 32, 110, 111, 116, 32, 102, 111, 117, 110, 100,
            58, 32, 109, 101, 115, 115, 97, 103, 101, 0,
        ],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__11_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12_value)
        as *mut LeanObject;
pub static l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13: *mut LeanObject =
    core::ptr::addr_of!(l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__13_value)
        as *mut LeanObject;
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___redArg(
    mut v_x_267_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_267_) == 0 {
        let mut v___x_268_: *mut LeanObject = core::ptr::null_mut();
        v___x_268_ = lean_unsigned_to_nat(0);
        return v___x_268_;
    } else {
        let mut v___x_269_: *mut LeanObject = core::ptr::null_mut();
        v___x_269_ = lean_unsigned_to_nat(1);
        return v___x_269_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___redArg___boxed(
    mut v_x_270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_271_: *mut LeanObject = core::ptr::null_mut();
    v_res_271_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_270_);
    lean_dec_ref(v_x_270_);
    return v_res_271_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx(
    mut v_00_u03b1_272_: *mut LeanObject,
    mut v_x_273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
    v___x_274_ = l_Lake_ReservoirResp_ctorIdx___redArg(v_x_273_);
    return v___x_274_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorIdx___boxed(
    mut v_00_u03b1_275_: *mut LeanObject,
    mut v_x_276_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_277_: *mut LeanObject = core::ptr::null_mut();
    v_res_277_ = l_Lake_ReservoirResp_ctorIdx(v_00_u03b1_275_, v_x_276_);
    lean_dec_ref(v_x_276_);
    return v_res_277_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim___redArg(
    mut v_t_278_: *mut LeanObject,
    mut v_k_279_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_278_) == 0 {
        let mut v_a_280_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_281_: *mut LeanObject = core::ptr::null_mut();
        v_a_280_ = lean_ctor_get(v_t_278_, 0);
        lean_inc(v_a_280_);
        lean_dec_ref_known(v_t_278_, 1);
        v___x_281_ = lean_apply_1(v_k_279_, v_a_280_);
        return v___x_281_;
    } else {
        let mut v_status_282_: *mut LeanObject = core::ptr::null_mut();
        let mut v_message_283_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_284_: *mut LeanObject = core::ptr::null_mut();
        v_status_282_ = lean_ctor_get(v_t_278_, 0);
        lean_inc(v_status_282_);
        v_message_283_ = lean_ctor_get(v_t_278_, 1);
        lean_inc_ref(v_message_283_);
        lean_dec_ref_known(v_t_278_, 2);
        v___x_284_ = lean_apply_2(v_k_279_, v_status_282_, v_message_283_);
        return v___x_284_;
    }
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim(
    mut v_00_u03b1_285_: *mut LeanObject,
    mut v_motive_286_: *mut LeanObject,
    mut v_ctorIdx_287_: *mut LeanObject,
    mut v_t_288_: *mut LeanObject,
    mut v_h_289_: *mut LeanObject,
    mut v_k_290_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_291_: *mut LeanObject = core::ptr::null_mut();
    v___x_291_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_288_, v_k_290_);
    return v___x_291_;
}
pub unsafe fn l_Lake_ReservoirResp_ctorElim___boxed(
    mut v_00_u03b1_292_: *mut LeanObject,
    mut v_motive_293_: *mut LeanObject,
    mut v_ctorIdx_294_: *mut LeanObject,
    mut v_t_295_: *mut LeanObject,
    mut v_h_296_: *mut LeanObject,
    mut v_k_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_298_: *mut LeanObject = core::ptr::null_mut();
    v_res_298_ = l_Lake_ReservoirResp_ctorElim(
        v_00_u03b1_292_,
        v_motive_293_,
        v_ctorIdx_294_,
        v_t_295_,
        v_h_296_,
        v_k_297_,
    );
    lean_dec(v_ctorIdx_294_);
    return v_res_298_;
}
pub unsafe fn l_Lake_ReservoirResp_data_elim___redArg(
    mut v_t_299_: *mut LeanObject,
    mut v_data_300_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_301_: *mut LeanObject = core::ptr::null_mut();
    v___x_301_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_299_, v_data_300_);
    return v___x_301_;
}
pub unsafe fn l_Lake_ReservoirResp_data_elim(
    mut v_00_u03b1_302_: *mut LeanObject,
    mut v_motive_303_: *mut LeanObject,
    mut v_t_304_: *mut LeanObject,
    mut v_h_305_: *mut LeanObject,
    mut v_data_306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_307_: *mut LeanObject = core::ptr::null_mut();
    v___x_307_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_304_, v_data_306_);
    return v___x_307_;
}
pub unsafe fn l_Lake_ReservoirResp_error_elim___redArg(
    mut v_t_308_: *mut LeanObject,
    mut v_error_309_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_310_: *mut LeanObject = core::ptr::null_mut();
    v___x_310_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_308_, v_error_309_);
    return v___x_310_;
}
pub unsafe fn l_Lake_ReservoirResp_error_elim(
    mut v_00_u03b1_311_: *mut LeanObject,
    mut v_motive_312_: *mut LeanObject,
    mut v_t_313_: *mut LeanObject,
    mut v_h_314_: *mut LeanObject,
    mut v_error_315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_316_: *mut LeanObject = core::ptr::null_mut();
    v___x_316_ = l_Lake_ReservoirResp_ctorElim___redArg(v_t_313_, v_error_315_);
    return v___x_316_;
}
pub unsafe fn l_Lake_ReservoirResp_fromJson_x3f___redArg(
    mut v_inst_333_: *mut LeanObject,
    mut v_val_334_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_340_: u8 = 0;
    let mut v___x_341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_345_: u8 = 0;
    let mut v___x_347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_349_: u8 = 0;
    let mut v_a_350_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_353_: u8 = 0;
    let mut v___x_355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_360_: u8 = 0;
    let mut v_isSharedCheck_361_: u8 = 0;
    let mut v___x_362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_366_: u8 = 0;
    let mut v___x_368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_370_: u8 = 0;
    let mut v_a_371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_374_: u8 = 0;
    let mut v___x_375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_379_: u8 = 0;
    let mut v___x_380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_391_: u8 = 0;
    let mut v___x_392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_397_: u8 = 0;
    let mut v_a_398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_401_: u8 = 0;
    let mut v___x_403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_405_: u8 = 0;
    let mut v_a_406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_415_: u8 = 0;
    let mut v___x_416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_421_: u8 = 0;
    let mut v_a_422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_425_: u8 = 0;
    let mut v___x_427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_429_: u8 = 0;
    let mut v_a_430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_440_: u8 = 0;
    let mut v___x_441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_446_: u8 = 0;
    let mut v_a_447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_450_: u8 = 0;
    let mut v___x_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_454_: u8 = 0;
    let mut v_a_455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_464_: u8 = 0;
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_470_: u8 = 0;
    let mut v_a_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_474_: u8 = 0;
    let mut v___x_476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_478_: u8 = 0;
    let mut v_a_479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_482_: u8 = 0;
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_487_: u8 = 0;
    let mut v___x_488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_492_: u8 = 0;
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_496_: u8 = 0;
    let mut v_a_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_500_: u8 = 0;
    let mut v___x_501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_505_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_val_334_);
                v___x_380_ = l_Lean_Json_getObj_x3f(v_val_334_);
                if lean_obj_tag(v___x_380_) == 1 {
                    v_a_381_ = lean_ctor_get(v___x_380_, 0);
                    lean_inc(v_a_381_);
                    lean_dec_ref_known(v___x_380_, 1);
                    v___f_382_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__0;
                    v___x_407_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__3;
                    v___x_408_ = l_Lake_JsonObject_getJson_x3f(v_a_381_, v___x_407_);
                    if lean_obj_tag(v___x_408_) == 0 {
                        state = 12;
                        continue;
                    } else {
                        v_val_409_ = lean_ctor_get(v___x_408_, 0);
                        lean_inc(v_val_409_);
                        lean_dec_ref_known(v___x_408_, 1);
                        v___x_410_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__4;
                        v___x_411_ = l_Option_fromJson_x3f___redArg(v___x_410_, v_val_409_);
                        if lean_obj_tag(v___x_411_) == 0 {
                            lean_dec(v_a_381_);
                            lean_dec(v_val_334_);
                            lean_dec_ref(v_inst_333_);
                            v_a_412_ = lean_ctor_get(v___x_411_, 0);
                            v_isSharedCheck_421_ = (!lean_is_exclusive(v___x_411_)) as u8;
                            if v_isSharedCheck_421_ == 0 {
                                v___x_414_ = v___x_411_;
                                v_isShared_415_ = v_isSharedCheck_421_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_412_);
                                lean_dec(v___x_411_);
                                v___x_414_ = lean_box(0);
                                v_isShared_415_ = v_isSharedCheck_421_;
                                state = 17;
                                continue;
                            }
                        } else {
                            if lean_obj_tag(v___x_411_) == 0 {
                                lean_dec(v_a_381_);
                                lean_dec(v_val_334_);
                                lean_dec_ref(v_inst_333_);
                                v_a_422_ = lean_ctor_get(v___x_411_, 0);
                                v_isSharedCheck_429_ = (!lean_is_exclusive(v___x_411_)) as u8;
                                if v_isSharedCheck_429_ == 0 {
                                    v___x_424_ = v___x_411_;
                                    v_isShared_425_ = v_isSharedCheck_429_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_422_);
                                    lean_dec(v___x_411_);
                                    v___x_424_ = lean_box(0);
                                    v_isShared_425_ = v_isSharedCheck_429_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                v_a_430_ = lean_ctor_get(v___x_411_, 0);
                                lean_inc(v_a_430_);
                                lean_dec_ref_known(v___x_411_, 1);
                                if lean_obj_tag(v_a_430_) == 1 {
                                    lean_dec(v_a_381_);
                                    lean_dec(v_val_334_);
                                    lean_dec_ref(v_inst_333_);
                                    v_val_431_ = lean_ctor_get(v_a_430_, 0);
                                    lean_inc(v_val_431_);
                                    lean_dec_ref_known(v_a_430_, 1);
                                    v___x_432_ =
                                        l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__6;
                                    v___x_433_ =
                                        l_Lake_JsonObject_getJson_x3f(v_val_431_, v___x_432_);
                                    if lean_obj_tag(v___x_433_) == 0 {
                                        lean_dec(v_val_431_);
                                        v___x_434_ =
                                            l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__8;
                                        return v___x_434_;
                                    } else {
                                        v_val_435_ = lean_ctor_get(v___x_433_, 0);
                                        lean_inc(v_val_435_);
                                        lean_dec_ref_known(v___x_433_, 1);
                                        v___x_436_ = l_Lean_Json_getNat_x3f(v_val_435_);
                                        if lean_obj_tag(v___x_436_) == 0 {
                                            lean_dec(v_val_431_);
                                            v_a_437_ = lean_ctor_get(v___x_436_, 0);
                                            v_isSharedCheck_446_ =
                                                (!lean_is_exclusive(v___x_436_)) as u8;
                                            if v_isSharedCheck_446_ == 0 {
                                                v___x_439_ = v___x_436_;
                                                v_isShared_440_ = v_isSharedCheck_446_;
                                                state = 21;
                                                continue;
                                            } else {
                                                lean_inc(v_a_437_);
                                                lean_dec(v___x_436_);
                                                v___x_439_ = lean_box(0);
                                                v_isShared_440_ = v_isSharedCheck_446_;
                                                state = 21;
                                                continue;
                                            }
                                        } else {
                                            if lean_obj_tag(v___x_436_) == 0 {
                                                lean_dec(v_val_431_);
                                                v_a_447_ = lean_ctor_get(v___x_436_, 0);
                                                v_isSharedCheck_454_ =
                                                    (!lean_is_exclusive(v___x_436_)) as u8;
                                                if v_isSharedCheck_454_ == 0 {
                                                    v___x_449_ = v___x_436_;
                                                    v_isShared_450_ = v_isSharedCheck_454_;
                                                    state = 23;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_447_);
                                                    lean_dec(v___x_436_);
                                                    v___x_449_ = lean_box(0);
                                                    v_isShared_450_ = v_isSharedCheck_454_;
                                                    state = 23;
                                                    continue;
                                                }
                                            } else {
                                                v_a_455_ = lean_ctor_get(v___x_436_, 0);
                                                lean_inc(v_a_455_);
                                                lean_dec_ref_known(v___x_436_, 1);
                                                v___x_456_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__10;
                                                v___x_457_ = l_Lake_JsonObject_getJson_x3f(
                                                    v_val_431_, v___x_456_,
                                                );
                                                lean_dec(v_val_431_);
                                                if lean_obj_tag(v___x_457_) == 0 {
                                                    lean_dec(v_a_455_);
                                                    v___x_458_ = l_Lake_ReservoirResp_fromJson_x3f___redArg___closed__12;
                                                    return v___x_458_;
                                                } else {
                                                    v_val_459_ = lean_ctor_get(v___x_457_, 0);
                                                    lean_inc(v_val_459_);
                                                    lean_dec_ref_known(v___x_457_, 1);
                                                    v___x_460_ = l_Lean_Json_getStr_x3f(v_val_459_);
                                                    if lean_obj_tag(v___x_460_) == 0 {
                                                        lean_dec(v_a_455_);
                                                        v_a_461_ = lean_ctor_get(v___x_460_, 0);
                                                        v_isSharedCheck_470_ =
                                                            (!lean_is_exclusive(v___x_460_)) as u8;
                                                        if v_isSharedCheck_470_ == 0 {
                                                            v___x_463_ = v___x_460_;
                                                            v_isShared_464_ = v_isSharedCheck_470_;
                                                            state = 25;
                                                            continue;
                                                        } else {
                                                            lean_inc(v_a_461_);
                                                            lean_dec(v___x_460_);
                                                            v___x_463_ = lean_box(0);
                                                            v_isShared_464_ = v_isSharedCheck_470_;
                                                            state = 25;
                                                            continue;
                                                        }
                                                    } else {
                                                        if lean_obj_tag(v___x_460_) == 0 {
                                                            lean_dec(v_a_455_);
                                                            v_a_471_ = lean_ctor_get(v___x_460_, 0);
                                                            v_isSharedCheck_478_ =
                                                                (!lean_is_exclusive(v___x_460_))
                                                                    as u8;
                                                            if v_isSharedCheck_478_ == 0 {
                                                                v___x_473_ = v___x_460_;
                                                                v_isShared_474_ =
                                                                    v_isSharedCheck_478_;
                                                                state = 27;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_471_);
                                                                lean_dec(v___x_460_);
                                                                v___x_473_ = lean_box(0);
                                                                v_isShared_474_ =
                                                                    v_isSharedCheck_478_;
                                                                state = 27;
                                                                continue;
                                                            }
                                                        } else {
                                                            v_a_479_ = lean_ctor_get(v___x_460_, 0);
                                                            v_isSharedCheck_487_ =
                                                                (!lean_is_exclusive(v___x_460_))
                                                                    as u8;
                                                            if v_isSharedCheck_487_ == 0 {
                                                                v___x_481_ = v___x_460_;
                                                                v_isShared_482_ =
                                                                    v_isSharedCheck_487_;
                                                                state = 29;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_479_);
                                                                lean_dec(v___x_460_);
                                                                v___x_481_ = lean_box(0);
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
                                    lean_dec(v_a_430_);
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___x_380_);
                    v___x_488_ = lean_apply_1(v_inst_333_, v_val_334_);
                    if lean_obj_tag(v___x_488_) == 0 {
                        v_a_489_ = lean_ctor_get(v___x_488_, 0);
                        v_isSharedCheck_496_ = (!lean_is_exclusive(v___x_488_)) as u8;
                        if v_isSharedCheck_496_ == 0 {
                            v___x_491_ = v___x_488_;
                            v_isShared_492_ = v_isSharedCheck_496_;
                            state = 31;
                            continue;
                        } else {
                            lean_inc(v_a_489_);
                            lean_dec(v___x_488_);
                            v___x_491_ = lean_box(0);
                            v_isShared_492_ = v_isSharedCheck_496_;
                            state = 31;
                            continue;
                        }
                    } else {
                        v_a_497_ = lean_ctor_get(v___x_488_, 0);
                        v_isSharedCheck_505_ = (!lean_is_exclusive(v___x_488_)) as u8;
                        if v_isSharedCheck_505_ == 0 {
                            v___x_499_ = v___x_488_;
                            v_isShared_500_ = v_isSharedCheck_505_;
                            state = 33;
                            continue;
                        } else {
                            lean_inc(v_a_497_);
                            lean_dec(v___x_488_);
                            v___x_499_ = lean_box(0);
                            v_isShared_500_ = v_isSharedCheck_505_;
                            state = 33;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_336_) == 1 {
                    lean_dec(v_val_334_);
                    v_val_337_ = lean_ctor_get(v_a_336_, 0);
                    v_isSharedCheck_361_ = (!lean_is_exclusive(v_a_336_)) as u8;
                    if v_isSharedCheck_361_ == 0 {
                        v___x_339_ = v_a_336_;
                        v_isShared_340_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_337_);
                        lean_dec(v_a_336_);
                        v___x_339_ = lean_box(0);
                        v_isShared_340_ = v_isSharedCheck_361_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_336_);
                    v___x_362_ = lean_apply_1(v_inst_333_, v_val_334_);
                    if lean_obj_tag(v___x_362_) == 0 {
                        v_a_363_ = lean_ctor_get(v___x_362_, 0);
                        v_isSharedCheck_370_ = (!lean_is_exclusive(v___x_362_)) as u8;
                        if v_isSharedCheck_370_ == 0 {
                            v___x_365_ = v___x_362_;
                            v_isShared_366_ = v_isSharedCheck_370_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_363_);
                            lean_dec(v___x_362_);
                            v___x_365_ = lean_box(0);
                            v_isShared_366_ = v_isSharedCheck_370_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_a_371_ = lean_ctor_get(v___x_362_, 0);
                        v_isSharedCheck_379_ = (!lean_is_exclusive(v___x_362_)) as u8;
                        if v_isSharedCheck_379_ == 0 {
                            v___x_373_ = v___x_362_;
                            v_isShared_374_ = v_isSharedCheck_379_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_371_);
                            lean_dec(v___x_362_);
                            v___x_373_ = lean_box(0);
                            v_isShared_374_ = v_isSharedCheck_379_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            2 => {
                v___x_341_ = lean_apply_1(v_inst_333_, v_val_337_);
                if lean_obj_tag(v___x_341_) == 0 {
                    lean_del_object(v___x_339_);
                    v_a_342_ = lean_ctor_get(v___x_341_, 0);
                    v_isSharedCheck_349_ = (!lean_is_exclusive(v___x_341_)) as u8;
                    if v_isSharedCheck_349_ == 0 {
                        v___x_344_ = v___x_341_;
                        v_isShared_345_ = v_isSharedCheck_349_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_342_);
                        lean_dec(v___x_341_);
                        v___x_344_ = lean_box(0);
                        v_isShared_345_ = v_isSharedCheck_349_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_350_ = lean_ctor_get(v___x_341_, 0);
                    v_isSharedCheck_360_ = (!lean_is_exclusive(v___x_341_)) as u8;
                    if v_isSharedCheck_360_ == 0 {
                        v___x_352_ = v___x_341_;
                        v_isShared_353_ = v_isSharedCheck_360_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_350_);
                        lean_dec(v___x_341_);
                        v___x_352_ = lean_box(0);
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
                    v_reuseFailAlloc_348_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_348_, 0, v_a_342_);
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
                    lean_ctor_set_tag(v___x_339_, 0);
                    lean_ctor_set(v___x_339_, 0, v_a_350_);
                    v___x_355_ = v___x_339_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_350_);
                    v___x_355_ = v_reuseFailAlloc_359_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_353_ == 0 {
                    lean_ctor_set(v___x_352_, 0, v___x_355_);
                    v___x_357_ = v___x_352_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_355_);
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
                    v_reuseFailAlloc_369_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_369_, 0, v_a_363_);
                    v___x_368_ = v_reuseFailAlloc_369_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_368_;
            }
            10 => {
                v___x_375_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_375_, 0, v_a_371_);
                if v_isShared_374_ == 0 {
                    lean_ctor_set(v___x_373_, 0, v___x_375_);
                    v___x_377_ = v___x_373_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_375_);
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
                lean_dec(v_a_381_);
                if lean_obj_tag(v___x_385_) == 0 {
                    v_a_336_ = v___x_385_;
                    state = 1;
                    continue;
                } else {
                    v_val_386_ = lean_ctor_get(v___x_385_, 0);
                    lean_inc(v_val_386_);
                    lean_dec_ref_known(v___x_385_, 1);
                    v___x_387_ = l_Option_fromJson_x3f___redArg(v___f_382_, v_val_386_);
                    if lean_obj_tag(v___x_387_) == 0 {
                        lean_dec(v_val_334_);
                        lean_dec_ref(v_inst_333_);
                        v_a_388_ = lean_ctor_get(v___x_387_, 0);
                        v_isSharedCheck_397_ = (!lean_is_exclusive(v___x_387_)) as u8;
                        if v_isSharedCheck_397_ == 0 {
                            v___x_390_ = v___x_387_;
                            v_isShared_391_ = v_isSharedCheck_397_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_388_);
                            lean_dec(v___x_387_);
                            v___x_390_ = lean_box(0);
                            v_isShared_391_ = v_isSharedCheck_397_;
                            state = 13;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_387_) == 0 {
                            lean_dec(v_val_334_);
                            lean_dec_ref(v_inst_333_);
                            v_a_398_ = lean_ctor_get(v___x_387_, 0);
                            v_isSharedCheck_405_ = (!lean_is_exclusive(v___x_387_)) as u8;
                            if v_isSharedCheck_405_ == 0 {
                                v___x_400_ = v___x_387_;
                                v_isShared_401_ = v_isSharedCheck_405_;
                                state = 15;
                                continue;
                            } else {
                                lean_inc(v_a_398_);
                                lean_dec(v___x_387_);
                                v___x_400_ = lean_box(0);
                                v_isShared_401_ = v_isSharedCheck_405_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_406_ = lean_ctor_get(v___x_387_, 0);
                            lean_inc(v_a_406_);
                            lean_dec_ref_known(v___x_387_, 1);
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
                lean_dec(v_a_388_);
                if v_isShared_391_ == 0 {
                    lean_ctor_set(v___x_390_, 0, v___x_393_);
                    v___x_395_ = v___x_390_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_396_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_393_);
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
                    lean_ctor_set_tag(v___x_400_, 0);
                    v___x_403_ = v___x_400_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
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
                lean_dec(v_a_412_);
                if v_isShared_415_ == 0 {
                    lean_ctor_set(v___x_414_, 0, v___x_417_);
                    v___x_419_ = v___x_414_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_417_);
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
                    lean_ctor_set_tag(v___x_424_, 0);
                    v___x_427_ = v___x_424_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_428_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_428_, 0, v_a_422_);
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
                lean_dec(v_a_437_);
                if v_isShared_440_ == 0 {
                    lean_ctor_set(v___x_439_, 0, v___x_442_);
                    v___x_444_ = v___x_439_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_445_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_445_, 0, v___x_442_);
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
                    lean_ctor_set_tag(v___x_449_, 0);
                    v___x_452_ = v___x_449_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_453_, 0, v_a_447_);
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
                lean_dec(v_a_461_);
                if v_isShared_464_ == 0 {
                    lean_ctor_set(v___x_463_, 0, v___x_466_);
                    v___x_468_ = v___x_463_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_469_, 0, v___x_466_);
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
                    lean_ctor_set_tag(v___x_473_, 0);
                    v___x_476_ = v___x_473_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_477_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_477_, 0, v_a_471_);
                    v___x_476_ = v_reuseFailAlloc_477_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_476_;
            }
            29 => {
                v___x_483_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_483_, 0, v_a_455_);
                lean_ctor_set(v___x_483_, 1, v_a_479_);
                if v_isShared_482_ == 0 {
                    lean_ctor_set(v___x_481_, 0, v___x_483_);
                    v___x_485_ = v___x_481_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_486_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_486_, 0, v___x_483_);
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
                    v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_495_, 0, v_a_489_);
                    v___x_494_ = v_reuseFailAlloc_495_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_494_;
            }
            33 => {
                v___x_501_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_501_, 0, v_a_497_);
                if v_isShared_500_ == 0 {
                    lean_ctor_set(v___x_499_, 0, v___x_501_);
                    v___x_503_ = v___x_499_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_504_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_504_, 0, v___x_501_);
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
    mut v_00_u03b1_506_: *mut LeanObject,
    mut v_inst_507_: *mut LeanObject,
    mut v_val_508_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    v___x_509_ = l_Lake_ReservoirResp_fromJson_x3f___redArg(v_inst_507_, v_val_508_);
    return v___x_509_;
}
pub unsafe fn l_Lake_instFromJsonReservoirResp___redArg(
    mut v_inst_510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = lean_alloc_closure(
        l_Lake_ReservoirResp_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_511_, 0, lean_box(0));
    lean_closure_set(v___x_511_, 1, v_inst_510_);
    return v___x_511_;
}
pub unsafe fn l_Lake_instFromJsonReservoirResp(
    mut v_00_u03b1_512_: *mut LeanObject,
    mut v_inst_513_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    v___x_514_ = lean_alloc_closure(
        l_Lake_ReservoirResp_fromJson_x3f as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___x_514_, 0, lean_box(0));
    lean_closure_set(v___x_514_, 1, v_inst_513_);
    return v___x_514_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lake_Util_Reservoir(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lake_Util_Reservoir(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lake_Util_Reservoir(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lake_Util_JsonObject(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lake_Util_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lake_Util_Reservoir(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lake_Util_Reservoir(builtin);
}

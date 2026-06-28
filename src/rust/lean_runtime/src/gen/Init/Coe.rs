// Lean compiler output
// Module: Init.Coe
// Imports: Init.Prelude Init.Prelude
use crate::r#gen::Init::Prelude::{
    initialize_Init_Prelude, l_Lean_Name_mkStr1, meta_initialize_Init_Prelude,
    runtime_initialize_Init_Prelude,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_4,
    lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_unbox,
};
pub static l_instCoeTC___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_instCoeTC___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_instCoeTC___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_instCoeTC___closed__0_value) as *mut LeanObject;
pub static l_coeNotation___closed__0_value: LeanStringObject<12> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [99, 111, 101, 78, 111, 116, 97, 116, 105, 111, 110, 0],
};
static mut l_coeNotation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__0_value) as *mut LeanObject;
pub static l_coeNotation___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__0_value) as *mut LeanObject,
        4193428478068483112 as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__1_value) as *mut LeanObject;
pub static l_coeNotation___closed__2_value: LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [97, 110, 100, 116, 104, 101, 110, 0],
};
static mut l_coeNotation___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__2_value) as *mut LeanObject;
pub static l_coeNotation___closed__3_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__2_value) as *mut LeanObject,
        12571085391447129896 as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__3_value) as *mut LeanObject;
pub static l_coeNotation___closed__4_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 145, 0],
};
static mut l_coeNotation___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__4_value) as *mut LeanObject;
pub static l_coeNotation___closed__5_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_coeNotation___closed__4_value) as *mut LeanObject],
};
static mut l_coeNotation___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__5_value) as *mut LeanObject;
pub static l_coeNotation___closed__6_value: LeanStringObject<5> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [116, 101, 114, 109, 0],
};
static mut l_coeNotation___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__6_value) as *mut LeanObject;
pub static l_coeNotation___closed__7_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__6_value) as *mut LeanObject,
        8609355255726335675 as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__7_value) as *mut LeanObject;
pub static l_coeNotation___closed__8_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 7,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeNotation___closed__7_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__8_value) as *mut LeanObject;
pub static l_coeNotation___closed__9_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeNotation___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__5_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__9_value) as *mut LeanObject;
pub static l_coeNotation___closed__10_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeNotation___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__9_value) as *mut LeanObject,
    ],
};
static mut l_coeNotation___closed__10: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__10_value) as *mut LeanObject;
pub static mut l_coeNotation: *mut LeanObject =
    core::ptr::addr_of!(l_coeNotation___closed__10_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__0_value: LeanStringObject<15> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 111, 101, 70, 117, 110, 78, 111, 116, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_coeFunNotation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__0_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeFunNotation___closed__0_value) as *mut LeanObject,
        18048501494880625826 as *mut LeanObject,
    ],
};
static mut l_coeFunNotation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__1_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 135, 145, 0],
};
static mut l_coeFunNotation___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__2_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_coeFunNotation___closed__2_value) as *mut LeanObject],
};
static mut l_coeFunNotation___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__3_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeNotation___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeFunNotation___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_coeFunNotation___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__4_value) as *mut LeanObject;
pub static l_coeFunNotation___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeFunNotation___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeFunNotation___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_coeFunNotation___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__5_value) as *mut LeanObject;
pub static mut l_coeFunNotation: *mut LeanObject =
    core::ptr::addr_of!(l_coeFunNotation___closed__5_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__0_value: LeanStringObject<16> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        99, 111, 101, 83, 111, 114, 116, 78, 111, 116, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_coeSortNotation___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__0_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__1_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeSortNotation___closed__0_value) as *mut LeanObject,
        6774197400381406744 as *mut LeanObject,
    ],
};
static mut l_coeSortNotation___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__1_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__2_value: LeanStringObject<4> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 1,
    m_data: [226, 134, 165, 0],
};
static mut l_coeSortNotation___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__2_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__3_value: LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 5,
    },
    m_objs: [core::ptr::addr_of!(l_coeSortNotation___closed__2_value) as *mut LeanObject],
};
static mut l_coeSortNotation___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__3_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__4_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 2,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeNotation___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeSortNotation___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_coeNotation___closed__8_value) as *mut LeanObject,
    ],
};
static mut l_coeSortNotation___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__4_value) as *mut LeanObject;
pub static l_coeSortNotation___closed__5_value: LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_coeSortNotation___closed__1_value) as *mut LeanObject,
        (((1024 as usize) << 1) | 1) as *mut LeanObject,
        core::ptr::addr_of!(l_coeSortNotation___closed__4_value) as *mut LeanObject,
    ],
};
static mut l_coeSortNotation___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__5_value) as *mut LeanObject;
pub static mut l_coeSortNotation: *mut LeanObject =
    core::ptr::addr_of!(l_coeSortNotation___closed__5_value) as *mut LeanObject;
pub static mut l_boolToProp: *mut LeanObject = core::ptr::null_mut();
pub static mut l_boolToSort: *mut LeanObject = core::ptr::null_mut();
pub static l_subtypeCoe___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_subtypeCoe___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_subtypeCoe___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_subtypeCoe___closed__0_value) as *mut LeanObject;
pub unsafe fn l_instCoeTCOfCoe___redArg___lam__0(
    mut v_inst_244_: *mut LeanObject,
    mut v_inst_245_: *mut LeanObject,
    mut v_a_246_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut LeanObject = core::ptr::null_mut();
    v___x_247_ = lean_apply_1(v_inst_244_, v_a_246_);
    v___x_248_ = lean_apply_1(v_inst_245_, v___x_247_);
    return v___x_248_;
}
pub unsafe fn l_instCoeTCOfCoe___redArg(
    mut v_inst_249_: *mut LeanObject,
    mut v_inst_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_251_: *mut LeanObject = core::ptr::null_mut();
    v___f_251_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_251_, 0, v_inst_250_);
    lean_closure_set(v___f_251_, 1, v_inst_249_);
    return v___f_251_;
}
pub unsafe fn l_instCoeTCOfCoe(
    mut v_00_u03b2_252_: *mut LeanObject,
    mut v_00_u03b3_253_: *mut LeanObject,
    mut v_00_u03b1_254_: *mut LeanObject,
    mut v_inst_255_: *mut LeanObject,
    mut v_inst_256_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_257_: *mut LeanObject = core::ptr::null_mut();
    v___f_257_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_257_, 0, v_inst_256_);
    lean_closure_set(v___f_257_, 1, v_inst_255_);
    return v___f_257_;
}
pub unsafe fn l_instCoeTCOfCoe__1___redArg___lam__0(
    mut v_inst_258_: *mut LeanObject,
    mut v_a_259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
    v___x_260_ = lean_apply_1(v_inst_258_, v_a_259_);
    return v___x_260_;
}
pub unsafe fn l_instCoeTCOfCoe__1___redArg(mut v_inst_261_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_262_: *mut LeanObject = core::ptr::null_mut();
    v___f_262_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_262_, 0, v_inst_261_);
    return v___f_262_;
}
pub unsafe fn l_instCoeTCOfCoe__1(
    mut v_00_u03b1_263_: *mut LeanObject,
    mut v_00_u03b2_264_: *mut LeanObject,
    mut v_inst_265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_266_: *mut LeanObject = core::ptr::null_mut();
    v___f_266_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_266_, 0, v_inst_265_);
    return v___f_266_;
}
pub unsafe fn l_instCoeTC___lam__0(mut v_a_267_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_267_);
    return v_a_267_;
}
pub unsafe fn l_instCoeTC___lam__0___boxed(mut v_a_268_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_269_: *mut LeanObject = core::ptr::null_mut();
    v_res_269_ = l_instCoeTC___lam__0(v_a_268_);
    lean_dec(v_a_268_);
    return v_res_269_;
}
pub unsafe fn l_instCoeTC(mut v_00_u03b1_271_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_272_: *mut LeanObject = core::ptr::null_mut();
    v___f_272_ = l_instCoeTC___closed__0;
    return v___f_272_;
}
pub unsafe fn l_instCoeOTCOfCoeOut___redArg(
    mut v_inst_273_: *mut LeanObject,
    mut v_inst_274_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_275_: *mut LeanObject = core::ptr::null_mut();
    v___f_275_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_275_, 0, v_inst_273_);
    lean_closure_set(v___f_275_, 1, v_inst_274_);
    return v___f_275_;
}
pub unsafe fn l_instCoeOTCOfCoeOut(
    mut v_00_u03b1_276_: *mut LeanObject,
    mut v_00_u03b2_277_: *mut LeanObject,
    mut v_00_u03b3_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_inst_280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_281_: *mut LeanObject = core::ptr::null_mut();
    v___f_281_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_281_, 0, v_inst_279_);
    lean_closure_set(v___f_281_, 1, v_inst_280_);
    return v___f_281_;
}
pub unsafe fn l_instCoeOTCOfCoeTC___redArg(mut v_inst_282_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_283_: *mut LeanObject = core::ptr::null_mut();
    v___f_283_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_283_, 0, v_inst_282_);
    return v___f_283_;
}
pub unsafe fn l_instCoeOTCOfCoeTC(
    mut v_00_u03b1_284_: *mut LeanObject,
    mut v_00_u03b2_285_: *mut LeanObject,
    mut v_inst_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_287_: *mut LeanObject = core::ptr::null_mut();
    v___f_287_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_287_, 0, v_inst_286_);
    return v___f_287_;
}
pub unsafe fn l_instCoeOTC(mut v_00_u03b1_288_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_289_: *mut LeanObject = core::ptr::null_mut();
    v___f_289_ = l_instCoeTC___closed__0;
    return v___f_289_;
}
pub unsafe fn l_instCoeHTCOfCoeHeadOfCoeOTC___redArg(
    mut v_inst_290_: *mut LeanObject,
    mut v_inst_291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_292_: *mut LeanObject = core::ptr::null_mut();
    v___f_292_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_292_, 0, v_inst_290_);
    lean_closure_set(v___f_292_, 1, v_inst_291_);
    return v___f_292_;
}
pub unsafe fn l_instCoeHTCOfCoeHeadOfCoeOTC(
    mut v_00_u03b1_293_: *mut LeanObject,
    mut v_00_u03b2_294_: *mut LeanObject,
    mut v_00_u03b3_295_: *mut LeanObject,
    mut v_inst_296_: *mut LeanObject,
    mut v_inst_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_298_: *mut LeanObject = core::ptr::null_mut();
    v___f_298_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_298_, 0, v_inst_296_);
    lean_closure_set(v___f_298_, 1, v_inst_297_);
    return v___f_298_;
}
pub unsafe fn l_instCoeHTCOfCoeOTC___redArg(mut v_inst_299_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_300_: *mut LeanObject = core::ptr::null_mut();
    v___f_300_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_300_, 0, v_inst_299_);
    return v___f_300_;
}
pub unsafe fn l_instCoeHTCOfCoeOTC(
    mut v_00_u03b1_301_: *mut LeanObject,
    mut v_00_u03b2_302_: *mut LeanObject,
    mut v_inst_303_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_304_: *mut LeanObject = core::ptr::null_mut();
    v___f_304_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_304_, 0, v_inst_303_);
    return v___f_304_;
}
pub unsafe fn l_instCoeHTC(mut v_00_u03b1_305_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_306_: *mut LeanObject = core::ptr::null_mut();
    v___f_306_ = l_instCoeTC___closed__0;
    return v___f_306_;
}
pub unsafe fn l_instCoeHTCTOfCoeTailOfCoeHTC___redArg(
    mut v_inst_307_: *mut LeanObject,
    mut v_inst_308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_309_: *mut LeanObject = core::ptr::null_mut();
    v___f_309_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_309_, 0, v_inst_308_);
    lean_closure_set(v___f_309_, 1, v_inst_307_);
    return v___f_309_;
}
pub unsafe fn l_instCoeHTCTOfCoeTailOfCoeHTC(
    mut v_00_u03b2_310_: *mut LeanObject,
    mut v_00_u03b3_311_: *mut LeanObject,
    mut v_00_u03b1_312_: *mut LeanObject,
    mut v_inst_313_: *mut LeanObject,
    mut v_inst_314_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_315_: *mut LeanObject = core::ptr::null_mut();
    v___f_315_ = lean_alloc_closure(
        l_instCoeTCOfCoe___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_315_, 0, v_inst_314_);
    lean_closure_set(v___f_315_, 1, v_inst_313_);
    return v___f_315_;
}
pub unsafe fn l_instCoeHTCTOfCoeHTC___redArg(mut v_inst_316_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_317_: *mut LeanObject = core::ptr::null_mut();
    v___f_317_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_317_, 0, v_inst_316_);
    return v___f_317_;
}
pub unsafe fn l_instCoeHTCTOfCoeHTC(
    mut v_00_u03b1_318_: *mut LeanObject,
    mut v_00_u03b2_319_: *mut LeanObject,
    mut v_inst_320_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_321_: *mut LeanObject = core::ptr::null_mut();
    v___f_321_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_321_, 0, v_inst_320_);
    return v___f_321_;
}
pub unsafe fn l_instCoeHTCT(mut v_00_u03b1_322_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_323_: *mut LeanObject = core::ptr::null_mut();
    v___f_323_ = l_instCoeTC___closed__0;
    return v___f_323_;
}
pub unsafe fn l_instCoeTOfCoeHTCT___redArg(
    mut v_a_324_: *mut LeanObject,
    mut v_inst_325_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_326_: *mut LeanObject = core::ptr::null_mut();
    v___x_326_ = lean_apply_1(v_inst_325_, v_a_324_);
    return v___x_326_;
}
pub unsafe fn l_instCoeTOfCoeHTCT(
    mut v_00_u03b1_327_: *mut LeanObject,
    mut v_00_u03b2_328_: *mut LeanObject,
    mut v_a_329_: *mut LeanObject,
    mut v_inst_330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_331_: *mut LeanObject = core::ptr::null_mut();
    v___x_331_ = lean_apply_1(v_inst_330_, v_a_329_);
    return v___x_331_;
}
pub unsafe fn l_instCoeTOfCoeDep___redArg(mut v_inst_332_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_inst_332_);
    return v_inst_332_;
}
pub unsafe fn l_instCoeTOfCoeDep___redArg___boxed(
    mut v_inst_333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_334_: *mut LeanObject = core::ptr::null_mut();
    v_res_334_ = l_instCoeTOfCoeDep___redArg(v_inst_333_);
    lean_dec(v_inst_333_);
    return v_res_334_;
}
pub unsafe fn l_instCoeTOfCoeDep(
    mut v_00_u03b1_335_: *mut LeanObject,
    mut v_a_336_: *mut LeanObject,
    mut v_00_u03b2_337_: *mut LeanObject,
    mut v_inst_338_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_inst_338_);
    return v_inst_338_;
}
pub unsafe fn l_instCoeTOfCoeDep___boxed(
    mut v_00_u03b1_339_: *mut LeanObject,
    mut v_a_340_: *mut LeanObject,
    mut v_00_u03b2_341_: *mut LeanObject,
    mut v_inst_342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_343_: *mut LeanObject = core::ptr::null_mut();
    v_res_343_ = l_instCoeTOfCoeDep(v_00_u03b1_339_, v_a_340_, v_00_u03b2_341_, v_inst_342_);
    lean_dec(v_inst_342_);
    lean_dec(v_a_340_);
    return v_res_343_;
}
pub unsafe fn l_instCoeT___redArg(mut v_a_344_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_a_344_);
    return v_a_344_;
}
pub unsafe fn l_instCoeT___redArg___boxed(mut v_a_345_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_346_: *mut LeanObject = core::ptr::null_mut();
    v_res_346_ = l_instCoeT___redArg(v_a_345_);
    lean_dec(v_a_345_);
    return v_res_346_;
}
pub unsafe fn l_instCoeT(
    mut v_00_u03b1_347_: *mut LeanObject,
    mut v_a_348_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_a_348_);
    return v_a_348_;
}
pub unsafe fn l_instCoeT___boxed(
    mut v_00_u03b1_349_: *mut LeanObject,
    mut v_a_350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_351_: *mut LeanObject = core::ptr::null_mut();
    v_res_351_ = l_instCoeT(v_00_u03b1_349_, v_a_350_);
    lean_dec(v_a_350_);
    return v_res_351_;
}
pub unsafe fn l_instCoeOutOfCoeFun___redArg(mut v_inst_352_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_353_: *mut LeanObject = core::ptr::null_mut();
    v___f_353_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_353_, 0, v_inst_352_);
    return v___f_353_;
}
pub unsafe fn l_instCoeOutOfCoeFun(
    mut v_00_u03b1_354_: *mut LeanObject,
    mut v_00_u03b2_355_: *mut LeanObject,
    mut v_inst_356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_357_: *mut LeanObject = core::ptr::null_mut();
    v___f_357_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_357_, 0, v_inst_356_);
    return v___f_357_;
}
pub unsafe fn l_instCoeOutOfCoeSort___redArg(mut v_inst_358_: *mut LeanObject) -> *mut LeanObject {
    let mut v___f_359_: *mut LeanObject = core::ptr::null_mut();
    v___f_359_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_359_, 0, v_inst_358_);
    return v___f_359_;
}
pub unsafe fn l_instCoeOutOfCoeSort(
    mut v_00_u03b1_360_: *mut LeanObject,
    mut v_00_u03b2_361_: *mut LeanObject,
    mut v_inst_362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_363_: *mut LeanObject = core::ptr::null_mut();
    v___f_363_ = lean_alloc_closure(
        l_instCoeTCOfCoe__1___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_363_, 0, v_inst_362_);
    return v___f_363_;
}
pub unsafe fn _init_l_boolToProp() -> *mut LeanObject {
    let mut v___x_418_: *mut LeanObject = core::ptr::null_mut();
    v___x_418_ = lean_box(0);
    return v___x_418_;
}
pub unsafe fn _init_l_boolToSort() -> *mut LeanObject {
    let mut v___x_419_: *mut LeanObject = core::ptr::null_mut();
    v___x_419_ = lean_box(0);
    return v___x_419_;
}
pub unsafe fn l_decPropToBool___redArg(mut v_inst_420_: u8) -> u8 {
    return v_inst_420_;
}
pub unsafe fn l_decPropToBool___redArg___boxed(
    mut v_inst_421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_7__boxed_422_: u8 = 0;
    let mut v_res_423_: u8 = 0;
    let mut v_r_424_: *mut LeanObject = core::ptr::null_mut();
    v_inst_7__boxed_422_ = (lean_unbox(v_inst_421_) as u8);
    v_res_423_ = l_decPropToBool___redArg(v_inst_7__boxed_422_);
    v_r_424_ = lean_box((v_res_423_) as usize);
    return v_r_424_;
}
pub unsafe fn l_decPropToBool(mut v_p_425_: *mut LeanObject, mut v_inst_426_: u8) -> u8 {
    return v_inst_426_;
}
pub unsafe fn l_decPropToBool___boxed(
    mut v_p_427_: *mut LeanObject,
    mut v_inst_428_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_inst_10__boxed_429_: u8 = 0;
    let mut v_res_430_: u8 = 0;
    let mut v_r_431_: *mut LeanObject = core::ptr::null_mut();
    v_inst_10__boxed_429_ = (lean_unbox(v_inst_428_) as u8);
    v_res_430_ = l_decPropToBool(v_p_427_, v_inst_10__boxed_429_);
    v_r_431_ = lean_box((v_res_430_) as usize);
    return v_r_431_;
}
pub unsafe fn l_subtypeCoe___lam__0(mut v_v_432_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_v_432_);
    return v_v_432_;
}
pub unsafe fn l_subtypeCoe___lam__0___boxed(mut v_v_433_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_434_: *mut LeanObject = core::ptr::null_mut();
    v_res_434_ = l_subtypeCoe___lam__0(v_v_433_);
    lean_dec(v_v_433_);
    return v_res_434_;
}
pub unsafe fn l_subtypeCoe(
    mut v_00_u03b1_436_: *mut LeanObject,
    mut v_p_437_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_438_: *mut LeanObject = core::ptr::null_mut();
    v___f_438_ = l_subtypeCoe___closed__0;
    return v___f_438_;
}
pub unsafe fn l_Lean_Internal_liftCoeM___redArg___lam__0(
    mut v_inst_439_: *mut LeanObject,
    mut v_toPure_440_: *mut LeanObject,
    mut v_a_441_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_443_: *mut LeanObject = core::ptr::null_mut();
    v___x_442_ = lean_apply_1(v_inst_439_, v_a_441_);
    v___x_443_ = lean_apply_2(v_toPure_440_, lean_box(0), v___x_442_);
    return v___x_443_;
}
pub unsafe fn l_Lean_Internal_liftCoeM___redArg(
    mut v_inst_444_: *mut LeanObject,
    mut v_inst_445_: *mut LeanObject,
    mut v_inst_446_: *mut LeanObject,
    mut v_x_447_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_453_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_448_ = lean_ctor_get(v_inst_446_, 0);
    lean_inc_ref(v_toApplicative_448_);
    v_toBind_449_ = lean_ctor_get(v_inst_446_, 1);
    lean_inc(v_toBind_449_);
    lean_dec_ref(v_inst_446_);
    v_toPure_450_ = lean_ctor_get(v_toApplicative_448_, 1);
    lean_inc(v_toPure_450_);
    lean_dec_ref(v_toApplicative_448_);
    v___x_451_ = lean_apply_2(v_inst_444_, lean_box(0), v_x_447_);
    v___f_452_ = lean_alloc_closure(
        l_Lean_Internal_liftCoeM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_452_, 0, v_inst_445_);
    lean_closure_set(v___f_452_, 1, v_toPure_450_);
    v___x_453_ = lean_apply_4(
        v_toBind_449_,
        lean_box(0),
        lean_box(0),
        v___x_451_,
        v___f_452_,
    );
    return v___x_453_;
}
pub unsafe fn l_Lean_Internal_liftCoeM(
    mut v_m_454_: *mut LeanObject,
    mut v_n_455_: *mut LeanObject,
    mut v_00_u03b1_456_: *mut LeanObject,
    mut v_00_u03b2_457_: *mut LeanObject,
    mut v_inst_458_: *mut LeanObject,
    mut v_inst_459_: *mut LeanObject,
    mut v_inst_460_: *mut LeanObject,
    mut v_x_461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_467_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_462_ = lean_ctor_get(v_inst_460_, 0);
    lean_inc_ref(v_toApplicative_462_);
    v_toBind_463_ = lean_ctor_get(v_inst_460_, 1);
    lean_inc(v_toBind_463_);
    lean_dec_ref(v_inst_460_);
    v_toPure_464_ = lean_ctor_get(v_toApplicative_462_, 1);
    lean_inc(v_toPure_464_);
    lean_dec_ref(v_toApplicative_462_);
    v___x_465_ = lean_apply_2(v_inst_458_, lean_box(0), v_x_461_);
    v___f_466_ = lean_alloc_closure(
        l_Lean_Internal_liftCoeM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_466_, 0, v_inst_459_);
    lean_closure_set(v___f_466_, 1, v_toPure_464_);
    v___x_467_ = lean_apply_4(
        v_toBind_463_,
        lean_box(0),
        lean_box(0),
        v___x_465_,
        v___f_466_,
    );
    return v___x_467_;
}
pub unsafe fn l_Lean_Internal_coeM___redArg(
    mut v_inst_468_: *mut LeanObject,
    mut v_inst_469_: *mut LeanObject,
    mut v_x_470_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_471_ = lean_ctor_get(v_inst_469_, 0);
    lean_inc_ref(v_toApplicative_471_);
    v_toBind_472_ = lean_ctor_get(v_inst_469_, 1);
    lean_inc(v_toBind_472_);
    lean_dec_ref(v_inst_469_);
    v_toPure_473_ = lean_ctor_get(v_toApplicative_471_, 1);
    lean_inc(v_toPure_473_);
    lean_dec_ref(v_toApplicative_471_);
    v___f_474_ = lean_alloc_closure(
        l_Lean_Internal_liftCoeM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_474_, 0, v_inst_468_);
    lean_closure_set(v___f_474_, 1, v_toPure_473_);
    v___x_475_ = lean_apply_4(
        v_toBind_472_,
        lean_box(0),
        lean_box(0),
        v_x_470_,
        v___f_474_,
    );
    return v___x_475_;
}
pub unsafe fn l_Lean_Internal_coeM(
    mut v_m_476_: *mut LeanObject,
    mut v_00_u03b1_477_: *mut LeanObject,
    mut v_00_u03b2_478_: *mut LeanObject,
    mut v_inst_479_: *mut LeanObject,
    mut v_inst_480_: *mut LeanObject,
    mut v_x_481_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_482_ = lean_ctor_get(v_inst_480_, 0);
    lean_inc_ref(v_toApplicative_482_);
    v_toBind_483_ = lean_ctor_get(v_inst_480_, 1);
    lean_inc(v_toBind_483_);
    lean_dec_ref(v_inst_480_);
    v_toPure_484_ = lean_ctor_get(v_toApplicative_482_, 1);
    lean_inc(v_toPure_484_);
    lean_dec_ref(v_toApplicative_482_);
    v___f_485_ = lean_alloc_closure(
        l_Lean_Internal_liftCoeM___redArg___lam__0 as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_485_, 0, v_inst_479_);
    lean_closure_set(v___f_485_, 1, v_toPure_484_);
    v___x_486_ = lean_apply_4(
        v_toBind_483_,
        lean_box(0),
        lean_box(0),
        v_x_481_,
        v___f_485_,
    );
    return v___x_486_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Coe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_boolToProp = _init_l_boolToProp();
    l_boolToSort = _init_l_boolToSort();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Coe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Coe(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Prelude(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Coe(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Coe(builtin);
}

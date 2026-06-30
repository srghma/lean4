// Lean compiler output
// Module: Init.Data.Range.Polymorphic.Nat
// Imports: Init.Data.Nat.Lemmas Init.Data.Range.Polymorphic.Instances Init.Data.Nat.MinMax Init.Omega Init.RCases
use crate::ffi::{lean_nat_add, lean_nat_dec_le, lean_nat_sub};
use crate::r#gen::Init::Data::Nat::Lemmas::{
    initialize_Init_Data_Nat_Lemmas, runtime_initialize_Init_Data_Nat_Lemmas,
};
use crate::r#gen::Init::Data::Nat::MinMax::{
    initialize_Init_Data_Nat_MinMax, runtime_initialize_Init_Data_Nat_MinMax,
};
use crate::r#gen::Init::Data::Range::Polymorphic::Instances::{
    initialize_Init_Data_Range_Polymorphic_Instances,
    runtime_initialize_Init_Data_Range_Polymorphic_Instances,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::RCases::{initialize_Init_RCases, runtime_initialize_Init_RCases};
pub static l_Std_PRange_instUpwardEnumerableNat___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instUpwardEnumerableNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instUpwardEnumerableNat___closed__1_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_PRange_instUpwardEnumerableNat___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instUpwardEnumerableNat___closed__2_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Std_PRange_instUpwardEnumerableNat___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__2_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instUpwardEnumerableNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instUpwardEnumerableNat___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instLeast_x3fNat___closed__0_value: leanh::LeanCtorObject<1> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 1,
        },
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Std_PRange_instLeast_x3fNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instLeast_x3fNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instLeast_x3fNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instLeast_x3fNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instHasSizeNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instHasSizeNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instHasSizeNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_PRange_instHasSizeNat__1___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_PRange_instHasSizeNat__1___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_PRange_instHasSizeNat__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_PRange_instHasSizeNat__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_PRange_instHasSizeNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Std_instHasRcoIntersectionNat___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Std_instHasRcoIntersectionNat___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__1___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__1___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__1___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__2___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__2___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__2___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__2___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__3___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__3___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__3___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__3___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__4___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__4___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__4___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__4___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__5___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__5___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__5___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__5___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__6___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__6___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__6___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__6___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Std_instHasRcoIntersectionNat__7___closed__0_value: leanh::LeanClosureObject<
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
    m_fun: l_Std_instHasRcoIntersectionNat__7___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Std_instHasRcoIntersectionNat__7___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__7___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Std_instHasRcoIntersectionNat__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Std_instHasRcoIntersectionNat__7___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Std_PRange_instUpwardEnumerableNat___lam__0(
    mut v_n_223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_224_ = leanh::lean_unsigned_to_nat(1);
    v___x_225_ = lean_nat_add(v_n_223_, v___x_224_);
    v___x_226_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_226_, 0, v___x_225_);
    return v___x_226_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableNat___lam__0___boxed(
    mut v_n_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_228_ = l_Std_PRange_instUpwardEnumerableNat___lam__0(v_n_227_);
    leanh::lean_dec(v_n_227_);
    return v_res_228_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableNat___lam__1(
    mut v_k_229_: *mut leanh::LeanObject,
    mut v_n_230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_231_ = lean_nat_add(v_n_230_, v_k_229_);
    v___x_232_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_232_, 0, v___x_231_);
    return v___x_232_;
}
pub unsafe fn l_Std_PRange_instUpwardEnumerableNat___lam__1___boxed(
    mut v_k_233_: *mut leanh::LeanObject,
    mut v_n_234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_235_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_235_ = l_Std_PRange_instUpwardEnumerableNat___lam__1(v_k_233_, v_n_234_);
    leanh::lean_dec(v_n_234_);
    leanh::lean_dec(v_k_233_);
    return v_res_235_;
}
pub unsafe fn l_Std_PRange_instHasSizeNat___lam__0(
    mut v_lo_245_: *mut leanh::LeanObject,
    mut v_hi_246_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_247_ = leanh::lean_unsigned_to_nat(1);
    v___x_248_ = lean_nat_add(v_hi_246_, v___x_247_);
    v___x_249_ = lean_nat_sub(v___x_248_, v_lo_245_);
    leanh::lean_dec(v___x_248_);
    return v___x_249_;
}
pub unsafe fn l_Std_PRange_instHasSizeNat___lam__0___boxed(
    mut v_lo_250_: *mut leanh::LeanObject,
    mut v_hi_251_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_252_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_252_ = l_Std_PRange_instHasSizeNat___lam__0(v_lo_250_, v_hi_251_);
    leanh::lean_dec(v_hi_251_);
    leanh::lean_dec(v_lo_250_);
    return v_res_252_;
}
pub unsafe fn l_Std_PRange_instHasSizeNat__1___lam__0(
    mut v_lo_255_: *mut leanh::LeanObject,
    mut v_hi_256_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_257_ = leanh::lean_unsigned_to_nat(1);
    v___x_258_ = lean_nat_add(v_hi_256_, v___x_257_);
    v___x_259_ = lean_nat_sub(v___x_258_, v_lo_255_);
    leanh::lean_dec(v___x_258_);
    v___x_260_ = lean_nat_sub(v___x_259_, v___x_257_);
    leanh::lean_dec(v___x_259_);
    return v___x_260_;
}
pub unsafe fn l_Std_PRange_instHasSizeNat__1___lam__0___boxed(
    mut v_lo_261_: *mut leanh::LeanObject,
    mut v_hi_262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_263_ = l_Std_PRange_instHasSizeNat__1___lam__0(v_lo_261_, v_hi_262_);
    leanh::lean_dec(v_hi_262_);
    leanh::lean_dec(v_lo_261_);
    return v_res_263_;
}
pub unsafe fn l_Std_instHasRcoIntersectionNat___lam__0(
    mut v_r_266_: *mut leanh::LeanObject,
    mut v_s_267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_274_: u8 = 0;
    let mut v___y_276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_277_: u8 = 0;
    let mut v___x_279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_286_: u8 = 0;
    let mut v_isSharedCheck_287_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_268_ = leanh::lean_ctor_get(v_r_266_, 0);
                v_upper_269_ = leanh::lean_ctor_get(v_r_266_, 1);
                v_lower_270_ = leanh::lean_ctor_get(v_s_267_, 0);
                v_upper_271_ = leanh::lean_ctor_get(v_s_267_, 1);
                v_isSharedCheck_287_ = (!leanh::lean_is_exclusive(v_s_267_)) as u8;
                if v_isSharedCheck_287_ == 0 {
                    v___x_273_ = v_s_267_;
                    v_isShared_274_ = v_isSharedCheck_287_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_271_);
                    leanh::lean_inc(v_lower_270_);
                    leanh::lean_dec(v_s_267_);
                    v___x_273_ = leanh::lean_box(0);
                    v_isShared_274_ = v_isSharedCheck_287_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_284_ = leanh::lean_unsigned_to_nat(1);
                v___x_285_ = lean_nat_add(v_lower_268_, v___x_284_);
                v___x_286_ = lean_nat_dec_le(v___x_285_, v_lower_270_);
                if v___x_286_ == 0 {
                    leanh::lean_dec(v_lower_270_);
                    v___y_276_ = v___x_285_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_285_);
                    v___y_276_ = v_lower_270_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_277_ = lean_nat_dec_le(v_upper_269_, v_upper_271_);
                if v___x_277_ == 0 {
                    if v_isShared_274_ == 0 {
                        leanh::lean_ctor_set(v___x_273_, 0, v___y_276_);
                        v___x_279_ = v___x_273_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_280_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_280_, 0, v___y_276_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_280_, 1, v_upper_271_);
                        v___x_279_ = v_reuseFailAlloc_280_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_271_);
                    leanh::lean_inc(v_upper_269_);
                    if v_isShared_274_ == 0 {
                        leanh::lean_ctor_set(v___x_273_, 1, v_upper_269_);
                        leanh::lean_ctor_set(v___x_273_, 0, v___y_276_);
                        v___x_282_ = v___x_273_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_283_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_283_, 0, v___y_276_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_283_, 1, v_upper_269_);
                        v___x_282_ = v_reuseFailAlloc_283_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_279_;
            }
            4 => {
                return v___x_282_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat___lam__0___boxed(
    mut v_r_288_: *mut leanh::LeanObject,
    mut v_s_289_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_290_ = l_Std_instHasRcoIntersectionNat___lam__0(v_r_288_, v_s_289_);
    leanh::lean_dec_ref(v_r_288_);
    return v_res_290_;
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__1___lam__0(
    mut v_r_293_: *mut leanh::LeanObject,
    mut v_s_294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_301_: u8 = 0;
    let mut v___x_302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_306_: u8 = 0;
    let mut v___x_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_314_: u8 = 0;
    let mut v_isSharedCheck_315_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_295_ = leanh::lean_ctor_get(v_r_293_, 0);
                v_upper_296_ = leanh::lean_ctor_get(v_r_293_, 1);
                v_lower_297_ = leanh::lean_ctor_get(v_s_294_, 0);
                v_upper_298_ = leanh::lean_ctor_get(v_s_294_, 1);
                v_isSharedCheck_315_ = (!leanh::lean_is_exclusive(v_s_294_)) as u8;
                if v_isSharedCheck_315_ == 0 {
                    v___x_300_ = v_s_294_;
                    v_isShared_301_ = v_isSharedCheck_315_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_298_);
                    leanh::lean_inc(v_lower_297_);
                    leanh::lean_dec(v_s_294_);
                    v___x_300_ = leanh::lean_box(0);
                    v_isShared_301_ = v_isSharedCheck_315_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_302_ = leanh::lean_unsigned_to_nat(1);
                v___x_313_ = lean_nat_add(v_lower_295_, v___x_302_);
                v___x_314_ = lean_nat_dec_le(v___x_313_, v_lower_297_);
                if v___x_314_ == 0 {
                    leanh::lean_dec(v_lower_297_);
                    v___y_304_ = v___x_313_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v___x_313_);
                    v___y_304_ = v_lower_297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_305_ = lean_nat_add(v_upper_296_, v___x_302_);
                v___x_306_ = lean_nat_dec_le(v___x_305_, v_upper_298_);
                if v___x_306_ == 0 {
                    leanh::lean_dec(v___x_305_);
                    if v_isShared_301_ == 0 {
                        leanh::lean_ctor_set(v___x_300_, 0, v___y_304_);
                        v___x_308_ = v___x_300_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_309_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_309_, 0, v___y_304_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_309_, 1, v_upper_298_);
                        v___x_308_ = v_reuseFailAlloc_309_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_298_);
                    if v_isShared_301_ == 0 {
                        leanh::lean_ctor_set(v___x_300_, 1, v___x_305_);
                        leanh::lean_ctor_set(v___x_300_, 0, v___y_304_);
                        v___x_311_ = v___x_300_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_312_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_312_, 0, v___y_304_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_312_, 1, v___x_305_);
                        v___x_311_ = v_reuseFailAlloc_312_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_308_;
            }
            4 => {
                return v___x_311_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__1___lam__0___boxed(
    mut v_r_316_: *mut leanh::LeanObject,
    mut v_s_317_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_318_ = l_Std_instHasRcoIntersectionNat__1___lam__0(v_r_316_, v_s_317_);
    leanh::lean_dec_ref(v_r_316_);
    return v_res_318_;
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__2___lam__0(
    mut v_r_321_: *mut leanh::LeanObject,
    mut v_s_322_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_327_: u8 = 0;
    let mut v___x_328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: u8 = 0;
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_337_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_323_ = leanh::lean_ctor_get(v_s_322_, 0);
                v_upper_324_ = leanh::lean_ctor_get(v_s_322_, 1);
                v_isSharedCheck_337_ = (!leanh::lean_is_exclusive(v_s_322_)) as u8;
                if v_isSharedCheck_337_ == 0 {
                    v___x_326_ = v_s_322_;
                    v_isShared_327_ = v_isSharedCheck_337_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_324_);
                    leanh::lean_inc(v_lower_323_);
                    leanh::lean_dec(v_s_322_);
                    v___x_326_ = leanh::lean_box(0);
                    v_isShared_327_ = v_isSharedCheck_337_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_328_ = leanh::lean_unsigned_to_nat(1);
                v___x_329_ = lean_nat_add(v_r_321_, v___x_328_);
                v___x_330_ = lean_nat_dec_le(v___x_329_, v_lower_323_);
                if v___x_330_ == 0 {
                    leanh::lean_dec(v_lower_323_);
                    if v_isShared_327_ == 0 {
                        leanh::lean_ctor_set(v___x_326_, 0, v___x_329_);
                        v___x_332_ = v___x_326_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_333_, 0, v___x_329_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_333_, 1, v_upper_324_);
                        v___x_332_ = v_reuseFailAlloc_333_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_329_);
                    if v_isShared_327_ == 0 {
                        v___x_335_ = v___x_326_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_336_, 0, v_lower_323_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_336_, 1, v_upper_324_);
                        v___x_335_ = v_reuseFailAlloc_336_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_332_;
            }
            3 => {
                return v___x_335_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__2___lam__0___boxed(
    mut v_r_338_: *mut leanh::LeanObject,
    mut v_s_339_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_340_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_340_ = l_Std_instHasRcoIntersectionNat__2___lam__0(v_r_338_, v_s_339_);
    leanh::lean_dec(v_r_338_);
    return v_res_340_;
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__3___lam__0(
    mut v_r_343_: *mut leanh::LeanObject,
    mut v_s_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_351_: u8 = 0;
    let mut v___y_353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_354_: u8 = 0;
    let mut v___x_356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_361_: u8 = 0;
    let mut v_isSharedCheck_362_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_345_ = leanh::lean_ctor_get(v_r_343_, 0);
                leanh::lean_inc(v_lower_345_);
                v_upper_346_ = leanh::lean_ctor_get(v_r_343_, 1);
                leanh::lean_inc(v_upper_346_);
                leanh::lean_dec_ref(v_r_343_);
                v_lower_347_ = leanh::lean_ctor_get(v_s_344_, 0);
                v_upper_348_ = leanh::lean_ctor_get(v_s_344_, 1);
                v_isSharedCheck_362_ = (!leanh::lean_is_exclusive(v_s_344_)) as u8;
                if v_isSharedCheck_362_ == 0 {
                    v___x_350_ = v_s_344_;
                    v_isShared_351_ = v_isSharedCheck_362_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_348_);
                    leanh::lean_inc(v_lower_347_);
                    leanh::lean_dec(v_s_344_);
                    v___x_350_ = leanh::lean_box(0);
                    v_isShared_351_ = v_isSharedCheck_362_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_361_ = lean_nat_dec_le(v_lower_345_, v_lower_347_);
                if v___x_361_ == 0 {
                    leanh::lean_dec(v_lower_347_);
                    v___y_353_ = v_lower_345_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_lower_345_);
                    v___y_353_ = v_lower_347_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_354_ = lean_nat_dec_le(v_upper_346_, v_upper_348_);
                if v___x_354_ == 0 {
                    leanh::lean_dec(v_upper_346_);
                    if v_isShared_351_ == 0 {
                        leanh::lean_ctor_set(v___x_350_, 0, v___y_353_);
                        v___x_356_ = v___x_350_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_357_, 0, v___y_353_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_357_, 1, v_upper_348_);
                        v___x_356_ = v_reuseFailAlloc_357_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_348_);
                    if v_isShared_351_ == 0 {
                        leanh::lean_ctor_set(v___x_350_, 1, v_upper_346_);
                        leanh::lean_ctor_set(v___x_350_, 0, v___y_353_);
                        v___x_359_ = v___x_350_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_360_, 0, v___y_353_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_360_, 1, v_upper_346_);
                        v___x_359_ = v_reuseFailAlloc_360_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_356_;
            }
            4 => {
                return v___x_359_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__4___lam__0(
    mut v_r_365_: *mut leanh::LeanObject,
    mut v_s_366_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_373_: u8 = 0;
    let mut v___y_375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_378_: u8 = 0;
    let mut v___x_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_385_: u8 = 0;
    let mut v_isSharedCheck_386_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_367_ = leanh::lean_ctor_get(v_r_365_, 0);
                leanh::lean_inc(v_lower_367_);
                v_upper_368_ = leanh::lean_ctor_get(v_r_365_, 1);
                leanh::lean_inc(v_upper_368_);
                leanh::lean_dec_ref(v_r_365_);
                v_lower_369_ = leanh::lean_ctor_get(v_s_366_, 0);
                v_upper_370_ = leanh::lean_ctor_get(v_s_366_, 1);
                v_isSharedCheck_386_ = (!leanh::lean_is_exclusive(v_s_366_)) as u8;
                if v_isSharedCheck_386_ == 0 {
                    v___x_372_ = v_s_366_;
                    v_isShared_373_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_370_);
                    leanh::lean_inc(v_lower_369_);
                    leanh::lean_dec(v_s_366_);
                    v___x_372_ = leanh::lean_box(0);
                    v_isShared_373_ = v_isSharedCheck_386_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_385_ = lean_nat_dec_le(v_lower_367_, v_lower_369_);
                if v___x_385_ == 0 {
                    leanh::lean_dec(v_lower_369_);
                    v___y_375_ = v_lower_367_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_lower_367_);
                    v___y_375_ = v_lower_369_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_376_ = leanh::lean_unsigned_to_nat(1);
                v___x_377_ = lean_nat_add(v_upper_368_, v___x_376_);
                leanh::lean_dec(v_upper_368_);
                v___x_378_ = lean_nat_dec_le(v___x_377_, v_upper_370_);
                if v___x_378_ == 0 {
                    leanh::lean_dec(v___x_377_);
                    if v_isShared_373_ == 0 {
                        leanh::lean_ctor_set(v___x_372_, 0, v___y_375_);
                        v___x_380_ = v___x_372_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_381_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_381_, 0, v___y_375_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_381_, 1, v_upper_370_);
                        v___x_380_ = v_reuseFailAlloc_381_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_370_);
                    if v_isShared_373_ == 0 {
                        leanh::lean_ctor_set(v___x_372_, 1, v___x_377_);
                        leanh::lean_ctor_set(v___x_372_, 0, v___y_375_);
                        v___x_383_ = v___x_372_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_384_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_384_, 0, v___y_375_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_377_);
                        v___x_383_ = v_reuseFailAlloc_384_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_380_;
            }
            4 => {
                return v___x_383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__5___lam__0(
    mut v_r_389_: *mut leanh::LeanObject,
    mut v_s_390_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_395_: u8 = 0;
    let mut v___x_396_: u8 = 0;
    let mut v___x_398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_403_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_391_ = leanh::lean_ctor_get(v_s_390_, 0);
                v_upper_392_ = leanh::lean_ctor_get(v_s_390_, 1);
                v_isSharedCheck_403_ = (!leanh::lean_is_exclusive(v_s_390_)) as u8;
                if v_isSharedCheck_403_ == 0 {
                    v___x_394_ = v_s_390_;
                    v_isShared_395_ = v_isSharedCheck_403_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_392_);
                    leanh::lean_inc(v_lower_391_);
                    leanh::lean_dec(v_s_390_);
                    v___x_394_ = leanh::lean_box(0);
                    v_isShared_395_ = v_isSharedCheck_403_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_396_ = lean_nat_dec_le(v_r_389_, v_lower_391_);
                if v___x_396_ == 0 {
                    leanh::lean_dec(v_lower_391_);
                    if v_isShared_395_ == 0 {
                        leanh::lean_ctor_set(v___x_394_, 0, v_r_389_);
                        v___x_398_ = v___x_394_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_399_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_399_, 0, v_r_389_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_399_, 1, v_upper_392_);
                        v___x_398_ = v_reuseFailAlloc_399_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_r_389_);
                    if v_isShared_395_ == 0 {
                        v___x_401_ = v___x_394_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_402_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_402_, 0, v_lower_391_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_402_, 1, v_upper_392_);
                        v___x_401_ = v_reuseFailAlloc_402_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_398_;
            }
            3 => {
                return v___x_401_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__6___lam__0(
    mut v_r_406_: *mut leanh::LeanObject,
    mut v_s_407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_412_: u8 = 0;
    let mut v___x_413_: u8 = 0;
    let mut v___x_415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_420_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_408_ = leanh::lean_ctor_get(v_s_407_, 0);
                v_upper_409_ = leanh::lean_ctor_get(v_s_407_, 1);
                v_isSharedCheck_420_ = (!leanh::lean_is_exclusive(v_s_407_)) as u8;
                if v_isSharedCheck_420_ == 0 {
                    v___x_411_ = v_s_407_;
                    v_isShared_412_ = v_isSharedCheck_420_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_409_);
                    leanh::lean_inc(v_lower_408_);
                    leanh::lean_dec(v_s_407_);
                    v___x_411_ = leanh::lean_box(0);
                    v_isShared_412_ = v_isSharedCheck_420_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_413_ = lean_nat_dec_le(v_r_406_, v_upper_409_);
                if v___x_413_ == 0 {
                    leanh::lean_dec(v_r_406_);
                    if v_isShared_412_ == 0 {
                        v___x_415_ = v___x_411_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_416_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_416_, 0, v_lower_408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_416_, 1, v_upper_409_);
                        v___x_415_ = v_reuseFailAlloc_416_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_409_);
                    if v_isShared_412_ == 0 {
                        leanh::lean_ctor_set(v___x_411_, 1, v_r_406_);
                        v___x_418_ = v___x_411_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_419_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_419_, 0, v_lower_408_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_419_, 1, v_r_406_);
                        v___x_418_ = v_reuseFailAlloc_419_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_415_;
            }
            3 => {
                return v___x_418_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__7___lam__0(
    mut v_r_423_: *mut leanh::LeanObject,
    mut v_s_424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_lower_425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_429_: u8 = 0;
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_432_: u8 = 0;
    let mut v___x_434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_439_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_lower_425_ = leanh::lean_ctor_get(v_s_424_, 0);
                v_upper_426_ = leanh::lean_ctor_get(v_s_424_, 1);
                v_isSharedCheck_439_ = (!leanh::lean_is_exclusive(v_s_424_)) as u8;
                if v_isSharedCheck_439_ == 0 {
                    v___x_428_ = v_s_424_;
                    v_isShared_429_ = v_isSharedCheck_439_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_upper_426_);
                    leanh::lean_inc(v_lower_425_);
                    leanh::lean_dec(v_s_424_);
                    v___x_428_ = leanh::lean_box(0);
                    v_isShared_429_ = v_isSharedCheck_439_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_430_ = leanh::lean_unsigned_to_nat(1);
                v___x_431_ = lean_nat_add(v_r_423_, v___x_430_);
                v___x_432_ = lean_nat_dec_le(v___x_431_, v_upper_426_);
                if v___x_432_ == 0 {
                    leanh::lean_dec(v___x_431_);
                    if v_isShared_429_ == 0 {
                        v___x_434_ = v___x_428_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_435_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_435_, 0, v_lower_425_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_435_, 1, v_upper_426_);
                        v___x_434_ = v_reuseFailAlloc_435_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_upper_426_);
                    if v_isShared_429_ == 0 {
                        leanh::lean_ctor_set(v___x_428_, 1, v___x_431_);
                        v___x_437_ = v___x_428_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_438_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_438_, 0, v_lower_425_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_438_, 1, v___x_431_);
                        v___x_437_ = v_reuseFailAlloc_438_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_434_;
            }
            3 => {
                return v___x_437_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_instHasRcoIntersectionNat__7___lam__0___boxed(
    mut v_r_440_: *mut leanh::LeanObject,
    mut v_s_441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_442_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_442_ = l_Std_instHasRcoIntersectionNat__7___lam__0(v_r_440_, v_s_441_);
    leanh::lean_dec(v_r_440_);
    return v_res_442_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Range_Polymorphic_Nat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Range_Polymorphic_Nat(
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
pub unsafe fn initialize_Init_Data_Range_Polymorphic_Nat(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Nat_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Instances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_MinMax(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_RCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Range_Polymorphic_Nat(builtin);
}
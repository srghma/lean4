// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Proj
// Imports: Lean.Meta.Tactic.Grind.Types
use crate::ffi::{
    lean_array_fget, lean_array_push, lean_grind_internalize, lean_mk_array, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get, lean_st_ref_set,
    lean_st_ref_take,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::l_Lean_Name_append;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_app___override,
    l_Lean_Expr_appArg_x21, l_Lean_Expr_appFn_x21, l_Lean_Expr_getAppFn, l_Lean_Expr_getAppNumArgs,
    l_Lean_Expr_getRevArg_x21, l_Lean_Expr_isAppOf, l_Lean_Expr_sort___override, l_Lean_mkAppN,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofExpr;
use crate::r#gen::Lean::Meta::AppBuilder::{
    l_Lean_Meta_mkEq, l_Lean_Meta_mkEqRefl, l_Lean_Meta_mkExpectedPropHint,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Sym::SymM::l_Lean_Meta_Sym_shareCommon___redArg;
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    initialize_Lean_Meta_Tactic_Grind_Types, l_Lean_Meta_Grind_getGeneration___redArg,
    l_Lean_Meta_Grind_getRootENode___redArg, l_Lean_Meta_Grind_isCongrRoot___redArg,
    l_Lean_Meta_Grind_pushEqCore___redArg, l_Lean_Meta_Grind_updateLastTag,
    runtime_initialize_Lean_Meta_Tactic_Grind_Types,
};
use crate::r#gen::Lean::ProjFns::l_Lean_Environment_getProjectionFnInfo_x3f;
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateProjEq___closed__0_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [103, 114, 105, 110, 100, 0],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateProjEq___closed__1_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [100, 101, 98, 117, 103, 0],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateProjEq___closed__2_value: leanh::LeanStringObject<5> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 5,
        m_capacity: 5,
        m_length: 4,
        m_data: [112, 114, 111, 106, 0],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_0: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__0_value)
                as *mut leanh::LeanObject,
            15947788021050471391 as *mut leanh::LeanObject,
        ],
    };
static l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_1: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_0)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__1_value)
                as *mut leanh::LeanObject,
            5637236024813792860 as *mut leanh::LeanObject,
        ],
    };
pub static l_Lean_Meta_Grind_propagateProjEq___closed__3_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__3_value_aux_1)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__2_value)
                as *mut leanh::LeanObject,
            11850799392639992908 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateProjEq___closed__4_value: leanh::LeanStringObject<6> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 6,
        m_capacity: 6,
        m_length: 5,
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Grind_propagateProjEq___closed__5_value: leanh::LeanCtorObject<3> =
    leanh::LeanCtorObject {
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
            core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__4_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Grind_propagateProjEq___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_propagateProjEq___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_propagateProjEq___closed__8_value: leanh::LeanArrayObject<0> =
    leanh::LeanArrayObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_Meta_Grind_propagateProjEq___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_propagateProjEq___closed__8_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(
    mut v_declName_407_: *mut leanh::LeanObject,
    mut v___y_408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_413_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_410_ = lean_st_ref_get(v___y_408_);
    v_env_411_ = leanh::lean_ctor_get(v___x_410_, 0);
    leanh::lean_inc_ref(v_env_411_);
    leanh::lean_dec(v___x_410_);
    v___x_412_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_411_, v_declName_407_);
    v___x_413_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_413_, 0, v___x_412_);
    return v___x_413_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg___boxed(
    mut v_declName_414_: *mut leanh::LeanObject,
    mut v___y_415_: *mut leanh::LeanObject,
    mut v___y_416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_417_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(
            v_declName_414_,
            v___y_415_,
        );
    leanh::lean_dec(v___y_415_);
    return v_res_417_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(
    mut v_declName_418_: *mut leanh::LeanObject,
    mut v___y_419_: *mut leanh::LeanObject,
    mut v___y_420_: *mut leanh::LeanObject,
    mut v___y_421_: *mut leanh::LeanObject,
    mut v___y_422_: *mut leanh::LeanObject,
    mut v___y_423_: *mut leanh::LeanObject,
    mut v___y_424_: *mut leanh::LeanObject,
    mut v___y_425_: *mut leanh::LeanObject,
    mut v___y_426_: *mut leanh::LeanObject,
    mut v___y_427_: *mut leanh::LeanObject,
    mut v___y_428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_430_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_430_ =
        l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(
            v_declName_418_,
            v___y_428_,
        );
    return v___x_430_;
}
pub unsafe fn l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___boxed(
    mut v_declName_431_: *mut leanh::LeanObject,
    mut v___y_432_: *mut leanh::LeanObject,
    mut v___y_433_: *mut leanh::LeanObject,
    mut v___y_434_: *mut leanh::LeanObject,
    mut v___y_435_: *mut leanh::LeanObject,
    mut v___y_436_: *mut leanh::LeanObject,
    mut v___y_437_: *mut leanh::LeanObject,
    mut v___y_438_: *mut leanh::LeanObject,
    mut v___y_439_: *mut leanh::LeanObject,
    mut v___y_440_: *mut leanh::LeanObject,
    mut v___y_441_: *mut leanh::LeanObject,
    mut v___y_442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_443_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0(
        v_declName_431_,
        v___y_432_,
        v___y_433_,
        v___y_434_,
        v___y_435_,
        v___y_436_,
        v___y_437_,
        v___y_438_,
        v___y_439_,
        v___y_440_,
        v___y_441_,
    );
    leanh::lean_dec(v___y_441_);
    leanh::lean_dec_ref(v___y_440_);
    leanh::lean_dec(v___y_439_);
    leanh::lean_dec_ref(v___y_438_);
    leanh::lean_dec(v___y_437_);
    leanh::lean_dec_ref(v___y_436_);
    leanh::lean_dec(v___y_435_);
    leanh::lean_dec_ref(v___y_434_);
    leanh::lean_dec(v___y_433_);
    leanh::lean_dec(v___y_432_);
    return v_res_443_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(
    mut v_a_444_: *mut leanh::LeanObject,
    mut v_b_445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_array_446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_451_: u8 = 0;
    let mut v___x_452_: u8 = 0;
    let mut v___x_453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_461_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_446_ = leanh::lean_ctor_get(v_a_444_, 0);
                v_start_447_ = leanh::lean_ctor_get(v_a_444_, 1);
                v_stop_448_ = leanh::lean_ctor_get(v_a_444_, 2);
                v_isSharedCheck_461_ = (!leanh::lean_is_exclusive(v_a_444_)) as u8;
                if v_isSharedCheck_461_ == 0 {
                    v___x_450_ = v_a_444_;
                    v_isShared_451_ = v_isSharedCheck_461_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_stop_448_);
                    leanh::lean_inc(v_start_447_);
                    leanh::lean_inc(v_array_446_);
                    leanh::lean_dec(v_a_444_);
                    v___x_450_ = leanh::lean_box(0);
                    v_isShared_451_ = v_isSharedCheck_461_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_452_ = lean_nat_dec_lt(v_start_447_, v_stop_448_);
                if v___x_452_ == 0 {
                    leanh::lean_del_object(v___x_450_);
                    leanh::lean_dec(v_stop_448_);
                    leanh::lean_dec(v_start_447_);
                    leanh::lean_dec_ref(v_array_446_);
                    return v_b_445_;
                } else {
                    v___x_453_ = leanh::lean_unsigned_to_nat(1);
                    v___x_454_ = lean_nat_add(v_start_447_, v___x_453_);
                    leanh::lean_inc_ref(v_array_446_);
                    if v_isShared_451_ == 0 {
                        leanh::lean_ctor_set(v___x_450_, 1, v___x_454_);
                        v___x_456_ = v___x_450_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_460_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_460_, 0, v_array_446_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_454_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_460_, 2, v_stop_448_);
                        v___x_456_ = v_reuseFailAlloc_460_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_457_ = lean_array_fget(v_array_446_, v_start_447_);
                leanh::lean_dec(v_start_447_);
                leanh::lean_dec_ref(v_array_446_);
                v___x_458_ = lean_array_push(v_b_445_, v___x_457_);
                v_a_444_ = v___x_456_;
                v_b_445_ = v___x_458_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(
    mut v_msgData_462_: *mut leanh::LeanObject,
    mut v___y_463_: *mut leanh::LeanObject,
    mut v___y_464_: *mut leanh::LeanObject,
    mut v___y_465_: *mut leanh::LeanObject,
    mut v___y_466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_468_ = lean_st_ref_get(v___y_466_);
    v_env_469_ = leanh::lean_ctor_get(v___x_468_, 0);
    leanh::lean_inc_ref(v_env_469_);
    leanh::lean_dec(v___x_468_);
    v___x_470_ = lean_st_ref_get(v___y_464_);
    v_mctx_471_ = leanh::lean_ctor_get(v___x_470_, 0);
    leanh::lean_inc_ref(v_mctx_471_);
    leanh::lean_dec(v___x_470_);
    v_lctx_472_ = leanh::lean_ctor_get(v___y_463_, 2);
    v_options_473_ = leanh::lean_ctor_get(v___y_465_, 2);
    leanh::lean_inc_ref(v_options_473_);
    leanh::lean_inc_ref(v_lctx_472_);
    v___x_474_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_474_, 0, v_env_469_);
    leanh::lean_ctor_set(v___x_474_, 1, v_mctx_471_);
    leanh::lean_ctor_set(v___x_474_, 2, v_lctx_472_);
    leanh::lean_ctor_set(v___x_474_, 3, v_options_473_);
    v___x_475_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_475_, 0, v___x_474_);
    leanh::lean_ctor_set(v___x_475_, 1, v_msgData_462_);
    v___x_476_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_476_, 0, v___x_475_);
    return v___x_476_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1___boxed(
    mut v_msgData_477_: *mut leanh::LeanObject,
    mut v___y_478_: *mut leanh::LeanObject,
    mut v___y_479_: *mut leanh::LeanObject,
    mut v___y_480_: *mut leanh::LeanObject,
    mut v___y_481_: *mut leanh::LeanObject,
    mut v___y_482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_483_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_483_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msgData_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_);
    leanh::lean_dec(v___y_481_);
    leanh::lean_dec_ref(v___y_480_);
    leanh::lean_dec(v___y_479_);
    leanh::lean_dec_ref(v___y_478_);
    return v_res_483_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0()
-> f64 {
    let mut v___x_484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_485_: f64 = 0.0;
    v___x_484_ = leanh::lean_unsigned_to_nat(0);
    v___x_485_ = lean_float_of_nat(v___x_484_);
    return v___x_485_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(
    mut v_cls_489_: *mut leanh::LeanObject,
    mut v_msg_490_: *mut leanh::LeanObject,
    mut v___y_491_: *mut leanh::LeanObject,
    mut v___y_492_: *mut leanh::LeanObject,
    mut v___y_493_: *mut leanh::LeanObject,
    mut v___y_494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_501_: u8 = 0;
    let mut v___x_502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_514_: u8 = 0;
    let mut v_tid_515_: u64 = 0;
    let mut v_traces_516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_519_: u8 = 0;
    let mut v___x_520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_521_: f64 = 0.0;
    let mut v___x_522_: u8 = 0;
    let mut v___x_523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_540_: u8 = 0;
    let mut v_isSharedCheck_541_: u8 = 0;
    let mut v_isSharedCheck_542_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_496_ = leanh::lean_ctor_get(v___y_493_, 5);
                v___x_497_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1_spec__1(v_msg_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
                v_a_498_ = leanh::lean_ctor_get(v___x_497_, 0);
                v_isSharedCheck_542_ = (!leanh::lean_is_exclusive(v___x_497_)) as u8;
                if v_isSharedCheck_542_ == 0 {
                    v___x_500_ = v___x_497_;
                    v_isShared_501_ = v_isSharedCheck_542_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_498_);
                    leanh::lean_dec(v___x_497_);
                    v___x_500_ = leanh::lean_box(0);
                    v_isShared_501_ = v_isSharedCheck_542_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_502_ = lean_st_ref_take(v___y_494_);
                v_traceState_503_ = leanh::lean_ctor_get(v___x_502_, 4);
                v_env_504_ = leanh::lean_ctor_get(v___x_502_, 0);
                v_nextMacroScope_505_ = leanh::lean_ctor_get(v___x_502_, 1);
                v_ngen_506_ = leanh::lean_ctor_get(v___x_502_, 2);
                v_auxDeclNGen_507_ = leanh::lean_ctor_get(v___x_502_, 3);
                v_cache_508_ = leanh::lean_ctor_get(v___x_502_, 5);
                v_messages_509_ = leanh::lean_ctor_get(v___x_502_, 6);
                v_infoState_510_ = leanh::lean_ctor_get(v___x_502_, 7);
                v_snapshotTasks_511_ = leanh::lean_ctor_get(v___x_502_, 8);
                v_isSharedCheck_541_ = (!leanh::lean_is_exclusive(v___x_502_)) as u8;
                if v_isSharedCheck_541_ == 0 {
                    v___x_513_ = v___x_502_;
                    v_isShared_514_ = v_isSharedCheck_541_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_511_);
                    leanh::lean_inc(v_infoState_510_);
                    leanh::lean_inc(v_messages_509_);
                    leanh::lean_inc(v_cache_508_);
                    leanh::lean_inc(v_traceState_503_);
                    leanh::lean_inc(v_auxDeclNGen_507_);
                    leanh::lean_inc(v_ngen_506_);
                    leanh::lean_inc(v_nextMacroScope_505_);
                    leanh::lean_inc(v_env_504_);
                    leanh::lean_dec(v___x_502_);
                    v___x_513_ = leanh::lean_box(0);
                    v_isShared_514_ = v_isSharedCheck_541_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_515_ = leanh::lean_ctor_get_uint64(
                    v_traceState_503_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_516_ = leanh::lean_ctor_get(v_traceState_503_, 0);
                v_isSharedCheck_540_ = (!leanh::lean_is_exclusive(v_traceState_503_)) as u8;
                if v_isSharedCheck_540_ == 0 {
                    v___x_518_ = v_traceState_503_;
                    v_isShared_519_ = v_isSharedCheck_540_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_516_);
                    leanh::lean_dec(v_traceState_503_);
                    v___x_518_ = leanh::lean_box(0);
                    v_isShared_519_ = v_isSharedCheck_540_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_520_ = leanh::lean_box(0);
                v___x_521_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__0);
                v___x_522_ = 0;
                v___x_523_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__1;
                v___x_524_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_524_, 0, v_cls_489_);
                leanh::lean_ctor_set(v___x_524_, 1, v___x_520_);
                leanh::lean_ctor_set(v___x_524_, 2, v___x_523_);
                leanh::lean_ctor_set_float(
                    v___x_524_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_521_,
                );
                leanh::lean_ctor_set_float(
                    v___x_524_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_521_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_524_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_522_,
                );
                v___x_525_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___closed__2;
                v___x_526_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_526_, 0, v___x_524_);
                leanh::lean_ctor_set(v___x_526_, 1, v_a_498_);
                leanh::lean_ctor_set(v___x_526_, 2, v___x_525_);
                leanh::lean_inc(v_ref_496_);
                v___x_527_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_527_, 0, v_ref_496_);
                leanh::lean_ctor_set(v___x_527_, 1, v___x_526_);
                v___x_528_ = l_Lean_PersistentArray_push___redArg(v_traces_516_, v___x_527_);
                if v_isShared_519_ == 0 {
                    leanh::lean_ctor_set(v___x_518_, 0, v___x_528_);
                    v___x_530_ = v___x_518_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_539_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_539_, 0, v___x_528_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_539_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_515_,
                    );
                    v___x_530_ = v_reuseFailAlloc_539_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_514_ == 0 {
                    leanh::lean_ctor_set(v___x_513_, 4, v___x_530_);
                    v___x_532_ = v___x_513_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_538_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 0, v_env_504_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 1, v_nextMacroScope_505_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 2, v_ngen_506_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 3, v_auxDeclNGen_507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 4, v___x_530_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 5, v_cache_508_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 6, v_messages_509_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 7, v_infoState_510_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_538_, 8, v_snapshotTasks_511_);
                    v___x_532_ = v_reuseFailAlloc_538_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_533_ = lean_st_ref_set(v___y_494_, v___x_532_);
                v___x_534_ = leanh::lean_box(0);
                if v_isShared_501_ == 0 {
                    leanh::lean_ctor_set(v___x_500_, 0, v___x_534_);
                    v___x_536_ = v___x_500_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_537_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_537_, 0, v___x_534_);
                    v___x_536_ = v_reuseFailAlloc_537_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg___boxed(
    mut v_cls_543_: *mut leanh::LeanObject,
    mut v_msg_544_: *mut leanh::LeanObject,
    mut v___y_545_: *mut leanh::LeanObject,
    mut v___y_546_: *mut leanh::LeanObject,
    mut v___y_547_: *mut leanh::LeanObject,
    mut v___y_548_: *mut leanh::LeanObject,
    mut v___y_549_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_550_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(
        v_cls_543_, v_msg_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_,
    );
    leanh::lean_dec(v___y_548_);
    leanh::lean_dec_ref(v___y_547_);
    leanh::lean_dec(v___y_546_);
    leanh::lean_dec_ref(v___y_545_);
    return v_res_550_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateProjEq___closed__6() -> *mut leanh::LeanObject
{
    let mut v___x_561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_563_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_561_ = l_Lean_Meta_Grind_propagateProjEq___closed__3;
    v___x_562_ = l_Lean_Meta_Grind_propagateProjEq___closed__5;
    v___x_563_ = l_Lean_Name_append(v___x_562_, v___x_561_);
    return v___x_563_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_propagateProjEq___closed__7() -> *mut leanh::LeanObject
{
    let mut v___x_564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_564_ = leanh::lean_box(0);
    v_dummy_565_ = l_Lean_Expr_sort___override(v___x_564_);
    return v_dummy_565_;
}
pub unsafe fn l_Lean_Meta_Grind_propagateProjEq(
    mut v_parent_568_: *mut leanh::LeanObject,
    mut v_a_569_: *mut leanh::LeanObject,
    mut v_a_570_: *mut leanh::LeanObject,
    mut v_a_571_: *mut leanh::LeanObject,
    mut v_a_572_: *mut leanh::LeanObject,
    mut v_a_573_: *mut leanh::LeanObject,
    mut v_a_574_: *mut leanh::LeanObject,
    mut v_a_575_: *mut leanh::LeanObject,
    mut v_a_576_: *mut leanh::LeanObject,
    mut v_a_577_: *mut leanh::LeanObject,
    mut v_a_578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_projFn_580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_586_: u8 = 0;
    let mut v_val_587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: u8 = 0;
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_603_: u8 = 0;
    let mut v___x_604_: u8 = 0;
    let mut v___x_605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_614_: u8 = 0;
    let mut v_self_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_heqProofs_616_: u8 = 0;
    let mut v___y_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_627_: u8 = 0;
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_640_: u8 = 0;
    let mut v___x_641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_645_: u8 = 0;
    let mut v___x_647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_649_: u8 = 0;
    let mut v_a_650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_653_: u8 = 0;
    let mut v___x_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_657_: u8 = 0;
    let mut v_parentNew_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_671_: u8 = 0;
    let mut v_inheritedTraceOptions_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_675_: u8 = 0;
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_parentNew_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_698_: u8 = 0;
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_702_: u8 = 0;
    let mut v___x_703_: u8 = 0;
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: u8 = 0;
    let mut v___x_709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_716_: u8 = 0;
    let mut v___x_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_720_: u8 = 0;
    let mut v_dummy_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_737_: u8 = 0;
    let mut v___x_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_741_: u8 = 0;
    let mut v_isSharedCheck_742_: u8 = 0;
    let mut v_a_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_746_: u8 = 0;
    let mut v___x_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v_isSharedCheck_751_: u8 = 0;
    let mut v_a_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_755_: u8 = 0;
    let mut v___x_757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_759_: u8 = 0;
    let mut v___x_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_764_: u8 = 0;
    let mut v___x_765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_projFn_580_ = l_Lean_Expr_getAppFn(v_parent_568_);
                if leanh::lean_obj_tag(v_projFn_580_) == 4 {
                    v_declName_581_ = leanh::lean_ctor_get(v_projFn_580_, 0);
                    leanh::lean_inc(v_declName_581_);
                    v___x_582_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_Grind_propagateProjEq_spec__0___redArg(v_declName_581_, v_a_578_);
                    v_a_583_ = leanh::lean_ctor_get(v___x_582_, 0);
                    v_isSharedCheck_764_ = (!leanh::lean_is_exclusive(v___x_582_)) as u8;
                    if v_isSharedCheck_764_ == 0 {
                        v___x_585_ = v___x_582_;
                        v_isShared_586_ = v_isSharedCheck_764_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_583_);
                        leanh::lean_dec(v___x_582_);
                        v___x_585_ = leanh::lean_box(0);
                        v_isShared_586_ = v_isSharedCheck_764_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_projFn_580_);
                    leanh::lean_dec_ref(v_parent_568_);
                    v___x_765_ = leanh::lean_box(0);
                    v___x_766_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_766_, 0, v___x_765_);
                    return v___x_766_;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_583_) == 1 {
                    v_val_587_ = leanh::lean_ctor_get(v_a_583_, 0);
                    leanh::lean_inc(v_val_587_);
                    leanh::lean_dec_ref_known(v_a_583_, 1);
                    v_ctorName_588_ = leanh::lean_ctor_get(v_val_587_, 0);
                    leanh::lean_inc(v_ctorName_588_);
                    v_numParams_589_ = leanh::lean_ctor_get(v_val_587_, 1);
                    leanh::lean_inc(v_numParams_589_);
                    v_i_590_ = leanh::lean_ctor_get(v_val_587_, 2);
                    leanh::lean_inc(v_i_590_);
                    leanh::lean_dec(v_val_587_);
                    v___x_591_ = leanh::lean_unsigned_to_nat(1);
                    v___x_592_ = lean_nat_add(v_numParams_589_, v___x_591_);
                    v___x_593_ = l_Lean_Expr_getAppNumArgs(v_parent_568_);
                    v___x_594_ = lean_nat_dec_eq(v___x_592_, v___x_593_);
                    leanh::lean_dec(v___x_593_);
                    leanh::lean_dec(v___x_592_);
                    if v___x_594_ == 0 {
                        leanh::lean_dec(v_i_590_);
                        leanh::lean_dec(v_numParams_589_);
                        leanh::lean_dec(v_ctorName_588_);
                        leanh::lean_dec_ref_known(v_projFn_580_, 2);
                        leanh::lean_dec_ref(v_parent_568_);
                        v___x_595_ = leanh::lean_box(0);
                        if v_isShared_586_ == 0 {
                            leanh::lean_ctor_set(v___x_585_, 0, v___x_595_);
                            v___x_597_ = v___x_585_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_598_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_595_);
                            v___x_597_ = v_reuseFailAlloc_598_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_585_);
                        leanh::lean_inc_ref(v_parent_568_);
                        v___x_599_ = l_Lean_Meta_Grind_isCongrRoot___redArg(
                            v_parent_568_,
                            v_a_569_,
                            v_a_575_,
                            v_a_576_,
                            v_a_577_,
                            v_a_578_,
                        );
                        if leanh::lean_obj_tag(v___x_599_) == 0 {
                            v_a_600_ = leanh::lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_751_ =
                                (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_751_ == 0 {
                                v___x_602_ = v___x_599_;
                                v_isShared_603_ = v_isSharedCheck_751_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_600_);
                                leanh::lean_dec(v___x_599_);
                                v___x_602_ = leanh::lean_box(0);
                                v_isShared_603_ = v_isSharedCheck_751_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_i_590_);
                            leanh::lean_dec(v_numParams_589_);
                            leanh::lean_dec(v_ctorName_588_);
                            leanh::lean_dec_ref_known(v_projFn_580_, 2);
                            leanh::lean_dec_ref(v_parent_568_);
                            v_a_752_ = leanh::lean_ctor_get(v___x_599_, 0);
                            v_isSharedCheck_759_ =
                                (!leanh::lean_is_exclusive(v___x_599_)) as u8;
                            if v_isSharedCheck_759_ == 0 {
                                v___x_754_ = v___x_599_;
                                v_isShared_755_ = v_isSharedCheck_759_;
                                state = 23;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_752_);
                                leanh::lean_dec(v___x_599_);
                                v___x_754_ = leanh::lean_box(0);
                                v_isShared_755_ = v_isSharedCheck_759_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_583_);
                    leanh::lean_dec_ref_known(v_projFn_580_, 2);
                    leanh::lean_dec_ref(v_parent_568_);
                    v___x_760_ = leanh::lean_box(0);
                    if v_isShared_586_ == 0 {
                        leanh::lean_ctor_set(v___x_585_, 0, v___x_760_);
                        v___x_762_ = v___x_585_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_763_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_760_);
                        v___x_762_ = v_reuseFailAlloc_763_;
                        state = 25;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_597_;
            }
            3 => {
                v___x_604_ = (leanh::lean_unbox(v_a_600_) as u8);
                leanh::lean_dec(v_a_600_);
                if v___x_604_ == 0 {
                    leanh::lean_dec(v_i_590_);
                    leanh::lean_dec(v_numParams_589_);
                    leanh::lean_dec(v_ctorName_588_);
                    leanh::lean_dec_ref_known(v_projFn_580_, 2);
                    leanh::lean_dec_ref(v_parent_568_);
                    v___x_605_ = leanh::lean_box(0);
                    if v_isShared_603_ == 0 {
                        leanh::lean_ctor_set(v___x_602_, 0, v___x_605_);
                        v___x_607_ = v___x_602_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_608_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_605_);
                        v___x_607_ = v_reuseFailAlloc_608_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_609_ = l_Lean_Expr_appArg_x21(v_parent_568_);
                    leanh::lean_inc_ref(v___x_609_);
                    v___x_610_ = l_Lean_Meta_Grind_getRootENode___redArg(
                        v___x_609_, v_a_569_, v_a_575_, v_a_576_, v_a_577_, v_a_578_,
                    );
                    if leanh::lean_obj_tag(v___x_610_) == 0 {
                        v_a_611_ = leanh::lean_ctor_get(v___x_610_, 0);
                        v_isSharedCheck_742_ = (!leanh::lean_is_exclusive(v___x_610_)) as u8;
                        if v_isSharedCheck_742_ == 0 {
                            v___x_613_ = v___x_610_;
                            v_isShared_614_ = v_isSharedCheck_742_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_611_);
                            leanh::lean_dec(v___x_610_);
                            v___x_613_ = leanh::lean_box(0);
                            v_isShared_614_ = v_isSharedCheck_742_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_609_);
                        leanh::lean_del_object(v___x_602_);
                        leanh::lean_dec(v_i_590_);
                        leanh::lean_dec(v_numParams_589_);
                        leanh::lean_dec(v_ctorName_588_);
                        leanh::lean_dec_ref_known(v_projFn_580_, 2);
                        leanh::lean_dec_ref(v_parent_568_);
                        v_a_743_ = leanh::lean_ctor_get(v___x_610_, 0);
                        v_isSharedCheck_750_ = (!leanh::lean_is_exclusive(v___x_610_)) as u8;
                        if v_isSharedCheck_750_ == 0 {
                            v___x_745_ = v___x_610_;
                            v_isShared_746_ = v_isSharedCheck_750_;
                            state = 21;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_743_);
                            leanh::lean_dec(v___x_610_);
                            v___x_745_ = leanh::lean_box(0);
                            v_isShared_746_ = v_isSharedCheck_750_;
                            state = 21;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_607_;
            }
            5 => {
                v_self_615_ = leanh::lean_ctor_get(v_a_611_, 0);
                leanh::lean_inc_ref(v_self_615_);
                v_heqProofs_616_ = leanh::lean_ctor_get_uint8(
                    v_a_611_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 12 + 4) as u32,
                );
                leanh::lean_dec(v_a_611_);
                v___x_703_ = l_Lean_Expr_isAppOf(v_self_615_, v_ctorName_588_);
                leanh::lean_dec(v_ctorName_588_);
                if v___x_703_ == 0 {
                    leanh::lean_dec_ref(v_self_615_);
                    leanh::lean_del_object(v___x_613_);
                    leanh::lean_dec_ref(v___x_609_);
                    leanh::lean_dec(v_i_590_);
                    leanh::lean_dec(v_numParams_589_);
                    leanh::lean_dec_ref_known(v_projFn_580_, 2);
                    leanh::lean_dec_ref(v_parent_568_);
                    v___x_704_ = leanh::lean_box(0);
                    if v_isShared_603_ == 0 {
                        leanh::lean_ctor_set(v___x_602_, 0, v___x_704_);
                        v___x_706_ = v___x_602_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_707_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_707_, 0, v___x_704_);
                        v___x_706_ = v_reuseFailAlloc_707_;
                        state = 16;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_602_);
                    v___x_708_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v___x_609_,
                            v_self_615_,
                        );
                    leanh::lean_dec_ref(v___x_609_);
                    if v___x_708_ == 0 {
                        if v_heqProofs_616_ == 0 {
                            leanh::lean_dec_ref_known(v_projFn_580_, 2);
                            v___x_709_ = l_Lean_Expr_appFn_x21(v_parent_568_);
                            leanh::lean_inc_ref(v_self_615_);
                            v___x_710_ = l_Lean_Expr_app___override(v___x_709_, v_self_615_);
                            v___x_711_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_710_, v_a_574_);
                            if leanh::lean_obj_tag(v___x_711_) == 0 {
                                v_a_712_ = leanh::lean_ctor_get(v___x_711_, 0);
                                leanh::lean_inc(v_a_712_);
                                leanh::lean_dec_ref_known(v___x_711_, 1);
                                v_parentNew_680_ = v_a_712_;
                                v___y_681_ = v_a_569_;
                                v___y_682_ = v_a_570_;
                                v___y_683_ = v_a_571_;
                                v___y_684_ = v_a_572_;
                                v___y_685_ = v_a_573_;
                                v___y_686_ = v_a_574_;
                                v___y_687_ = v_a_575_;
                                v___y_688_ = v_a_576_;
                                v___y_689_ = v_a_577_;
                                v___y_690_ = v_a_578_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_self_615_);
                                leanh::lean_del_object(v___x_613_);
                                leanh::lean_dec(v_i_590_);
                                leanh::lean_dec(v_numParams_589_);
                                leanh::lean_dec_ref(v_parent_568_);
                                v_a_713_ = leanh::lean_ctor_get(v___x_711_, 0);
                                v_isSharedCheck_720_ =
                                    (!leanh::lean_is_exclusive(v___x_711_)) as u8;
                                if v_isSharedCheck_720_ == 0 {
                                    v___x_715_ = v___x_711_;
                                    v_isShared_716_ = v_isSharedCheck_720_;
                                    state = 17;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_713_);
                                    leanh::lean_dec(v___x_711_);
                                    v___x_715_ = leanh::lean_box(0);
                                    v_isShared_716_ = v_isSharedCheck_720_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            v_dummy_721_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateProjEq___closed__7
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Meta_Grind_propagateProjEq___closed__7_once
                                ),
                                _init_l_Lean_Meta_Grind_propagateProjEq___closed__7,
                            );
                            v_nargs_722_ = l_Lean_Expr_getAppNumArgs(v_self_615_);
                            leanh::lean_inc(v_nargs_722_);
                            v___x_723_ = lean_mk_array(v_nargs_722_, v_dummy_721_);
                            v___x_724_ = lean_nat_sub(v_nargs_722_, v___x_591_);
                            leanh::lean_dec(v_nargs_722_);
                            leanh::lean_inc_ref_n(v_self_615_, 2);
                            v___x_725_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                v_self_615_,
                                v___x_723_,
                                v___x_724_,
                            );
                            v___x_726_ = leanh::lean_unsigned_to_nat(0);
                            leanh::lean_inc(v_numParams_589_);
                            v___x_727_ = l_Array_toSubarray___redArg(
                                v___x_725_,
                                v___x_726_,
                                v_numParams_589_,
                            );
                            v___x_728_ = l_Lean_Meta_Grind_propagateProjEq___closed__8;
                            v___x_729_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v___x_727_, v___x_728_);
                            v___x_730_ = l_Lean_mkAppN(v_projFn_580_, v___x_729_);
                            leanh::lean_dec_ref(v___x_729_);
                            v___x_731_ = l_Lean_Expr_app___override(v___x_730_, v_self_615_);
                            v___x_732_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_731_, v_a_574_);
                            if leanh::lean_obj_tag(v___x_732_) == 0 {
                                v_a_733_ = leanh::lean_ctor_get(v___x_732_, 0);
                                leanh::lean_inc(v_a_733_);
                                leanh::lean_dec_ref_known(v___x_732_, 1);
                                v_parentNew_680_ = v_a_733_;
                                v___y_681_ = v_a_569_;
                                v___y_682_ = v_a_570_;
                                v___y_683_ = v_a_571_;
                                v___y_684_ = v_a_572_;
                                v___y_685_ = v_a_573_;
                                v___y_686_ = v_a_574_;
                                v___y_687_ = v_a_575_;
                                v___y_688_ = v_a_576_;
                                v___y_689_ = v_a_577_;
                                v___y_690_ = v_a_578_;
                                state = 13;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_self_615_);
                                leanh::lean_del_object(v___x_613_);
                                leanh::lean_dec(v_i_590_);
                                leanh::lean_dec(v_numParams_589_);
                                leanh::lean_dec_ref(v_parent_568_);
                                v_a_734_ = leanh::lean_ctor_get(v___x_732_, 0);
                                v_isSharedCheck_741_ =
                                    (!leanh::lean_is_exclusive(v___x_732_)) as u8;
                                if v_isSharedCheck_741_ == 0 {
                                    v___x_736_ = v___x_732_;
                                    v_isShared_737_ = v_isSharedCheck_741_;
                                    state = 19;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_734_);
                                    leanh::lean_dec(v___x_732_);
                                    v___x_736_ = leanh::lean_box(0);
                                    v_isShared_737_ = v_isSharedCheck_741_;
                                    state = 19;
                                    continue;
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref_known(v_projFn_580_, 2);
                        v_parentNew_659_ = v_parent_568_;
                        v___y_660_ = v_a_569_;
                        v___y_661_ = v_a_570_;
                        v___y_662_ = v_a_571_;
                        v___y_663_ = v_a_572_;
                        v___y_664_ = v_a_573_;
                        v___y_665_ = v_a_574_;
                        v___y_666_ = v_a_575_;
                        v___y_667_ = v_a_576_;
                        v___y_668_ = v_a_577_;
                        v___y_669_ = v_a_578_;
                        state = 12;
                        continue;
                    }
                }
            }
            6 => {
                v___x_625_ = lean_nat_add(v_numParams_589_, v_i_590_);
                leanh::lean_dec(v_i_590_);
                leanh::lean_dec(v_numParams_589_);
                v___x_626_ = l_Lean_Expr_getAppNumArgs(v_self_615_);
                v___x_627_ = lean_nat_dec_lt(v___x_625_, v___x_626_);
                if v___x_627_ == 0 {
                    leanh::lean_dec(v___x_626_);
                    leanh::lean_dec(v___x_625_);
                    leanh::lean_dec_ref(v___y_618_);
                    leanh::lean_dec_ref(v_self_615_);
                    v___x_628_ = leanh::lean_box(0);
                    if v_isShared_614_ == 0 {
                        leanh::lean_ctor_set(v___x_613_, 0, v___x_628_);
                        v___x_630_ = v___x_613_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_631_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_631_, 0, v___x_628_);
                        v___x_630_ = v_reuseFailAlloc_631_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_613_);
                    v___x_632_ = lean_nat_sub(v___x_626_, v___x_625_);
                    leanh::lean_dec(v___x_625_);
                    leanh::lean_dec(v___x_626_);
                    v___x_633_ = lean_nat_sub(v___x_632_, v___x_591_);
                    leanh::lean_dec(v___x_632_);
                    v___x_634_ = l_Lean_Expr_getRevArg_x21(v_self_615_, v___x_633_);
                    leanh::lean_dec_ref(v_self_615_);
                    leanh::lean_inc_ref(v___x_634_);
                    v___x_635_ = l_Lean_Meta_mkEqRefl(
                        v___x_634_, v___y_621_, v___y_622_, v___y_623_, v___y_624_,
                    );
                    if leanh::lean_obj_tag(v___x_635_) == 0 {
                        v_a_636_ = leanh::lean_ctor_get(v___x_635_, 0);
                        leanh::lean_inc(v_a_636_);
                        leanh::lean_dec_ref_known(v___x_635_, 1);
                        leanh::lean_inc_ref(v___x_634_);
                        leanh::lean_inc_ref(v___y_618_);
                        v___x_637_ = l_Lean_Meta_mkEq(
                            v___y_618_, v___x_634_, v___y_621_, v___y_622_, v___y_623_, v___y_624_,
                        );
                        if leanh::lean_obj_tag(v___x_637_) == 0 {
                            v_a_638_ = leanh::lean_ctor_get(v___x_637_, 0);
                            leanh::lean_inc(v_a_638_);
                            leanh::lean_dec_ref_known(v___x_637_, 1);
                            v___x_639_ = l_Lean_Meta_mkExpectedPropHint(v_a_636_, v_a_638_);
                            v___x_640_ = 0;
                            v___x_641_ = l_Lean_Meta_Grind_pushEqCore___redArg(
                                v___y_618_, v___x_634_, v___x_639_, v___x_640_, v___y_619_,
                                v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_,
                            );
                            return v___x_641_;
                        } else {
                            leanh::lean_dec(v_a_636_);
                            leanh::lean_dec_ref(v___x_634_);
                            leanh::lean_dec_ref(v___y_618_);
                            v_a_642_ = leanh::lean_ctor_get(v___x_637_, 0);
                            v_isSharedCheck_649_ =
                                (!leanh::lean_is_exclusive(v___x_637_)) as u8;
                            if v_isSharedCheck_649_ == 0 {
                                v___x_644_ = v___x_637_;
                                v_isShared_645_ = v_isSharedCheck_649_;
                                state = 8;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_642_);
                                leanh::lean_dec(v___x_637_);
                                v___x_644_ = leanh::lean_box(0);
                                v_isShared_645_ = v_isSharedCheck_649_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_634_);
                        leanh::lean_dec_ref(v___y_618_);
                        v_a_650_ = leanh::lean_ctor_get(v___x_635_, 0);
                        v_isSharedCheck_657_ = (!leanh::lean_is_exclusive(v___x_635_)) as u8;
                        if v_isSharedCheck_657_ == 0 {
                            v___x_652_ = v___x_635_;
                            v_isShared_653_ = v_isSharedCheck_657_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_650_);
                            leanh::lean_dec(v___x_635_);
                            v___x_652_ = leanh::lean_box(0);
                            v_isShared_653_ = v_isSharedCheck_657_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            7 => {
                return v___x_630_;
            }
            8 => {
                if v_isShared_645_ == 0 {
                    v___x_647_ = v___x_644_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_648_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
                    v___x_647_ = v_reuseFailAlloc_648_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_647_;
            }
            10 => {
                if v_isShared_653_ == 0 {
                    v___x_655_ = v___x_652_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_656_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_656_, 0, v_a_650_);
                    v___x_655_ = v_reuseFailAlloc_656_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_655_;
            }
            12 => {
                v_options_670_ = leanh::lean_ctor_get(v___y_668_, 2);
                v_hasTrace_671_ = leanh::lean_ctor_get_uint8(
                    v_options_670_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_671_ == 0 {
                    v___y_618_ = v_parentNew_659_;
                    v___y_619_ = v___y_660_;
                    v___y_620_ = v___y_662_;
                    v___y_621_ = v___y_666_;
                    v___y_622_ = v___y_667_;
                    v___y_623_ = v___y_668_;
                    v___y_624_ = v___y_669_;
                    state = 6;
                    continue;
                } else {
                    v_inheritedTraceOptions_672_ = leanh::lean_ctor_get(v___y_668_, 13);
                    v___x_673_ = l_Lean_Meta_Grind_propagateProjEq___closed__3;
                    v___x_674_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateProjEq___closed__6),
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_propagateProjEq___closed__6_once),
                        _init_l_Lean_Meta_Grind_propagateProjEq___closed__6,
                    );
                    v___x_675_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_672_,
                        v_options_670_,
                        v___x_674_,
                    );
                    if v___x_675_ == 0 {
                        v___y_618_ = v_parentNew_659_;
                        v___y_619_ = v___y_660_;
                        v___y_620_ = v___y_662_;
                        v___y_621_ = v___y_666_;
                        v___y_622_ = v___y_667_;
                        v___y_623_ = v___y_668_;
                        v___y_624_ = v___y_669_;
                        state = 6;
                        continue;
                    } else {
                        v___x_676_ = l_Lean_Meta_Grind_updateLastTag(
                            v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_,
                            v___y_666_, v___y_667_, v___y_668_, v___y_669_,
                        );
                        if leanh::lean_obj_tag(v___x_676_) == 0 {
                            leanh::lean_dec_ref_known(v___x_676_, 1);
                            leanh::lean_inc_ref(v_parentNew_659_);
                            v___x_677_ = l_Lean_MessageData_ofExpr(v_parentNew_659_);
                            v___x_678_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(v___x_673_, v___x_677_, v___y_666_, v___y_667_, v___y_668_, v___y_669_);
                            if leanh::lean_obj_tag(v___x_678_) == 0 {
                                leanh::lean_dec_ref_known(v___x_678_, 1);
                                v___y_618_ = v_parentNew_659_;
                                v___y_619_ = v___y_660_;
                                v___y_620_ = v___y_662_;
                                v___y_621_ = v___y_666_;
                                v___y_622_ = v___y_667_;
                                v___y_623_ = v___y_668_;
                                v___y_624_ = v___y_669_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_parentNew_659_);
                                leanh::lean_dec_ref(v_self_615_);
                                leanh::lean_del_object(v___x_613_);
                                leanh::lean_dec(v_i_590_);
                                leanh::lean_dec(v_numParams_589_);
                                return v___x_678_;
                            }
                        } else {
                            leanh::lean_dec_ref(v_parentNew_659_);
                            leanh::lean_dec_ref(v_self_615_);
                            leanh::lean_del_object(v___x_613_);
                            leanh::lean_dec(v_i_590_);
                            leanh::lean_dec(v_numParams_589_);
                            return v___x_676_;
                        }
                    }
                }
            }
            13 => {
                v___x_691_ = l_Lean_Meta_Grind_getGeneration___redArg(v_parent_568_, v___y_681_);
                leanh::lean_dec_ref(v_parent_568_);
                if leanh::lean_obj_tag(v___x_691_) == 0 {
                    v_a_692_ = leanh::lean_ctor_get(v___x_691_, 0);
                    leanh::lean_inc(v_a_692_);
                    leanh::lean_dec_ref_known(v___x_691_, 1);
                    v___x_693_ = leanh::lean_box(0);
                    leanh::lean_inc(v___y_690_);
                    leanh::lean_inc_ref(v___y_689_);
                    leanh::lean_inc(v___y_688_);
                    leanh::lean_inc_ref(v___y_687_);
                    leanh::lean_inc(v___y_686_);
                    leanh::lean_inc_ref(v___y_685_);
                    leanh::lean_inc(v___y_684_);
                    leanh::lean_inc_ref(v___y_683_);
                    leanh::lean_inc(v___y_682_);
                    leanh::lean_inc(v___y_681_);
                    leanh::lean_inc_ref(v_parentNew_680_);
                    v___x_694_ = lean_grind_internalize(
                        v_parentNew_680_,
                        v_a_692_,
                        v___x_693_,
                        v___y_681_,
                        v___y_682_,
                        v___y_683_,
                        v___y_684_,
                        v___y_685_,
                        v___y_686_,
                        v___y_687_,
                        v___y_688_,
                        v___y_689_,
                        v___y_690_,
                    );
                    if leanh::lean_obj_tag(v___x_694_) == 0 {
                        leanh::lean_dec_ref_known(v___x_694_, 1);
                        v_parentNew_659_ = v_parentNew_680_;
                        v___y_660_ = v___y_681_;
                        v___y_661_ = v___y_682_;
                        v___y_662_ = v___y_683_;
                        v___y_663_ = v___y_684_;
                        v___y_664_ = v___y_685_;
                        v___y_665_ = v___y_686_;
                        v___y_666_ = v___y_687_;
                        v___y_667_ = v___y_688_;
                        v___y_668_ = v___y_689_;
                        v___y_669_ = v___y_690_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_parentNew_680_);
                        leanh::lean_dec_ref(v_self_615_);
                        leanh::lean_del_object(v___x_613_);
                        leanh::lean_dec(v_i_590_);
                        leanh::lean_dec(v_numParams_589_);
                        return v___x_694_;
                    }
                } else {
                    leanh::lean_dec_ref(v_parentNew_680_);
                    leanh::lean_dec_ref(v_self_615_);
                    leanh::lean_del_object(v___x_613_);
                    leanh::lean_dec(v_i_590_);
                    leanh::lean_dec(v_numParams_589_);
                    v_a_695_ = leanh::lean_ctor_get(v___x_691_, 0);
                    v_isSharedCheck_702_ = (!leanh::lean_is_exclusive(v___x_691_)) as u8;
                    if v_isSharedCheck_702_ == 0 {
                        v___x_697_ = v___x_691_;
                        v_isShared_698_ = v_isSharedCheck_702_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_695_);
                        leanh::lean_dec(v___x_691_);
                        v___x_697_ = leanh::lean_box(0);
                        v_isShared_698_ = v_isSharedCheck_702_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_698_ == 0 {
                    v___x_700_ = v___x_697_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_701_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_701_, 0, v_a_695_);
                    v___x_700_ = v_reuseFailAlloc_701_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_700_;
            }
            16 => {
                return v___x_706_;
            }
            17 => {
                if v_isShared_716_ == 0 {
                    v___x_718_ = v___x_715_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_719_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_719_, 0, v_a_713_);
                    v___x_718_ = v_reuseFailAlloc_719_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_718_;
            }
            19 => {
                if v_isShared_737_ == 0 {
                    v___x_739_ = v___x_736_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_740_, 0, v_a_734_);
                    v___x_739_ = v_reuseFailAlloc_740_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_739_;
            }
            21 => {
                if v_isShared_746_ == 0 {
                    v___x_748_ = v___x_745_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_749_, 0, v_a_743_);
                    v___x_748_ = v_reuseFailAlloc_749_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_748_;
            }
            23 => {
                if v_isShared_755_ == 0 {
                    v___x_757_ = v___x_754_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_758_, 0, v_a_752_);
                    v___x_757_ = v_reuseFailAlloc_758_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_757_;
            }
            25 => {
                return v___x_762_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_propagateProjEq___boxed(
    mut v_parent_767_: *mut leanh::LeanObject,
    mut v_a_768_: *mut leanh::LeanObject,
    mut v_a_769_: *mut leanh::LeanObject,
    mut v_a_770_: *mut leanh::LeanObject,
    mut v_a_771_: *mut leanh::LeanObject,
    mut v_a_772_: *mut leanh::LeanObject,
    mut v_a_773_: *mut leanh::LeanObject,
    mut v_a_774_: *mut leanh::LeanObject,
    mut v_a_775_: *mut leanh::LeanObject,
    mut v_a_776_: *mut leanh::LeanObject,
    mut v_a_777_: *mut leanh::LeanObject,
    mut v_a_778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_779_ = l_Lean_Meta_Grind_propagateProjEq(
        v_parent_767_,
        v_a_768_,
        v_a_769_,
        v_a_770_,
        v_a_771_,
        v_a_772_,
        v_a_773_,
        v_a_774_,
        v_a_775_,
        v_a_776_,
        v_a_777_,
    );
    leanh::lean_dec(v_a_777_);
    leanh::lean_dec_ref(v_a_776_);
    leanh::lean_dec(v_a_775_);
    leanh::lean_dec_ref(v_a_774_);
    leanh::lean_dec(v_a_773_);
    leanh::lean_dec_ref(v_a_772_);
    leanh::lean_dec(v_a_771_);
    leanh::lean_dec_ref(v_a_770_);
    leanh::lean_dec(v_a_769_);
    leanh::lean_dec(v_a_768_);
    return v_res_779_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(
    mut v_cls_780_: *mut leanh::LeanObject,
    mut v_msg_781_: *mut leanh::LeanObject,
    mut v___y_782_: *mut leanh::LeanObject,
    mut v___y_783_: *mut leanh::LeanObject,
    mut v___y_784_: *mut leanh::LeanObject,
    mut v___y_785_: *mut leanh::LeanObject,
    mut v___y_786_: *mut leanh::LeanObject,
    mut v___y_787_: *mut leanh::LeanObject,
    mut v___y_788_: *mut leanh::LeanObject,
    mut v___y_789_: *mut leanh::LeanObject,
    mut v___y_790_: *mut leanh::LeanObject,
    mut v___y_791_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_793_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_793_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___redArg(
        v_cls_780_, v_msg_781_, v___y_788_, v___y_789_, v___y_790_, v___y_791_,
    );
    return v___x_793_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1___boxed(
    mut v_cls_794_: *mut leanh::LeanObject,
    mut v_msg_795_: *mut leanh::LeanObject,
    mut v___y_796_: *mut leanh::LeanObject,
    mut v___y_797_: *mut leanh::LeanObject,
    mut v___y_798_: *mut leanh::LeanObject,
    mut v___y_799_: *mut leanh::LeanObject,
    mut v___y_800_: *mut leanh::LeanObject,
    mut v___y_801_: *mut leanh::LeanObject,
    mut v___y_802_: *mut leanh::LeanObject,
    mut v___y_803_: *mut leanh::LeanObject,
    mut v___y_804_: *mut leanh::LeanObject,
    mut v___y_805_: *mut leanh::LeanObject,
    mut v___y_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_807_ = l_Lean_addTrace___at___00Lean_Meta_Grind_propagateProjEq_spec__1(
        v_cls_794_, v_msg_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_,
        v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_,
    );
    leanh::lean_dec(v___y_805_);
    leanh::lean_dec_ref(v___y_804_);
    leanh::lean_dec(v___y_803_);
    leanh::lean_dec_ref(v___y_802_);
    leanh::lean_dec(v___y_801_);
    leanh::lean_dec_ref(v___y_800_);
    leanh::lean_dec(v___y_799_);
    leanh::lean_dec_ref(v___y_798_);
    leanh::lean_dec(v___y_797_);
    leanh::lean_dec(v___y_796_);
    return v_res_807_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2(
    mut v_inst_808_: *mut leanh::LeanObject,
    mut v_R_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_b_811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Meta_Grind_propagateProjEq_spec__2___redArg(v_a_810_, v_b_811_);
    return v___x_812_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Proj(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Proj(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Proj(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Proj(builtin);
}
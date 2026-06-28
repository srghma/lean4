// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.SearchM
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Util
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr1, l_Lean_Name_num___override};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Expr::{l_Lean_Expr_const___override, l_Lean_FVarIdSet_insert};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
    l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_3, lean_box,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unsigned_to_nat,
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value:
    LeanStringObject<20> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        95, 105, 110, 104, 97, 98, 105, 116, 101, 100, 69, 120, 112, 114, 68, 117, 109, 109, 121, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value
) as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value:
    LeanCtorObject<3> = LeanCtorObject {
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__2_value
        ) as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value:
    LeanArrayObject<0> = LeanArrayObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8_value
) as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default: u8 = 0;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind: u8 = 0;
pub static l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0_value) as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(
    mut v_x_443_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_443_) == 0 {
        let mut v___x_444_: *mut LeanObject = core::ptr::null_mut();
        v___x_444_ = lean_unsigned_to_nat(0);
        return v___x_444_;
    } else {
        let mut v___x_445_: *mut LeanObject = core::ptr::null_mut();
        v___x_445_ = lean_unsigned_to_nat(1);
        return v___x_445_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx___boxed(
    mut v_x_446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_447_: *mut LeanObject = core::ptr::null_mut();
    v_res_447_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorIdx(v_x_446_);
    lean_dec_ref(v_x_446_);
    return v_res_447_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(
    mut v_t_448_: *mut LeanObject,
    mut v_k_449_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_448_) == 0 {
        let mut v_d_450_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_451_: *mut LeanObject = core::ptr::null_mut();
        v_d_450_ = lean_ctor_get(v_t_448_, 0);
        lean_inc_ref(v_d_450_);
        lean_dec_ref_known(v_t_448_, 1);
        v___x_451_ = lean_apply_1(v_k_449_, v_d_450_);
        return v___x_451_;
    } else {
        let mut v_s_452_: *mut LeanObject = core::ptr::null_mut();
        let mut v_hs_453_: *mut LeanObject = core::ptr::null_mut();
        let mut v_decVars_454_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_455_: *mut LeanObject = core::ptr::null_mut();
        v_s_452_ = lean_ctor_get(v_t_448_, 0);
        lean_inc_ref(v_s_452_);
        v_hs_453_ = lean_ctor_get(v_t_448_, 1);
        lean_inc_ref(v_hs_453_);
        v_decVars_454_ = lean_ctor_get(v_t_448_, 2);
        lean_inc(v_decVars_454_);
        lean_dec_ref_known(v_t_448_, 3);
        v___x_455_ = lean_apply_3(v_k_449_, v_s_452_, v_hs_453_, v_decVars_454_);
        return v___x_455_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(
    mut v_motive_456_: *mut LeanObject,
    mut v_ctorIdx_457_: *mut LeanObject,
    mut v_t_458_: *mut LeanObject,
    mut v_h_459_: *mut LeanObject,
    mut v_k_460_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_461_: *mut LeanObject = core::ptr::null_mut();
    v___x_461_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_458_, v_k_460_);
    return v___x_461_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___boxed(
    mut v_motive_462_: *mut LeanObject,
    mut v_ctorIdx_463_: *mut LeanObject,
    mut v_t_464_: *mut LeanObject,
    mut v_h_465_: *mut LeanObject,
    mut v_k_466_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_467_: *mut LeanObject = core::ptr::null_mut();
    v_res_467_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim(
        v_motive_462_,
        v_ctorIdx_463_,
        v_t_464_,
        v_h_465_,
        v_k_466_,
    );
    lean_dec(v_ctorIdx_463_);
    return v_res_467_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim___redArg(
    mut v_t_468_: *mut LeanObject,
    mut v_diseq_469_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_470_: *mut LeanObject = core::ptr::null_mut();
    v___x_470_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_468_, v_diseq_469_);
    return v___x_470_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_diseq_elim(
    mut v_motive_471_: *mut LeanObject,
    mut v_t_472_: *mut LeanObject,
    mut v_h_473_: *mut LeanObject,
    mut v_diseq_474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_475_: *mut LeanObject = core::ptr::null_mut();
    v___x_475_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_472_, v_diseq_474_);
    return v___x_475_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim___redArg(
    mut v_t_476_: *mut LeanObject,
    mut v_cooper_477_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_478_: *mut LeanObject = core::ptr::null_mut();
    v___x_478_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_476_, v_cooper_477_);
    return v___x_478_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_cooper_elim(
    mut v_motive_479_: *mut LeanObject,
    mut v_t_480_: *mut LeanObject,
    mut v_h_481_: *mut LeanObject,
    mut v_cooper_482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_483_: *mut LeanObject = core::ptr::null_mut();
    v___x_483_ = l_Lean_Meta_Grind_Arith_Cutsat_CaseKind_ctorElim___redArg(v_t_480_, v_cooper_482_);
    return v___x_483_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0()
-> *mut LeanObject {
    let mut v___x_484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_485_: *mut LeanObject = core::ptr::null_mut();
    v___x_484_ = lean_unsigned_to_nat(0);
    v___x_485_ = lean_nat_to_int(v___x_484_);
    return v___x_485_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1()
-> *mut LeanObject {
    let mut v___x_486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_487_: *mut LeanObject = core::ptr::null_mut();
    v___x_486_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__0,
    );
    v___x_487_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_487_, 0, v___x_486_);
    return v___x_487_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4()
-> *mut LeanObject {
    let mut v___x_491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_493_: *mut LeanObject = core::ptr::null_mut();
    v___x_491_ = lean_box(0);
    v___x_492_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__3;
    v___x_493_ = l_Lean_Expr_const___override(v___x_492_, v___x_491_);
    return v___x_493_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5()
-> *mut LeanObject {
    let mut v___x_494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_495_: *mut LeanObject = core::ptr::null_mut();
    v___x_494_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__4,
    );
    v___x_495_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_495_, 0, v___x_494_);
    return v___x_495_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6()
-> *mut LeanObject {
    let mut v___x_496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_498_: *mut LeanObject = core::ptr::null_mut();
    v___x_496_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__5,
    );
    v___x_497_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__1,
    );
    v___x_498_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_498_, 0, v___x_497_);
    lean_ctor_set(v___x_498_, 1, v___x_496_);
    return v___x_498_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7()
-> *mut LeanObject {
    let mut v___x_499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_501_: u8 = 0;
    let mut v___x_502_: *mut LeanObject = core::ptr::null_mut();
    v___x_499_ = lean_box(0);
    v___x_500_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__6,
    );
    v___x_501_ = 0;
    v___x_502_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_502_, 0, v___x_500_);
    lean_ctor_set(v___x_502_, 1, v___x_500_);
    lean_ctor_set(v___x_502_, 2, v___x_499_);
    lean_ctor_set_uint8(
        v___x_502_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_501_,
    );
    return v___x_502_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9()
-> *mut LeanObject {
    let mut v___x_505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_508_: *mut LeanObject = core::ptr::null_mut();
    v___x_505_ = lean_box(1);
    v___x_506_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__8;
    v___x_507_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__7,
    );
    v___x_508_ = lean_alloc_ctor(1, 3, (0) as u32);
    lean_ctor_set(v___x_508_, 0, v___x_507_);
    lean_ctor_set(v___x_508_, 1, v___x_506_);
    lean_ctor_set(v___x_508_, 2, v___x_505_);
    return v___x_508_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default() -> *mut LeanObject
{
    let mut v___x_509_: *mut LeanObject = core::ptr::null_mut();
    v___x_509_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default___closed__9,
    );
    return v___x_509_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind() -> *mut LeanObject {
    let mut v___x_510_: *mut LeanObject = core::ptr::null_mut();
    v___x_510_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
    return v___x_510_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0()
-> *mut LeanObject {
    let mut v___x_511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_514_: *mut LeanObject = core::ptr::null_mut();
    v___x_511_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
    v___x_512_ = lean_box(0);
    v___x_513_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default;
    v___x_514_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_514_, 0, v___x_513_);
    lean_ctor_set(v___x_514_, 1, v___x_512_);
    lean_ctor_set(v___x_514_, 2, v___x_511_);
    return v___x_514_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default() -> *mut LeanObject {
    let mut v___x_515_: *mut LeanObject = core::ptr::null_mut();
    v___x_515_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default___closed__0,
    );
    return v___x_515_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase() -> *mut LeanObject {
    let mut v___x_516_: *mut LeanObject = core::ptr::null_mut();
    v___x_516_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default;
    return v___x_516_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(
    mut v_x_517_: u8,
) -> *mut LeanObject {
    if v_x_517_ == 0 {
        let mut v___x_518_: *mut LeanObject = core::ptr::null_mut();
        v___x_518_ = lean_unsigned_to_nat(0);
        return v___x_518_;
    } else {
        let mut v___x_519_: *mut LeanObject = core::ptr::null_mut();
        v___x_519_ = lean_unsigned_to_nat(1);
        return v___x_519_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx___boxed(
    mut v_x_520_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_boxed_521_: u8 = 0;
    let mut v_res_522_: *mut LeanObject = core::ptr::null_mut();
    v_x_boxed_521_ = (lean_unbox(v_x_520_) as u8);
    v_res_522_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_boxed_521_);
    return v_res_522_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(
    mut v_x_523_: u8,
) -> *mut LeanObject {
    let mut v___x_524_: *mut LeanObject = core::ptr::null_mut();
    v___x_524_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_523_);
    return v___x_524_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx___boxed(
    mut v_x_525_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_4__boxed_526_: u8 = 0;
    let mut v_res_527_: *mut LeanObject = core::ptr::null_mut();
    v_x_4__boxed_526_ = (lean_unbox(v_x_525_) as u8);
    v_res_527_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_toCtorIdx(v_x_4__boxed_526_);
    return v_res_527_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(
    mut v_k_528_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_528_);
    return v_k_528_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg___boxed(
    mut v_k_529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_530_: *mut LeanObject = core::ptr::null_mut();
    v_res_530_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___redArg(v_k_529_);
    lean_dec(v_k_529_);
    return v_res_530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(
    mut v_motive_531_: *mut LeanObject,
    mut v_ctorIdx_532_: *mut LeanObject,
    mut v_t_533_: u8,
    mut v_h_534_: *mut LeanObject,
    mut v_k_535_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_k_535_);
    return v_k_535_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim___boxed(
    mut v_motive_536_: *mut LeanObject,
    mut v_ctorIdx_537_: *mut LeanObject,
    mut v_t_538_: *mut LeanObject,
    mut v_h_539_: *mut LeanObject,
    mut v_k_540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_541_: u8 = 0;
    let mut v_res_542_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_541_ = (lean_unbox(v_t_538_) as u8);
    v_res_542_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorElim(
        v_motive_536_,
        v_ctorIdx_537_,
        v_t_boxed_541_,
        v_h_539_,
        v_k_540_,
    );
    lean_dec(v_k_540_);
    lean_dec(v_ctorIdx_537_);
    return v_res_542_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(
    mut v_rat_543_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rat_543_);
    return v_rat_543_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg___boxed(
    mut v_rat_544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_545_: *mut LeanObject = core::ptr::null_mut();
    v_res_545_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___redArg(v_rat_544_);
    lean_dec(v_rat_544_);
    return v_res_545_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(
    mut v_motive_546_: *mut LeanObject,
    mut v_t_547_: u8,
    mut v_h_548_: *mut LeanObject,
    mut v_rat_549_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_rat_549_);
    return v_rat_549_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim___boxed(
    mut v_motive_550_: *mut LeanObject,
    mut v_t_551_: *mut LeanObject,
    mut v_h_552_: *mut LeanObject,
    mut v_rat_553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_554_: u8 = 0;
    let mut v_res_555_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_554_ = (lean_unbox(v_t_551_) as u8);
    v_res_555_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_rat_elim(
        v_motive_550_,
        v_t_boxed_554_,
        v_h_552_,
        v_rat_553_,
    );
    lean_dec(v_rat_553_);
    return v_res_555_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(
    mut v_int_556_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_int_556_);
    return v_int_556_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg___boxed(
    mut v_int_557_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_558_: *mut LeanObject = core::ptr::null_mut();
    v_res_558_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___redArg(v_int_557_);
    lean_dec(v_int_557_);
    return v_res_558_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(
    mut v_motive_559_: *mut LeanObject,
    mut v_t_560_: u8,
    mut v_h_561_: *mut LeanObject,
    mut v_int_562_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_int_562_);
    return v_int_562_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim___boxed(
    mut v_motive_563_: *mut LeanObject,
    mut v_t_564_: *mut LeanObject,
    mut v_h_565_: *mut LeanObject,
    mut v_int_566_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_t_boxed_567_: u8 = 0;
    let mut v_res_568_: *mut LeanObject = core::ptr::null_mut();
    v_t_boxed_567_ = (lean_unbox(v_t_564_) as u8);
    v_res_568_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_int_elim(
        v_motive_563_,
        v_t_boxed_567_,
        v_h_565_,
        v_int_566_,
    );
    lean_dec(v_int_566_);
    return v_res_568_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default() -> u8 {
    let mut v___x_569_: u8 = 0;
    v___x_569_ = 0;
    return v___x_569_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind() -> u8 {
    let mut v___x_570_: u8 = 0;
    v___x_570_ = 0;
    return v___x_570_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(
    mut v_x_571_: u8,
    mut v_y_572_: u8,
) -> u8 {
    let mut v___x_573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_575_: u8 = 0;
    v___x_573_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_x_571_);
    v___x_574_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_Kind_ctorIdx(v_y_572_);
    v___x_575_ = lean_nat_dec_eq(v___x_573_, v___x_574_);
    lean_dec(v___x_574_);
    lean_dec(v___x_573_);
    return v___x_575_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq___boxed(
    mut v_x_576_: *mut LeanObject,
    mut v_y_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_17__boxed_578_: u8 = 0;
    let mut v_y_18__boxed_579_: u8 = 0;
    let mut v_res_580_: u8 = 0;
    let mut v_r_581_: *mut LeanObject = core::ptr::null_mut();
    v_x_17__boxed_578_ = (lean_unbox(v_x_576_) as u8);
    v_y_18__boxed_579_ = (lean_unbox(v_y_577_) as u8);
    v_res_580_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(
        v_x_17__boxed_578_,
        v_y_18__boxed_579_,
    );
    v_r_581_ = lean_box((v_res_580_) as usize);
    return v_r_581_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(
    mut v_a_584_: u8,
) -> *mut LeanObject {
    let mut v___x_586_: u8 = 0;
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_589_: *mut LeanObject = core::ptr::null_mut();
    v___x_586_ = 0;
    v___x_587_ = l_Lean_Meta_Grind_Arith_Cutsat_Search_instBEqKind_beq(v_a_584_, v___x_586_);
    v___x_588_ = lean_box((v___x_587_) as usize);
    v___x_589_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_589_, 0, v___x_588_);
    return v___x_589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg___boxed(
    mut v_a_590_: *mut LeanObject,
    mut v_a_591_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_592_: u8 = 0;
    let mut v_res_593_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_592_ = (lean_unbox(v_a_590_) as u8);
    v_res_593_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_boxed_592_);
    return v_res_593_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isApprox(
    mut v_a_594_: u8,
    mut v_a_595_: *mut LeanObject,
    mut v_a_596_: *mut LeanObject,
    mut v_a_597_: *mut LeanObject,
    mut v_a_598_: *mut LeanObject,
    mut v_a_599_: *mut LeanObject,
    mut v_a_600_: *mut LeanObject,
    mut v_a_601_: *mut LeanObject,
    mut v_a_602_: *mut LeanObject,
    mut v_a_603_: *mut LeanObject,
    mut v_a_604_: *mut LeanObject,
    mut v_a_605_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_607_: *mut LeanObject = core::ptr::null_mut();
    v___x_607_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox___redArg(v_a_594_);
    return v___x_607_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_isApprox___boxed(
    mut v_a_608_: *mut LeanObject,
    mut v_a_609_: *mut LeanObject,
    mut v_a_610_: *mut LeanObject,
    mut v_a_611_: *mut LeanObject,
    mut v_a_612_: *mut LeanObject,
    mut v_a_613_: *mut LeanObject,
    mut v_a_614_: *mut LeanObject,
    mut v_a_615_: *mut LeanObject,
    mut v_a_616_: *mut LeanObject,
    mut v_a_617_: *mut LeanObject,
    mut v_a_618_: *mut LeanObject,
    mut v_a_619_: *mut LeanObject,
    mut v_a_620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_621_: u8 = 0;
    let mut v_res_622_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_621_ = (lean_unbox(v_a_608_) as u8);
    v_res_622_ = l_Lean_Meta_Grind_Arith_Cutsat_isApprox(
        v_a_boxed_621_,
        v_a_609_,
        v_a_610_,
        v_a_611_,
        v_a_612_,
        v_a_613_,
        v_a_614_,
        v_a_615_,
        v_a_616_,
        v_a_617_,
        v_a_618_,
        v_a_619_,
    );
    lean_dec(v_a_619_);
    lean_dec_ref(v_a_618_);
    lean_dec(v_a_617_);
    lean_dec_ref(v_a_616_);
    lean_dec(v_a_615_);
    lean_dec_ref(v_a_614_);
    lean_dec(v_a_613_);
    lean_dec_ref(v_a_612_);
    lean_dec(v_a_611_);
    lean_dec(v_a_610_);
    lean_dec(v_a_609_);
    return v_res_622_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(
    mut v_a_623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decVars_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_630_: u8 = 0;
    let mut v___x_631_: u8 = 0;
    let mut v___x_633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_638_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_625_ = lean_st_ref_take(v_a_623_);
                v_cases_626_ = lean_ctor_get(v___x_625_, 0);
                v_decVars_627_ = lean_ctor_get(v___x_625_, 1);
                v_isSharedCheck_638_ = (!lean_is_exclusive(v___x_625_)) as u8;
                if v_isSharedCheck_638_ == 0 {
                    v___x_629_ = v___x_625_;
                    v_isShared_630_ = v_isSharedCheck_638_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_decVars_627_);
                    lean_inc(v_cases_626_);
                    lean_dec(v___x_625_);
                    v___x_629_ = lean_box(0);
                    v_isShared_630_ = v_isSharedCheck_638_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_631_ = 0;
                if v_isShared_630_ == 0 {
                    v___x_633_ = v___x_629_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_637_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_637_, 0, v_cases_626_);
                    lean_ctor_set(v_reuseFailAlloc_637_, 1, v_decVars_627_);
                    v___x_633_ = v_reuseFailAlloc_637_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_633_,
                    (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                    v___x_631_,
                );
                v___x_634_ = lean_st_ref_set(v_a_623_, v___x_633_);
                v___x_635_ = lean_box(0);
                v___x_636_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_636_, 0, v___x_635_);
                return v___x_636_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg___boxed(
    mut v_a_639_: *mut LeanObject,
    mut v_a_640_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_641_: *mut LeanObject = core::ptr::null_mut();
    v_res_641_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_639_);
    lean_dec(v_a_639_);
    return v_res_641_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(
    mut v_a_642_: u8,
    mut v_a_643_: *mut LeanObject,
    mut v_a_644_: *mut LeanObject,
    mut v_a_645_: *mut LeanObject,
    mut v_a_646_: *mut LeanObject,
    mut v_a_647_: *mut LeanObject,
    mut v_a_648_: *mut LeanObject,
    mut v_a_649_: *mut LeanObject,
    mut v_a_650_: *mut LeanObject,
    mut v_a_651_: *mut LeanObject,
    mut v_a_652_: *mut LeanObject,
    mut v_a_653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_655_: *mut LeanObject = core::ptr::null_mut();
    v___x_655_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___redArg(v_a_643_);
    return v___x_655_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_setImprecise___boxed(
    mut v_a_656_: *mut LeanObject,
    mut v_a_657_: *mut LeanObject,
    mut v_a_658_: *mut LeanObject,
    mut v_a_659_: *mut LeanObject,
    mut v_a_660_: *mut LeanObject,
    mut v_a_661_: *mut LeanObject,
    mut v_a_662_: *mut LeanObject,
    mut v_a_663_: *mut LeanObject,
    mut v_a_664_: *mut LeanObject,
    mut v_a_665_: *mut LeanObject,
    mut v_a_666_: *mut LeanObject,
    mut v_a_667_: *mut LeanObject,
    mut v_a_668_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_669_: u8 = 0;
    let mut v_res_670_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_669_ = (lean_unbox(v_a_656_) as u8);
    v_res_670_ = l_Lean_Meta_Grind_Arith_Cutsat_setImprecise(
        v_a_boxed_669_,
        v_a_657_,
        v_a_658_,
        v_a_659_,
        v_a_660_,
        v_a_661_,
        v_a_662_,
        v_a_663_,
        v_a_664_,
        v_a_665_,
        v_a_666_,
        v_a_667_,
    );
    lean_dec(v_a_667_);
    lean_dec_ref(v_a_666_);
    lean_dec(v_a_665_);
    lean_dec_ref(v_a_664_);
    lean_dec(v_a_663_);
    lean_dec_ref(v_a_662_);
    lean_dec(v_a_661_);
    lean_dec_ref(v_a_660_);
    lean_dec(v_a_659_);
    lean_dec(v_a_658_);
    lean_dec(v_a_657_);
    return v_res_670_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkCase___lam__0(
    mut v_s_671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_vars_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_x27_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_x27_675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natToIntMap_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natDef_677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dvds_678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimEqs_682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_elimStack_683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_occurs_684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_assignment_685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextCnstrId_686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_conflict_x3f_687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqSplits_688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_divMod_689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntIds_690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntInfos_691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntTermMap_692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toIntVarMap_693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_usedCommRing_694_: u8 = 0;
    let mut v_nonlinearOccs_695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_698_: u8 = 0;
    let mut v___x_699_: u8 = 0;
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_703_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vars_672_ = lean_ctor_get(v_s_671_, 0);
                v_varMap_673_ = lean_ctor_get(v_s_671_, 1);
                v_vars_x27_674_ = lean_ctor_get(v_s_671_, 2);
                v_varMap_x27_675_ = lean_ctor_get(v_s_671_, 3);
                v_natToIntMap_676_ = lean_ctor_get(v_s_671_, 4);
                v_natDef_677_ = lean_ctor_get(v_s_671_, 5);
                v_dvds_678_ = lean_ctor_get(v_s_671_, 6);
                v_lowers_679_ = lean_ctor_get(v_s_671_, 7);
                v_uppers_680_ = lean_ctor_get(v_s_671_, 8);
                v_diseqs_681_ = lean_ctor_get(v_s_671_, 9);
                v_elimEqs_682_ = lean_ctor_get(v_s_671_, 10);
                v_elimStack_683_ = lean_ctor_get(v_s_671_, 11);
                v_occurs_684_ = lean_ctor_get(v_s_671_, 12);
                v_assignment_685_ = lean_ctor_get(v_s_671_, 13);
                v_nextCnstrId_686_ = lean_ctor_get(v_s_671_, 14);
                v_conflict_x3f_687_ = lean_ctor_get(v_s_671_, 15);
                v_diseqSplits_688_ = lean_ctor_get(v_s_671_, 16);
                v_divMod_689_ = lean_ctor_get(v_s_671_, 17);
                v_toIntIds_690_ = lean_ctor_get(v_s_671_, 18);
                v_toIntInfos_691_ = lean_ctor_get(v_s_671_, 19);
                v_toIntTermMap_692_ = lean_ctor_get(v_s_671_, 20);
                v_toIntVarMap_693_ = lean_ctor_get(v_s_671_, 21);
                v_usedCommRing_694_ = lean_ctor_get_uint8(
                    v_s_671_,
                    (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                );
                v_nonlinearOccs_695_ = lean_ctor_get(v_s_671_, 22);
                v_isSharedCheck_703_ = (!lean_is_exclusive(v_s_671_)) as u8;
                if v_isSharedCheck_703_ == 0 {
                    v___x_697_ = v_s_671_;
                    v_isShared_698_ = v_isSharedCheck_703_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_nonlinearOccs_695_);
                    lean_inc(v_toIntVarMap_693_);
                    lean_inc(v_toIntTermMap_692_);
                    lean_inc(v_toIntInfos_691_);
                    lean_inc(v_toIntIds_690_);
                    lean_inc(v_divMod_689_);
                    lean_inc(v_diseqSplits_688_);
                    lean_inc(v_conflict_x3f_687_);
                    lean_inc(v_nextCnstrId_686_);
                    lean_inc(v_assignment_685_);
                    lean_inc(v_occurs_684_);
                    lean_inc(v_elimStack_683_);
                    lean_inc(v_elimEqs_682_);
                    lean_inc(v_diseqs_681_);
                    lean_inc(v_uppers_680_);
                    lean_inc(v_lowers_679_);
                    lean_inc(v_dvds_678_);
                    lean_inc(v_natDef_677_);
                    lean_inc(v_natToIntMap_676_);
                    lean_inc(v_varMap_x27_675_);
                    lean_inc(v_vars_x27_674_);
                    lean_inc(v_varMap_673_);
                    lean_inc(v_vars_672_);
                    lean_dec(v_s_671_);
                    v___x_697_ = lean_box(0);
                    v_isShared_698_ = v_isSharedCheck_703_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_699_ = 1;
                if v_isShared_698_ == 0 {
                    v___x_701_ = v___x_697_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 23, (2) as u32);
                    lean_ctor_set(v_reuseFailAlloc_702_, 0, v_vars_672_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 1, v_varMap_673_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 2, v_vars_x27_674_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 3, v_varMap_x27_675_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 4, v_natToIntMap_676_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 5, v_natDef_677_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 6, v_dvds_678_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 7, v_lowers_679_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 8, v_uppers_680_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 9, v_diseqs_681_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 10, v_elimEqs_682_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 11, v_elimStack_683_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 12, v_occurs_684_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 13, v_assignment_685_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 14, v_nextCnstrId_686_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 15, v_conflict_x3f_687_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 16, v_diseqSplits_688_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 17, v_divMod_689_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 18, v_toIntIds_690_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 19, v_toIntInfos_691_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 20, v_toIntTermMap_692_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 21, v_toIntVarMap_693_);
                    lean_ctor_set(v_reuseFailAlloc_702_, 22, v_nonlinearOccs_695_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_702_,
                        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
                        v_usedCommRing_694_,
                    );
                    v___x_701_ = v_reuseFailAlloc_702_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_ctor_set_uint8(
                    v___x_701_,
                    (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
                    v___x_699_,
                );
                return v___x_701_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(
    mut v___y_704_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_namePrefix_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_idx_709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_712_: u8 = 0;
    let mut v___x_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_724_: u8 = 0;
    let mut v_r_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_736_: u8 = 0;
    let mut v_unused_737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_738_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_706_ = lean_st_ref_get(v___y_704_);
                v_ngen_707_ = lean_ctor_get(v___x_706_, 2);
                lean_inc_ref(v_ngen_707_);
                lean_dec(v___x_706_);
                v_namePrefix_708_ = lean_ctor_get(v_ngen_707_, 0);
                v_idx_709_ = lean_ctor_get(v_ngen_707_, 1);
                v_isSharedCheck_738_ = (!lean_is_exclusive(v_ngen_707_)) as u8;
                if v_isSharedCheck_738_ == 0 {
                    v___x_711_ = v_ngen_707_;
                    v_isShared_712_ = v_isSharedCheck_738_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_idx_709_);
                    lean_inc(v_namePrefix_708_);
                    lean_dec(v_ngen_707_);
                    v___x_711_ = lean_box(0);
                    v_isShared_712_ = v_isSharedCheck_738_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_713_ = lean_st_ref_take(v___y_704_);
                v_env_714_ = lean_ctor_get(v___x_713_, 0);
                v_nextMacroScope_715_ = lean_ctor_get(v___x_713_, 1);
                v_auxDeclNGen_716_ = lean_ctor_get(v___x_713_, 3);
                v_traceState_717_ = lean_ctor_get(v___x_713_, 4);
                v_cache_718_ = lean_ctor_get(v___x_713_, 5);
                v_messages_719_ = lean_ctor_get(v___x_713_, 6);
                v_infoState_720_ = lean_ctor_get(v___x_713_, 7);
                v_snapshotTasks_721_ = lean_ctor_get(v___x_713_, 8);
                v_isSharedCheck_736_ = (!lean_is_exclusive(v___x_713_)) as u8;
                if v_isSharedCheck_736_ == 0 {
                    v_unused_737_ = lean_ctor_get(v___x_713_, 2);
                    lean_dec(v_unused_737_);
                    v___x_723_ = v___x_713_;
                    v_isShared_724_ = v_isSharedCheck_736_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_721_);
                    lean_inc(v_infoState_720_);
                    lean_inc(v_messages_719_);
                    lean_inc(v_cache_718_);
                    lean_inc(v_traceState_717_);
                    lean_inc(v_auxDeclNGen_716_);
                    lean_inc(v_nextMacroScope_715_);
                    lean_inc(v_env_714_);
                    lean_dec(v___x_713_);
                    v___x_723_ = lean_box(0);
                    v_isShared_724_ = v_isSharedCheck_736_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                lean_inc(v_idx_709_);
                lean_inc(v_namePrefix_708_);
                v_r_725_ = l_Lean_Name_num___override(v_namePrefix_708_, v_idx_709_);
                v___x_726_ = lean_unsigned_to_nat(1);
                v___x_727_ = lean_nat_add(v_idx_709_, v___x_726_);
                lean_dec(v_idx_709_);
                if v_isShared_712_ == 0 {
                    lean_ctor_set(v___x_711_, 1, v___x_727_);
                    v___x_729_ = v___x_711_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_735_, 0, v_namePrefix_708_);
                    lean_ctor_set(v_reuseFailAlloc_735_, 1, v___x_727_);
                    v___x_729_ = v_reuseFailAlloc_735_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_724_ == 0 {
                    lean_ctor_set(v___x_723_, 2, v___x_729_);
                    v___x_731_ = v___x_723_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_734_, 0, v_env_714_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 1, v_nextMacroScope_715_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 2, v___x_729_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 3, v_auxDeclNGen_716_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 4, v_traceState_717_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 5, v_cache_718_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 6, v_messages_719_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 7, v_infoState_720_);
                    lean_ctor_set(v_reuseFailAlloc_734_, 8, v_snapshotTasks_721_);
                    v___x_731_ = v_reuseFailAlloc_734_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_732_ = lean_st_ref_set(v___y_704_, v___x_731_);
                v___x_733_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_733_, 0, v_r_725_);
                return v___x_733_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg___boxed(
    mut v___y_739_: *mut LeanObject,
    mut v___y_740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_741_: *mut LeanObject = core::ptr::null_mut();
    v_res_741_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_739_);
    lean_dec(v___y_739_);
    return v_res_741_;
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(
    mut v___y_742_: u8,
    mut v___y_743_: *mut LeanObject,
    mut v___y_744_: *mut LeanObject,
    mut v___y_745_: *mut LeanObject,
    mut v___y_746_: *mut LeanObject,
    mut v___y_747_: *mut LeanObject,
    mut v___y_748_: *mut LeanObject,
    mut v___y_749_: *mut LeanObject,
    mut v___y_750_: *mut LeanObject,
    mut v___y_751_: *mut LeanObject,
    mut v___y_752_: *mut LeanObject,
    mut v___y_753_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_759_: u8 = 0;
    let mut v___x_761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_755_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_753_);
                v_a_756_ = lean_ctor_get(v___x_755_, 0);
                v_isSharedCheck_763_ = (!lean_is_exclusive(v___x_755_)) as u8;
                if v_isSharedCheck_763_ == 0 {
                    v___x_758_ = v___x_755_;
                    v_isShared_759_ = v_isSharedCheck_763_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_756_);
                    lean_dec(v___x_755_);
                    v___x_758_ = lean_box(0);
                    v_isShared_759_ = v_isSharedCheck_763_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if v_isShared_759_ == 0 {
                    v___x_761_ = v___x_758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_762_, 0, v_a_756_);
                    v___x_761_ = v_reuseFailAlloc_762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0___boxed(
    mut v___y_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
    mut v___y_769_: *mut LeanObject,
    mut v___y_770_: *mut LeanObject,
    mut v___y_771_: *mut LeanObject,
    mut v___y_772_: *mut LeanObject,
    mut v___y_773_: *mut LeanObject,
    mut v___y_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_12224__boxed_777_: u8 = 0;
    let mut v_res_778_: *mut LeanObject = core::ptr::null_mut();
    v___y_12224__boxed_777_ = (lean_unbox(v___y_764_) as u8);
    v_res_778_ = l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(
        v___y_12224__boxed_777_,
        v___y_765_,
        v___y_766_,
        v___y_767_,
        v___y_768_,
        v___y_769_,
        v___y_770_,
        v___y_771_,
        v___y_772_,
        v___y_773_,
        v___y_774_,
        v___y_775_,
    );
    lean_dec(v___y_775_);
    lean_dec_ref(v___y_774_);
    lean_dec(v___y_773_);
    lean_dec_ref(v___y_772_);
    lean_dec(v___y_771_);
    lean_dec_ref(v___y_770_);
    lean_dec(v___y_769_);
    lean_dec_ref(v___y_768_);
    lean_dec(v___y_767_);
    lean_dec(v___y_766_);
    lean_dec(v___y_765_);
    return v_res_778_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkCase(
    mut v_kind_780_: *mut LeanObject,
    mut v_a_781_: u8,
    mut v_a_782_: *mut LeanObject,
    mut v_a_783_: *mut LeanObject,
    mut v_a_784_: *mut LeanObject,
    mut v_a_785_: *mut LeanObject,
    mut v_a_786_: *mut LeanObject,
    mut v_a_787_: *mut LeanObject,
    mut v_a_788_: *mut LeanObject,
    mut v_a_789_: *mut LeanObject,
    mut v_a_790_: *mut LeanObject,
    mut v_a_791_: *mut LeanObject,
    mut v_a_792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_precise_800_: u8 = 0;
    let mut v_decVars_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_816_: u8 = 0;
    let mut v___x_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_820_: u8 = 0;
    let mut v_unused_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_825_: u8 = 0;
    let mut v___x_827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_829_: u8 = 0;
    let mut v_reuseFailAlloc_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_831_: u8 = 0;
    let mut v_a_832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_835_: u8 = 0;
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_794_ =
                    l_Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0(
                        v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_,
                        v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_,
                    );
                if lean_obj_tag(v___x_794_) == 0 {
                    v_a_795_ = lean_ctor_get(v___x_794_, 0);
                    lean_inc(v_a_795_);
                    lean_dec_ref_known(v___x_794_, 1);
                    v___x_796_ =
                        l_Lean_Meta_Grind_Arith_Cutsat_get_x27___redArg(v_a_783_, v_a_791_);
                    if lean_obj_tag(v___x_796_) == 0 {
                        v_a_797_ = lean_ctor_get(v___x_796_, 0);
                        lean_inc(v_a_797_);
                        lean_dec_ref_known(v___x_796_, 1);
                        v___x_798_ = lean_st_ref_take(v_a_782_);
                        v_cases_799_ = lean_ctor_get(v___x_798_, 0);
                        v_precise_800_ = lean_ctor_get_uint8(
                            v___x_798_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        );
                        v_decVars_801_ = lean_ctor_get(v___x_798_, 1);
                        v_isSharedCheck_831_ = (!lean_is_exclusive(v___x_798_)) as u8;
                        if v_isSharedCheck_831_ == 0 {
                            v___x_803_ = v___x_798_;
                            v_isShared_804_ = v_isSharedCheck_831_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_decVars_801_);
                            lean_inc(v_cases_799_);
                            lean_dec(v___x_798_);
                            v___x_803_ = lean_box(0);
                            v_isShared_804_ = v_isSharedCheck_831_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_795_);
                        lean_dec_ref(v_kind_780_);
                        v_a_832_ = lean_ctor_get(v___x_796_, 0);
                        v_isSharedCheck_839_ = (!lean_is_exclusive(v___x_796_)) as u8;
                        if v_isSharedCheck_839_ == 0 {
                            v___x_834_ = v___x_796_;
                            v_isShared_835_ = v_isSharedCheck_839_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_832_);
                            lean_dec(v___x_796_);
                            v___x_834_ = lean_box(0);
                            v_isShared_835_ = v_isSharedCheck_839_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_kind_780_);
                    return v___x_794_;
                }
            }
            1 => {
                lean_inc_n(v_a_795_, 2);
                v___x_805_ = lean_alloc_ctor(0, 3, (0) as u32);
                lean_ctor_set(v___x_805_, 0, v_kind_780_);
                lean_ctor_set(v___x_805_, 1, v_a_795_);
                lean_ctor_set(v___x_805_, 2, v_a_797_);
                v___x_806_ = l_Lean_PersistentArray_push___redArg(v_cases_799_, v___x_805_);
                v___x_807_ = l_Lean_FVarIdSet_insert(v_decVars_801_, v_a_795_);
                if v_isShared_804_ == 0 {
                    lean_ctor_set(v___x_803_, 1, v___x_807_);
                    lean_ctor_set(v___x_803_, 0, v___x_806_);
                    v___x_809_ = v___x_803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_830_ = lean_alloc_ctor(0, 2, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_830_, 0, v___x_806_);
                    lean_ctor_set(v_reuseFailAlloc_830_, 1, v___x_807_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_830_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
                        v_precise_800_,
                    );
                    v___x_809_ = v_reuseFailAlloc_830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_810_ = lean_st_ref_set(v_a_782_, v___x_809_);
                v___f_811_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase___closed__0;
                v___x_812_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                v___x_813_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_812_, v___f_811_, v_a_783_);
                if lean_obj_tag(v___x_813_) == 0 {
                    v_isSharedCheck_820_ = (!lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_820_ == 0 {
                        v_unused_821_ = lean_ctor_get(v___x_813_, 0);
                        lean_dec(v_unused_821_);
                        v___x_815_ = v___x_813_;
                        v_isShared_816_ = v_isSharedCheck_820_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v___x_813_);
                        v___x_815_ = lean_box(0);
                        v_isShared_816_ = v_isSharedCheck_820_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_795_);
                    v_a_822_ = lean_ctor_get(v___x_813_, 0);
                    v_isSharedCheck_829_ = (!lean_is_exclusive(v___x_813_)) as u8;
                    if v_isSharedCheck_829_ == 0 {
                        v___x_824_ = v___x_813_;
                        v_isShared_825_ = v_isSharedCheck_829_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_822_);
                        lean_dec(v___x_813_);
                        v___x_824_ = lean_box(0);
                        v_isShared_825_ = v_isSharedCheck_829_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_816_ == 0 {
                    lean_ctor_set(v___x_815_, 0, v_a_795_);
                    v___x_818_ = v___x_815_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_819_, 0, v_a_795_);
                    v___x_818_ = v_reuseFailAlloc_819_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_818_;
            }
            5 => {
                if v_isShared_825_ == 0 {
                    v___x_827_ = v___x_824_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_828_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_828_, 0, v_a_822_);
                    v___x_827_ = v_reuseFailAlloc_828_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_827_;
            }
            7 => {
                if v_isShared_835_ == 0 {
                    v___x_837_ = v___x_834_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
                    v___x_837_ = v_reuseFailAlloc_838_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_837_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkCase___boxed(
    mut v_kind_840_: *mut LeanObject,
    mut v_a_841_: *mut LeanObject,
    mut v_a_842_: *mut LeanObject,
    mut v_a_843_: *mut LeanObject,
    mut v_a_844_: *mut LeanObject,
    mut v_a_845_: *mut LeanObject,
    mut v_a_846_: *mut LeanObject,
    mut v_a_847_: *mut LeanObject,
    mut v_a_848_: *mut LeanObject,
    mut v_a_849_: *mut LeanObject,
    mut v_a_850_: *mut LeanObject,
    mut v_a_851_: *mut LeanObject,
    mut v_a_852_: *mut LeanObject,
    mut v_a_853_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_boxed_854_: u8 = 0;
    let mut v_res_855_: *mut LeanObject = core::ptr::null_mut();
    v_a_boxed_854_ = (lean_unbox(v_a_841_) as u8);
    v_res_855_ = l_Lean_Meta_Grind_Arith_Cutsat_mkCase(
        v_kind_840_,
        v_a_boxed_854_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        v_a_847_,
        v_a_848_,
        v_a_849_,
        v_a_850_,
        v_a_851_,
        v_a_852_,
    );
    lean_dec(v_a_852_);
    lean_dec_ref(v_a_851_);
    lean_dec(v_a_850_);
    lean_dec_ref(v_a_849_);
    lean_dec(v_a_848_);
    lean_dec_ref(v_a_847_);
    lean_dec(v_a_846_);
    lean_dec_ref(v_a_845_);
    lean_dec(v_a_844_);
    lean_dec(v_a_843_);
    lean_dec(v_a_842_);
    return v_res_855_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(
    mut v___y_856_: u8,
    mut v___y_857_: *mut LeanObject,
    mut v___y_858_: *mut LeanObject,
    mut v___y_859_: *mut LeanObject,
    mut v___y_860_: *mut LeanObject,
    mut v___y_861_: *mut LeanObject,
    mut v___y_862_: *mut LeanObject,
    mut v___y_863_: *mut LeanObject,
    mut v___y_864_: *mut LeanObject,
    mut v___y_865_: *mut LeanObject,
    mut v___y_866_: *mut LeanObject,
    mut v___y_867_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_869_: *mut LeanObject = core::ptr::null_mut();
    v___x_869_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___redArg(v___y_867_);
    return v___x_869_;
}
pub unsafe fn l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0___boxed(
    mut v___y_870_: *mut LeanObject,
    mut v___y_871_: *mut LeanObject,
    mut v___y_872_: *mut LeanObject,
    mut v___y_873_: *mut LeanObject,
    mut v___y_874_: *mut LeanObject,
    mut v___y_875_: *mut LeanObject,
    mut v___y_876_: *mut LeanObject,
    mut v___y_877_: *mut LeanObject,
    mut v___y_878_: *mut LeanObject,
    mut v___y_879_: *mut LeanObject,
    mut v___y_880_: *mut LeanObject,
    mut v___y_881_: *mut LeanObject,
    mut v___y_882_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_12376__boxed_883_: u8 = 0;
    let mut v_res_884_: *mut LeanObject = core::ptr::null_mut();
    v___y_12376__boxed_883_ = (lean_unbox(v___y_870_) as u8);
    v_res_884_ = l_Lean_mkFreshId___at___00Lean_mkFreshFVarId___at___00Lean_Meta_Grind_Arith_Cutsat_mkCase_spec__0_spec__0(v___y_12376__boxed_883_, v___y_871_, v___y_872_, v___y_873_, v___y_874_, v___y_875_, v___y_876_, v___y_877_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
    lean_dec(v___y_881_);
    lean_dec_ref(v___y_880_);
    lean_dec(v___y_879_);
    lean_dec_ref(v___y_878_);
    lean_dec(v___y_877_);
    lean_dec_ref(v___y_876_);
    lean_dec(v___y_875_);
    lean_dec_ref(v___y_874_);
    lean_dec(v___y_873_);
    lean_dec(v___y_872_);
    lean_dec(v___y_871_);
    return v_res_884_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind_default);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCaseKind);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase_default);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCase);
    l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind_default();
    l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_Search_instInhabitedKind();
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_SearchM(builtin);
}

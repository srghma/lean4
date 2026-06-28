// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types
// Imports: Init.Data.Int.Linear Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.ToIntInfo
use crate::r#gen::Init::Data::Int::Linear::{
    initialize_Init_Data_Int_Linear, runtime_initialize_Init_Data_Int_Linear,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_Expr_const___override;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::ToIntInfo::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_registerSolverExtension___redArg;
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_lt, lean_nat_abs, lean_nat_to_int,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::lean_uint64_of_nat;
use crate::lean_imports_rs::Init::Prelude::{
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_mul, lean_nat_sub,
    lean_uint64_mix_hash,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_apply_5, lean_apply_7, lean_box,
    lean_box_uint64, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set,
    lean_ctor_set_uint8, lean_ctor_set_usize, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_inc_ref, lean_io_result_get_value, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_mark_persistent, lean_obj_once, lean_obj_tag, lean_unsigned_to_nat,
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value:
    LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value)
        as *mut LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value: LeanStringObject<
    20,
> = LeanStringObject {
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value: LeanCtorObject<
    3,
> = LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__1_value)
            as *mut LeanObject,
        17542774118954891045 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value:
    LeanCtorObject<1> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState: *mut LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0()
-> *mut LeanObject {
    let mut v_natZero_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_intZero_967_: *mut LeanObject = core::ptr::null_mut();
    v_natZero_966_ = lean_unsigned_to_nat(0);
    v_intZero_967_ = lean_nat_to_int(v_natZero_966_);
    return v_intZero_967_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(
    mut v_x_968_: *mut LeanObject,
) -> u64 {
    let mut v_k_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_970_: u64 = 0;
    let mut v_intZero_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_972_: u8 = 0;
    let mut v_a_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_976_: u64 = 0;
    let mut v___x_977_: u64 = 0;
    let mut v_abs_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: u64 = 0;
    let mut v___x_985_: u64 = 0;
    let mut v_k_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_987_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_989_: u64 = 0;
    let mut v___y_991_: u64 = 0;
    let mut v___x_992_: u64 = 0;
    let mut v___x_993_: u64 = 0;
    let mut v___x_994_: u64 = 0;
    let mut v___x_995_: u64 = 0;
    let mut v___x_996_: u64 = 0;
    let mut v_intZero_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isNeg_998_: u8 = 0;
    let mut v_a_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1002_: u64 = 0;
    let mut v_abs_1003_: *mut LeanObject = core::ptr::null_mut();
    let mut v_one_1004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_968_) == 0 {
                    v_k_969_ = lean_ctor_get(v_x_968_, 0);
                    v___x_970_ = 0u64;
                    v_intZero_971_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_972_ = lean_int_dec_lt(v_k_969_, v_intZero_971_);
                    if v_isNeg_972_ == 0 {
                        v_a_973_ = lean_nat_abs(v_k_969_);
                        v___x_974_ = lean_unsigned_to_nat(2);
                        v___x_975_ = lean_nat_mul(v___x_974_, v_a_973_);
                        lean_dec(v_a_973_);
                        v___x_976_ = lean_uint64_of_nat(v___x_975_);
                        lean_dec(v___x_975_);
                        v___x_977_ = lean_uint64_mix_hash(v___x_970_, v___x_976_);
                        return v___x_977_;
                    } else {
                        v_abs_978_ = lean_nat_abs(v_k_969_);
                        v_one_979_ = lean_unsigned_to_nat(1);
                        v_a_980_ = lean_nat_sub(v_abs_978_, v_one_979_);
                        lean_dec(v_abs_978_);
                        v___x_981_ = lean_unsigned_to_nat(2);
                        v___x_982_ = lean_nat_mul(v___x_981_, v_a_980_);
                        lean_dec(v_a_980_);
                        v___x_983_ = lean_nat_add(v___x_982_, v_one_979_);
                        lean_dec(v___x_982_);
                        v___x_984_ = lean_uint64_of_nat(v___x_983_);
                        lean_dec(v___x_983_);
                        v___x_985_ = lean_uint64_mix_hash(v___x_970_, v___x_984_);
                        return v___x_985_;
                    }
                } else {
                    v_k_986_ = lean_ctor_get(v_x_968_, 0);
                    v_v_987_ = lean_ctor_get(v_x_968_, 1);
                    v_p_988_ = lean_ctor_get(v_x_968_, 2);
                    v___x_989_ = 1u64;
                    v_intZero_997_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once), _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0);
                    v_isNeg_998_ = lean_int_dec_lt(v_k_986_, v_intZero_997_);
                    if v_isNeg_998_ == 0 {
                        v_a_999_ = lean_nat_abs(v_k_986_);
                        v___x_1000_ = lean_unsigned_to_nat(2);
                        v___x_1001_ = lean_nat_mul(v___x_1000_, v_a_999_);
                        lean_dec(v_a_999_);
                        v___x_1002_ = lean_uint64_of_nat(v___x_1001_);
                        lean_dec(v___x_1001_);
                        v___y_991_ = v___x_1002_;
                        state = 1;
                        continue;
                    } else {
                        v_abs_1003_ = lean_nat_abs(v_k_986_);
                        v_one_1004_ = lean_unsigned_to_nat(1);
                        v_a_1005_ = lean_nat_sub(v_abs_1003_, v_one_1004_);
                        lean_dec(v_abs_1003_);
                        v___x_1006_ = lean_unsigned_to_nat(2);
                        v___x_1007_ = lean_nat_mul(v___x_1006_, v_a_1005_);
                        lean_dec(v_a_1005_);
                        v___x_1008_ = lean_nat_add(v___x_1007_, v_one_1004_);
                        lean_dec(v___x_1007_);
                        v___x_1009_ = lean_uint64_of_nat(v___x_1008_);
                        lean_dec(v___x_1008_);
                        v___y_991_ = v___x_1009_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_992_ = lean_uint64_mix_hash(v___x_989_, v___y_991_);
                v___x_993_ = lean_uint64_of_nat(v_v_987_);
                v___x_994_ = lean_uint64_mix_hash(v___x_992_, v___x_993_);
                v___x_995_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_p_988_);
                v___x_996_ = lean_uint64_mix_hash(v___x_994_, v___x_995_);
                return v___x_996_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___boxed(
    mut v_x_1010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1011_: u64 = 0;
    let mut v_r_1012_: *mut LeanObject = core::ptr::null_mut();
    v_res_1011_ = l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash(v_x_1010_);
    lean_dec_ref(v_x_1010_);
    v_r_1012_ = lean_box_uint64(v_res_1011_);
    return v_r_1012_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(
    mut v_x_1015_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1015_) {
        0 => {
            let mut v___x_1016_: *mut LeanObject = core::ptr::null_mut();
            v___x_1016_ = lean_unsigned_to_nat(0);
            return v___x_1016_;
        }
        1 => {
            let mut v___x_1017_: *mut LeanObject = core::ptr::null_mut();
            v___x_1017_ = lean_unsigned_to_nat(1);
            return v___x_1017_;
        }
        2 => {
            let mut v___x_1018_: *mut LeanObject = core::ptr::null_mut();
            v___x_1018_ = lean_unsigned_to_nat(2);
            return v___x_1018_;
        }
        3 => {
            let mut v___x_1019_: *mut LeanObject = core::ptr::null_mut();
            v___x_1019_ = lean_unsigned_to_nat(3);
            return v___x_1019_;
        }
        4 => {
            let mut v___x_1020_: *mut LeanObject = core::ptr::null_mut();
            v___x_1020_ = lean_unsigned_to_nat(4);
            return v___x_1020_;
        }
        5 => {
            let mut v___x_1021_: *mut LeanObject = core::ptr::null_mut();
            v___x_1021_ = lean_unsigned_to_nat(5);
            return v___x_1021_;
        }
        6 => {
            let mut v___x_1022_: *mut LeanObject = core::ptr::null_mut();
            v___x_1022_ = lean_unsigned_to_nat(6);
            return v___x_1022_;
        }
        7 => {
            let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
            v___x_1023_ = lean_unsigned_to_nat(7);
            return v___x_1023_;
        }
        8 => {
            let mut v___x_1024_: *mut LeanObject = core::ptr::null_mut();
            v___x_1024_ = lean_unsigned_to_nat(8);
            return v___x_1024_;
        }
        9 => {
            let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
            v___x_1025_ = lean_unsigned_to_nat(9);
            return v___x_1025_;
        }
        10 => {
            let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
            v___x_1026_ = lean_unsigned_to_nat(10);
            return v___x_1026_;
        }
        11 => {
            let mut v___x_1027_: *mut LeanObject = core::ptr::null_mut();
            v___x_1027_ = lean_unsigned_to_nat(11);
            return v___x_1027_;
        }
        12 => {
            let mut v___x_1028_: *mut LeanObject = core::ptr::null_mut();
            v___x_1028_ = lean_unsigned_to_nat(12);
            return v___x_1028_;
        }
        13 => {
            let mut v___x_1029_: *mut LeanObject = core::ptr::null_mut();
            v___x_1029_ = lean_unsigned_to_nat(13);
            return v___x_1029_;
        }
        14 => {
            let mut v___x_1030_: *mut LeanObject = core::ptr::null_mut();
            v___x_1030_ = lean_unsigned_to_nat(14);
            return v___x_1030_;
        }
        15 => {
            let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
            v___x_1031_ = lean_unsigned_to_nat(15);
            return v___x_1031_;
        }
        _ => {
            let mut v___x_1032_: *mut LeanObject = core::ptr::null_mut();
            v___x_1032_ = lean_unsigned_to_nat(16);
            return v___x_1032_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx___boxed(
    mut v_x_1033_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1034_: *mut LeanObject = core::ptr::null_mut();
    v_res_1034_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorIdx(v_x_1033_);
    lean_dec_ref(v_x_1033_);
    return v_res_1034_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
    mut v_t_1035_: *mut LeanObject,
    mut v_k_1036_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1035_) {
        1 => {
            let mut v_a_1037_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1038_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2081_1039_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2082_1040_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1041_: *mut LeanObject = core::ptr::null_mut();
            v_a_1037_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_a_1037_);
            v_b_1038_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_b_1038_);
            v_p_u2081_1039_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_p_u2081_1039_);
            v_p_u2082_1040_ = lean_ctor_get(v_t_1035_, 3);
            lean_inc_ref(v_p_u2082_1040_);
            lean_dec_ref_known(v_t_1035_, 4);
            v___x_1041_ = lean_apply_4(
                v_k_1036_,
                v_a_1037_,
                v_b_1038_,
                v_p_u2081_1039_,
                v_p_u2082_1040_,
            );
            return v___x_1041_;
        }
        2 => {
            let mut v_a_1042_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1043_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toIntThm_1044_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_1045_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_1046_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
            v_a_1042_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_a_1042_);
            v_b_1043_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_b_1043_);
            v_toIntThm_1044_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_toIntThm_1044_);
            v_lhs_1045_ = lean_ctor_get(v_t_1035_, 3);
            lean_inc_ref(v_lhs_1045_);
            v_rhs_1046_ = lean_ctor_get(v_t_1035_, 4);
            lean_inc_ref(v_rhs_1046_);
            lean_dec_ref_known(v_t_1035_, 5);
            v___x_1047_ = lean_apply_5(
                v_k_1036_,
                v_a_1042_,
                v_b_1043_,
                v_toIntThm_1044_,
                v_lhs_1045_,
                v_rhs_1046_,
            );
            return v___x_1047_;
        }
        4 => {
            let mut v_h_1048_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1049_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_x27_1050_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
            v_h_1048_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_h_1048_);
            v_x_1049_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc(v_x_1049_);
            v_e_x27_1050_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_e_x27_1050_);
            lean_dec_ref_known(v_t_1035_, 3);
            v___x_1051_ = lean_apply_3(v_k_1036_, v_h_1048_, v_x_1049_, v_e_x27_1050_);
            return v___x_1051_;
        }
        5 => {
            let mut v_c_1052_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1053_: *mut LeanObject = core::ptr::null_mut();
            v_c_1052_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_c_1052_);
            lean_dec_ref_known(v_t_1035_, 1);
            v___x_1053_ = lean_apply_1(v_k_1036_, v_c_1052_);
            return v___x_1053_;
        }
        6 => {
            let mut v_c_1054_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1055_: *mut LeanObject = core::ptr::null_mut();
            v_c_1054_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_c_1054_);
            lean_dec_ref_known(v_t_1035_, 1);
            v___x_1055_ = lean_apply_1(v_k_1036_, v_c_1054_);
            return v___x_1055_;
        }
        7 => {
            let mut v_x_1056_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1057_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1058_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
            v_x_1056_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc(v_x_1056_);
            v_c_u2081_1057_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_c_u2081_1057_);
            v_c_u2082_1058_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_c_u2082_1058_);
            lean_dec_ref_known(v_t_1035_, 3);
            v___x_1059_ = lean_apply_3(v_k_1036_, v_x_1056_, v_c_u2081_1057_, v_c_u2082_1058_);
            return v___x_1059_;
        }
        9 => {
            let mut v_c_1060_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
            v_c_1060_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_c_1060_);
            lean_dec_ref_known(v_t_1035_, 1);
            v___x_1061_ = lean_apply_1(v_k_1036_, v_c_1060_);
            return v___x_1061_;
        }
        10 => {
            let mut v_c_1062_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_1063_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1064_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1065_: *mut LeanObject = core::ptr::null_mut();
            v_c_1062_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_c_1062_);
            v_e_1063_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_e_1063_);
            v_p_1064_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_p_1064_);
            lean_dec_ref_known(v_t_1035_, 3);
            v___x_1065_ = lean_apply_3(v_k_1036_, v_c_1062_, v_e_1063_, v_p_1064_);
            return v___x_1065_;
        }
        11 => {
            let mut v_e_1066_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1067_: *mut LeanObject = core::ptr::null_mut();
            let mut v_re_1068_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rp_1069_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_x27_1070_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
            v_e_1066_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_e_1066_);
            v_p_1067_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_p_1067_);
            v_re_1068_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_re_1068_);
            v_rp_1069_ = lean_ctor_get(v_t_1035_, 3);
            lean_inc_ref(v_rp_1069_);
            v_p_x27_1070_ = lean_ctor_get(v_t_1035_, 4);
            lean_inc_ref(v_p_x27_1070_);
            lean_dec_ref_known(v_t_1035_, 5);
            v___x_1071_ = lean_apply_5(
                v_k_1036_,
                v_e_1066_,
                v_p_1067_,
                v_re_1068_,
                v_rp_1069_,
                v_p_x27_1070_,
            );
            return v___x_1071_;
        }
        12 => {
            let mut v_h_1072_: *mut LeanObject = core::ptr::null_mut();
            let mut v_x_1073_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_x27_1074_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1075_: *mut LeanObject = core::ptr::null_mut();
            let mut v_re_1076_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rp_1077_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_x27_1078_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1079_: *mut LeanObject = core::ptr::null_mut();
            v_h_1072_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_h_1072_);
            v_x_1073_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc(v_x_1073_);
            v_e_x27_1074_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_e_x27_1074_);
            v_p_1075_ = lean_ctor_get(v_t_1035_, 3);
            lean_inc_ref(v_p_1075_);
            v_re_1076_ = lean_ctor_get(v_t_1035_, 4);
            lean_inc_ref(v_re_1076_);
            v_rp_1077_ = lean_ctor_get(v_t_1035_, 5);
            lean_inc_ref(v_rp_1077_);
            v_p_x27_1078_ = lean_ctor_get(v_t_1035_, 6);
            lean_inc_ref(v_p_x27_1078_);
            lean_dec_ref_known(v_t_1035_, 7);
            v___x_1079_ = lean_apply_7(
                v_k_1036_,
                v_h_1072_,
                v_x_1073_,
                v_e_x27_1074_,
                v_p_1075_,
                v_re_1076_,
                v_rp_1077_,
                v_p_x27_1078_,
            );
            return v___x_1079_;
        }
        13 => {
            let mut v_a_x3f_1080_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cs_1081_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
            v_a_x3f_1080_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc(v_a_x3f_1080_);
            v_cs_1081_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_cs_1081_);
            lean_dec_ref_known(v_t_1035_, 2);
            v___x_1082_ = lean_apply_2(v_k_1036_, v_a_x3f_1080_, v_cs_1081_);
            return v___x_1082_;
        }
        14 => {
            let mut v_k_1083_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_x3f_1084_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_1085_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
            v_k_1083_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc(v_k_1083_);
            v_y_x3f_1084_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc(v_y_x3f_1084_);
            v_c_1085_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_c_1085_);
            lean_dec_ref_known(v_t_1035_, 3);
            v___x_1086_ = lean_apply_3(v_k_1036_, v_k_1083_, v_y_x3f_1084_, v_c_1085_);
            return v___x_1086_;
        }
        15 => {
            let mut v_k_1087_: *mut LeanObject = core::ptr::null_mut();
            let mut v_y_x3f_1088_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_1089_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1090_: *mut LeanObject = core::ptr::null_mut();
            v_k_1087_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc(v_k_1087_);
            v_y_x3f_1088_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc(v_y_x3f_1088_);
            v_c_1089_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc_ref(v_c_1089_);
            lean_dec_ref_known(v_t_1035_, 3);
            v___x_1090_ = lean_apply_3(v_k_1036_, v_k_1087_, v_y_x3f_1088_, v_c_1089_);
            return v___x_1090_;
        }
        16 => {
            let mut v_ka_1091_: *mut LeanObject = core::ptr::null_mut();
            let mut v_ca_x3f_1092_: *mut LeanObject = core::ptr::null_mut();
            let mut v_kb_1093_: *mut LeanObject = core::ptr::null_mut();
            let mut v_cb_x3f_1094_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1095_: *mut LeanObject = core::ptr::null_mut();
            v_ka_1091_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc(v_ka_1091_);
            v_ca_x3f_1092_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc(v_ca_x3f_1092_);
            v_kb_1093_ = lean_ctor_get(v_t_1035_, 2);
            lean_inc(v_kb_1093_);
            v_cb_x3f_1094_ = lean_ctor_get(v_t_1035_, 3);
            lean_inc(v_cb_x3f_1094_);
            lean_dec_ref_known(v_t_1035_, 4);
            v___x_1095_ = lean_apply_4(
                v_k_1036_,
                v_ka_1091_,
                v_ca_x3f_1092_,
                v_kb_1093_,
                v_cb_x3f_1094_,
            );
            return v___x_1095_;
        }
        _ => {
            let mut v_a_1096_: *mut LeanObject = core::ptr::null_mut();
            let mut v_zero_1097_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1098_: *mut LeanObject = core::ptr::null_mut();
            v_a_1096_ = lean_ctor_get(v_t_1035_, 0);
            lean_inc_ref(v_a_1096_);
            v_zero_1097_ = lean_ctor_get(v_t_1035_, 1);
            lean_inc_ref(v_zero_1097_);
            lean_dec_ref(v_t_1035_);
            v___x_1098_ = lean_apply_2(v_k_1036_, v_a_1096_, v_zero_1097_);
            return v___x_1098_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(
    mut v_motive__2_1099_: *mut LeanObject,
    mut v_ctorIdx_1100_: *mut LeanObject,
    mut v_t_1101_: *mut LeanObject,
    mut v_h_1102_: *mut LeanObject,
    mut v_k_1103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    v___x_1104_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1101_, v_k_1103_);
    return v___x_1104_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___boxed(
    mut v_motive__2_1105_: *mut LeanObject,
    mut v_ctorIdx_1106_: *mut LeanObject,
    mut v_t_1107_: *mut LeanObject,
    mut v_h_1108_: *mut LeanObject,
    mut v_k_1109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1110_: *mut LeanObject = core::ptr::null_mut();
    v_res_1110_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim(
        v_motive__2_1105_,
        v_ctorIdx_1106_,
        v_t_1107_,
        v_h_1108_,
        v_k_1109_,
    );
    lean_dec(v_ctorIdx_1106_);
    return v_res_1110_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim___redArg(
    mut v_t_1111_: *mut LeanObject,
    mut v_core0_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    v___x_1113_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1111_, v_core0_1112_);
    return v___x_1113_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core0_elim(
    mut v_motive__2_1114_: *mut LeanObject,
    mut v_t_1115_: *mut LeanObject,
    mut v_h_1116_: *mut LeanObject,
    mut v_core0_1117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
    v___x_1118_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1115_, v_core0_1117_);
    return v___x_1118_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim___redArg(
    mut v_t_1119_: *mut LeanObject,
    mut v_core_1120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
    v___x_1121_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1119_, v_core_1120_);
    return v___x_1121_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_core_elim(
    mut v_motive__2_1122_: *mut LeanObject,
    mut v_t_1123_: *mut LeanObject,
    mut v_h_1124_: *mut LeanObject,
    mut v_core_1125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1126_: *mut LeanObject = core::ptr::null_mut();
    v___x_1126_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1123_, v_core_1125_);
    return v___x_1126_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim___redArg(
    mut v_t_1127_: *mut LeanObject,
    mut v_coreToInt_1128_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1129_: *mut LeanObject = core::ptr::null_mut();
    v___x_1129_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1127_, v_coreToInt_1128_);
    return v___x_1129_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_coreToInt_elim(
    mut v_motive__2_1130_: *mut LeanObject,
    mut v_t_1131_: *mut LeanObject,
    mut v_h_1132_: *mut LeanObject,
    mut v_coreToInt_1133_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
    v___x_1134_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1131_, v_coreToInt_1133_);
    return v___x_1134_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim___redArg(
    mut v_t_1135_: *mut LeanObject,
    mut v_defn_1136_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
    v___x_1137_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1135_, v_defn_1136_);
    return v___x_1137_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defn_elim(
    mut v_motive__2_1138_: *mut LeanObject,
    mut v_t_1139_: *mut LeanObject,
    mut v_h_1140_: *mut LeanObject,
    mut v_defn_1141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1142_: *mut LeanObject = core::ptr::null_mut();
    v___x_1142_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1139_, v_defn_1141_);
    return v___x_1142_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim___redArg(
    mut v_t_1143_: *mut LeanObject,
    mut v_defnNat_1144_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1145_: *mut LeanObject = core::ptr::null_mut();
    v___x_1145_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1143_, v_defnNat_1144_);
    return v___x_1145_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNat_elim(
    mut v_motive__2_1146_: *mut LeanObject,
    mut v_t_1147_: *mut LeanObject,
    mut v_h_1148_: *mut LeanObject,
    mut v_defnNat_1149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
    v___x_1150_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1147_, v_defnNat_1149_);
    return v___x_1150_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim___redArg(
    mut v_t_1151_: *mut LeanObject,
    mut v_norm_1152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1153_: *mut LeanObject = core::ptr::null_mut();
    v___x_1153_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1151_, v_norm_1152_);
    return v___x_1153_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_norm_elim(
    mut v_motive__2_1154_: *mut LeanObject,
    mut v_t_1155_: *mut LeanObject,
    mut v_h_1156_: *mut LeanObject,
    mut v_norm_1157_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
    v___x_1158_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1155_, v_norm_1157_);
    return v___x_1158_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1159_: *mut LeanObject,
    mut v_divCoeffs_1160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
    v___x_1161_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1159_, v_divCoeffs_1160_);
    return v___x_1161_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_divCoeffs_elim(
    mut v_motive__2_1162_: *mut LeanObject,
    mut v_t_1163_: *mut LeanObject,
    mut v_h_1164_: *mut LeanObject,
    mut v_divCoeffs_1165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1166_: *mut LeanObject = core::ptr::null_mut();
    v___x_1166_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1163_, v_divCoeffs_1165_);
    return v___x_1166_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim___redArg(
    mut v_t_1167_: *mut LeanObject,
    mut v_subst_1168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1169_: *mut LeanObject = core::ptr::null_mut();
    v___x_1169_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1167_, v_subst_1168_);
    return v___x_1169_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_subst_elim(
    mut v_motive__2_1170_: *mut LeanObject,
    mut v_t_1171_: *mut LeanObject,
    mut v_h_1172_: *mut LeanObject,
    mut v_subst_1173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1174_: *mut LeanObject = core::ptr::null_mut();
    v___x_1174_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1171_, v_subst_1173_);
    return v___x_1174_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim___redArg(
    mut v_t_1175_: *mut LeanObject,
    mut v_ofLeGe_1176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
    v___x_1177_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1175_, v_ofLeGe_1176_);
    return v___x_1177_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ofLeGe_elim(
    mut v_motive__2_1178_: *mut LeanObject,
    mut v_t_1179_: *mut LeanObject,
    mut v_h_1180_: *mut LeanObject,
    mut v_ofLeGe_1181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1182_: *mut LeanObject = core::ptr::null_mut();
    v___x_1182_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1179_, v_ofLeGe_1181_);
    return v___x_1182_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim___redArg(
    mut v_t_1183_: *mut LeanObject,
    mut v_reorder_1184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
    v___x_1185_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1183_, v_reorder_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_reorder_elim(
    mut v_motive__2_1186_: *mut LeanObject,
    mut v_t_1187_: *mut LeanObject,
    mut v_h_1188_: *mut LeanObject,
    mut v_reorder_1189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1190_: *mut LeanObject = core::ptr::null_mut();
    v___x_1190_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1187_, v_reorder_1189_);
    return v___x_1190_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1191_: *mut LeanObject,
    mut v_commRingNorm_1192_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1193_: *mut LeanObject = core::ptr::null_mut();
    v___x_1193_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1191_,
        v_commRingNorm_1192_,
    );
    return v___x_1193_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_commRingNorm_elim(
    mut v_motive__2_1194_: *mut LeanObject,
    mut v_t_1195_: *mut LeanObject,
    mut v_h_1196_: *mut LeanObject,
    mut v_commRingNorm_1197_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1198_: *mut LeanObject = core::ptr::null_mut();
    v___x_1198_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1195_,
        v_commRingNorm_1197_,
    );
    return v___x_1198_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim___redArg(
    mut v_t_1199_: *mut LeanObject,
    mut v_defnCommRing_1200_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1199_,
        v_defnCommRing_1200_,
    );
    return v___x_1201_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnCommRing_elim(
    mut v_motive__2_1202_: *mut LeanObject,
    mut v_t_1203_: *mut LeanObject,
    mut v_h_1204_: *mut LeanObject,
    mut v_defnCommRing_1205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1206_: *mut LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1203_,
        v_defnCommRing_1205_,
    );
    return v___x_1206_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim___redArg(
    mut v_t_1207_: *mut LeanObject,
    mut v_defnNatCommRing_1208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1209_: *mut LeanObject = core::ptr::null_mut();
    v___x_1209_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1207_,
        v_defnNatCommRing_1208_,
    );
    return v___x_1209_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_defnNatCommRing_elim(
    mut v_motive__2_1210_: *mut LeanObject,
    mut v_t_1211_: *mut LeanObject,
    mut v_h_1212_: *mut LeanObject,
    mut v_defnNatCommRing_1213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    v___x_1214_ = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(
        v_t_1211_,
        v_defnNatCommRing_1213_,
    );
    return v___x_1214_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim___redArg(
    mut v_t_1215_: *mut LeanObject,
    mut v_mul_1216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
    v___x_1217_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1215_, v_mul_1216_);
    return v___x_1217_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mul_elim(
    mut v_motive__2_1218_: *mut LeanObject,
    mut v_t_1219_: *mut LeanObject,
    mut v_h_1220_: *mut LeanObject,
    mut v_mul_1221_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1222_: *mut LeanObject = core::ptr::null_mut();
    v___x_1222_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1219_, v_mul_1221_);
    return v___x_1222_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim___redArg(
    mut v_t_1223_: *mut LeanObject,
    mut v_div_1224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1225_: *mut LeanObject = core::ptr::null_mut();
    v___x_1225_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1223_, v_div_1224_);
    return v___x_1225_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_div_elim(
    mut v_motive__2_1226_: *mut LeanObject,
    mut v_t_1227_: *mut LeanObject,
    mut v_h_1228_: *mut LeanObject,
    mut v_div_1229_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    v___x_1230_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1227_, v_div_1229_);
    return v___x_1230_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim___redArg(
    mut v_t_1231_: *mut LeanObject,
    mut v_mod_1232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    v___x_1233_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1231_, v_mod_1232_);
    return v___x_1233_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_mod_elim(
    mut v_motive__2_1234_: *mut LeanObject,
    mut v_t_1235_: *mut LeanObject,
    mut v_h_1236_: *mut LeanObject,
    mut v_mod_1237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    v___x_1238_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1235_, v_mod_1237_);
    return v___x_1238_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim___redArg(
    mut v_t_1239_: *mut LeanObject,
    mut v_pow_1240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1241_: *mut LeanObject = core::ptr::null_mut();
    v___x_1241_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1239_, v_pow_1240_);
    return v___x_1241_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_pow_elim(
    mut v_motive__2_1242_: *mut LeanObject,
    mut v_t_1243_: *mut LeanObject,
    mut v_h_1244_: *mut LeanObject,
    mut v_pow_1245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1246_: *mut LeanObject = core::ptr::null_mut();
    v___x_1246_ =
        l_Lean_Meta_Grind_Arith_Cutsat_EqCnstrProof_ctorElim___redArg(v_t_1243_, v_pow_1245_);
    return v___x_1246_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(
    mut v_x_1247_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1247_) == 0 {
        let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
        v___x_1248_ = lean_unsigned_to_nat(0);
        return v___x_1248_;
    } else {
        let mut v___x_1249_: *mut LeanObject = core::ptr::null_mut();
        v___x_1249_ = lean_unsigned_to_nat(1);
        return v___x_1249_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx___boxed(
    mut v_x_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorIdx(v_x_1250_);
    lean_dec_ref(v_x_1250_);
    return v_res_1251_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(
    mut v_t_1252_: *mut LeanObject,
    mut v_k_1253_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1252_) == 0 {
        let mut v_h_1254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
        v_h_1254_ = lean_ctor_get(v_t_1252_, 0);
        lean_inc(v_h_1254_);
        lean_dec_ref_known(v_t_1252_, 1);
        v___x_1255_ = lean_apply_1(v_k_1253_, v_h_1254_);
        return v___x_1255_;
    } else {
        let mut v_hs_1256_: *mut LeanObject = core::ptr::null_mut();
        let mut v_decVars_1257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
        v_hs_1256_ = lean_ctor_get(v_t_1252_, 0);
        lean_inc_ref(v_hs_1256_);
        v_decVars_1257_ = lean_ctor_get(v_t_1252_, 1);
        lean_inc_ref(v_decVars_1257_);
        lean_dec_ref_known(v_t_1252_, 2);
        v___x_1258_ = lean_apply_2(v_k_1253_, v_hs_1256_, v_decVars_1257_);
        return v___x_1258_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(
    mut v_motive__6_1259_: *mut LeanObject,
    mut v_ctorIdx_1260_: *mut LeanObject,
    mut v_t_1261_: *mut LeanObject,
    mut v_h_1262_: *mut LeanObject,
    mut v_k_1263_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1264_: *mut LeanObject = core::ptr::null_mut();
    v___x_1264_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1261_, v_k_1263_);
    return v___x_1264_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___boxed(
    mut v_motive__6_1265_: *mut LeanObject,
    mut v_ctorIdx_1266_: *mut LeanObject,
    mut v_t_1267_: *mut LeanObject,
    mut v_h_1268_: *mut LeanObject,
    mut v_k_1269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1270_: *mut LeanObject = core::ptr::null_mut();
    v_res_1270_ = l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim(
        v_motive__6_1265_,
        v_ctorIdx_1266_,
        v_t_1267_,
        v_h_1268_,
        v_k_1269_,
    );
    lean_dec(v_ctorIdx_1266_);
    return v_res_1270_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim___redArg(
    mut v_t_1271_: *mut LeanObject,
    mut v_dec_1272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
    v___x_1273_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1271_, v_dec_1272_);
    return v___x_1273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_dec_elim(
    mut v_motive__6_1274_: *mut LeanObject,
    mut v_t_1275_: *mut LeanObject,
    mut v_h_1276_: *mut LeanObject,
    mut v_dec_1277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1278_: *mut LeanObject = core::ptr::null_mut();
    v___x_1278_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1275_, v_dec_1277_);
    return v___x_1278_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim___redArg(
    mut v_t_1279_: *mut LeanObject,
    mut v_last_1280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1281_: *mut LeanObject = core::ptr::null_mut();
    v___x_1281_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1279_, v_last_1280_);
    return v___x_1281_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_last_elim(
    mut v_motive__6_1282_: *mut LeanObject,
    mut v_t_1283_: *mut LeanObject,
    mut v_h_1284_: *mut LeanObject,
    mut v_last_1285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    v___x_1286_ =
        l_Lean_Meta_Grind_Arith_Cutsat_CooperSplitProof_ctorElim___redArg(v_t_1283_, v_last_1285_);
    return v___x_1286_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(
    mut v_x_1287_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1287_) {
        0 => {
            let mut v___x_1288_: *mut LeanObject = core::ptr::null_mut();
            v___x_1288_ = lean_unsigned_to_nat(0);
            return v___x_1288_;
        }
        1 => {
            let mut v___x_1289_: *mut LeanObject = core::ptr::null_mut();
            v___x_1289_ = lean_unsigned_to_nat(1);
            return v___x_1289_;
        }
        2 => {
            let mut v___x_1290_: *mut LeanObject = core::ptr::null_mut();
            v___x_1290_ = lean_unsigned_to_nat(2);
            return v___x_1290_;
        }
        3 => {
            let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
            v___x_1291_ = lean_unsigned_to_nat(3);
            return v___x_1291_;
        }
        4 => {
            let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
            v___x_1292_ = lean_unsigned_to_nat(4);
            return v___x_1292_;
        }
        5 => {
            let mut v___x_1293_: *mut LeanObject = core::ptr::null_mut();
            v___x_1293_ = lean_unsigned_to_nat(5);
            return v___x_1293_;
        }
        6 => {
            let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
            v___x_1294_ = lean_unsigned_to_nat(6);
            return v___x_1294_;
        }
        7 => {
            let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
            v___x_1295_ = lean_unsigned_to_nat(7);
            return v___x_1295_;
        }
        8 => {
            let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
            v___x_1296_ = lean_unsigned_to_nat(8);
            return v___x_1296_;
        }
        9 => {
            let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
            v___x_1297_ = lean_unsigned_to_nat(9);
            return v___x_1297_;
        }
        10 => {
            let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
            v___x_1298_ = lean_unsigned_to_nat(10);
            return v___x_1298_;
        }
        11 => {
            let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
            v___x_1299_ = lean_unsigned_to_nat(11);
            return v___x_1299_;
        }
        _ => {
            let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
            v___x_1300_ = lean_unsigned_to_nat(12);
            return v___x_1300_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx___boxed(
    mut v_x_1301_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1302_: *mut LeanObject = core::ptr::null_mut();
    v_res_1302_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorIdx(v_x_1301_);
    lean_dec_ref(v_x_1301_);
    return v_res_1302_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
    mut v_t_1303_: *mut LeanObject,
    mut v_k_1304_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1303_) {
        1 => {
            let mut v_e_1305_: *mut LeanObject = core::ptr::null_mut();
            let mut v_thm_1306_: *mut LeanObject = core::ptr::null_mut();
            let mut v_d_1307_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1308_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
            v_e_1305_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc_ref(v_e_1305_);
            v_thm_1306_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_thm_1306_);
            v_d_1307_ = lean_ctor_get(v_t_1303_, 2);
            lean_inc(v_d_1307_);
            v_a_1308_ = lean_ctor_get(v_t_1303_, 3);
            lean_inc_ref(v_a_1308_);
            lean_dec_ref_known(v_t_1303_, 4);
            v___x_1309_ = lean_apply_4(v_k_1304_, v_e_1305_, v_thm_1306_, v_d_1307_, v_a_1308_);
            return v___x_1309_;
        }
        4 => {
            let mut v_c_u2081_1310_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1311_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1312_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1310_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc_ref(v_c_u2081_1310_);
            v_c_u2082_1311_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_c_u2082_1311_);
            lean_dec_ref_known(v_t_1303_, 2);
            v___x_1312_ = lean_apply_2(v_k_1304_, v_c_u2081_1310_, v_c_u2082_1311_);
            return v___x_1312_;
        }
        5 => {
            let mut v_c_u2081_1313_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1314_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1315_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1313_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc_ref(v_c_u2081_1313_);
            v_c_u2082_1314_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_c_u2082_1314_);
            lean_dec_ref_known(v_t_1303_, 2);
            v___x_1315_ = lean_apply_2(v_k_1304_, v_c_u2081_1313_, v_c_u2082_1314_);
            return v___x_1315_;
        }
        7 => {
            let mut v_x_1316_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_1317_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1318_: *mut LeanObject = core::ptr::null_mut();
            v_x_1316_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc(v_x_1316_);
            v_c_1317_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_c_1317_);
            lean_dec_ref_known(v_t_1303_, 2);
            v___x_1318_ = lean_apply_2(v_k_1304_, v_x_1316_, v_c_1317_);
            return v___x_1318_;
        }
        8 => {
            let mut v_x_1319_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1320_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1321_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1322_: *mut LeanObject = core::ptr::null_mut();
            v_x_1319_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc(v_x_1319_);
            v_c_u2081_1320_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_c_u2081_1320_);
            v_c_u2082_1321_ = lean_ctor_get(v_t_1303_, 2);
            lean_inc_ref(v_c_u2082_1321_);
            lean_dec_ref_known(v_t_1303_, 3);
            v___x_1322_ = lean_apply_3(v_k_1304_, v_x_1319_, v_c_u2081_1320_, v_c_u2082_1321_);
            return v___x_1322_;
        }
        12 => {
            let mut v_c_1323_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_1324_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1325_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1326_: *mut LeanObject = core::ptr::null_mut();
            v_c_1323_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc_ref(v_c_1323_);
            v_e_1324_ = lean_ctor_get(v_t_1303_, 1);
            lean_inc_ref(v_e_1324_);
            v_p_1325_ = lean_ctor_get(v_t_1303_, 2);
            lean_inc_ref(v_p_1325_);
            lean_dec_ref_known(v_t_1303_, 3);
            v___x_1326_ = lean_apply_3(v_k_1304_, v_c_1323_, v_e_1324_, v_p_1325_);
            return v___x_1326_;
        }
        _ => {
            let mut v_e_1327_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1328_: *mut LeanObject = core::ptr::null_mut();
            v_e_1327_ = lean_ctor_get(v_t_1303_, 0);
            lean_inc_ref(v_e_1327_);
            lean_dec_ref(v_t_1303_);
            v___x_1328_ = lean_apply_1(v_k_1304_, v_e_1327_);
            return v___x_1328_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(
    mut v_motive__7_1329_: *mut LeanObject,
    mut v_ctorIdx_1330_: *mut LeanObject,
    mut v_t_1331_: *mut LeanObject,
    mut v_h_1332_: *mut LeanObject,
    mut v_k_1333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1334_: *mut LeanObject = core::ptr::null_mut();
    v___x_1334_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1331_, v_k_1333_);
    return v___x_1334_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___boxed(
    mut v_motive__7_1335_: *mut LeanObject,
    mut v_ctorIdx_1336_: *mut LeanObject,
    mut v_t_1337_: *mut LeanObject,
    mut v_h_1338_: *mut LeanObject,
    mut v_k_1339_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1340_: *mut LeanObject = core::ptr::null_mut();
    v_res_1340_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim(
        v_motive__7_1335_,
        v_ctorIdx_1336_,
        v_t_1337_,
        v_h_1338_,
        v_k_1339_,
    );
    lean_dec(v_ctorIdx_1336_);
    return v_res_1340_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim___redArg(
    mut v_t_1341_: *mut LeanObject,
    mut v_core_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1343_: *mut LeanObject = core::ptr::null_mut();
    v___x_1343_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1341_, v_core_1342_);
    return v___x_1343_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_core_elim(
    mut v_motive__7_1344_: *mut LeanObject,
    mut v_t_1345_: *mut LeanObject,
    mut v_h_1346_: *mut LeanObject,
    mut v_core_1347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    v___x_1348_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1345_, v_core_1347_);
    return v___x_1348_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim___redArg(
    mut v_t_1349_: *mut LeanObject,
    mut v_coreOfNat_1350_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1351_: *mut LeanObject = core::ptr::null_mut();
    v___x_1351_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1349_,
        v_coreOfNat_1350_,
    );
    return v___x_1351_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_coreOfNat_elim(
    mut v_motive__7_1352_: *mut LeanObject,
    mut v_t_1353_: *mut LeanObject,
    mut v_h_1354_: *mut LeanObject,
    mut v_coreOfNat_1355_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    v___x_1356_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1353_,
        v_coreOfNat_1355_,
    );
    return v___x_1356_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim___redArg(
    mut v_t_1357_: *mut LeanObject,
    mut v_norm_1358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    v___x_1359_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1357_, v_norm_1358_);
    return v___x_1359_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_norm_elim(
    mut v_motive__7_1360_: *mut LeanObject,
    mut v_t_1361_: *mut LeanObject,
    mut v_h_1362_: *mut LeanObject,
    mut v_norm_1363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1364_: *mut LeanObject = core::ptr::null_mut();
    v___x_1364_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1361_, v_norm_1363_);
    return v___x_1364_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1365_: *mut LeanObject,
    mut v_divCoeffs_1366_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1367_: *mut LeanObject = core::ptr::null_mut();
    v___x_1367_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1365_,
        v_divCoeffs_1366_,
    );
    return v___x_1367_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_divCoeffs_elim(
    mut v_motive__7_1368_: *mut LeanObject,
    mut v_t_1369_: *mut LeanObject,
    mut v_h_1370_: *mut LeanObject,
    mut v_divCoeffs_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1369_,
        v_divCoeffs_1371_,
    );
    return v___x_1372_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim___redArg(
    mut v_t_1373_: *mut LeanObject,
    mut v_solveCombine_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1375_: *mut LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1373_,
        v_solveCombine_1374_,
    );
    return v___x_1375_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveCombine_elim(
    mut v_motive__7_1376_: *mut LeanObject,
    mut v_t_1377_: *mut LeanObject,
    mut v_h_1378_: *mut LeanObject,
    mut v_solveCombine_1379_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1380_: *mut LeanObject = core::ptr::null_mut();
    v___x_1380_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1377_,
        v_solveCombine_1379_,
    );
    return v___x_1380_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim___redArg(
    mut v_t_1381_: *mut LeanObject,
    mut v_solveElim_1382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
    v___x_1383_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1381_,
        v_solveElim_1382_,
    );
    return v___x_1383_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_solveElim_elim(
    mut v_motive__7_1384_: *mut LeanObject,
    mut v_t_1385_: *mut LeanObject,
    mut v_h_1386_: *mut LeanObject,
    mut v_solveElim_1387_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1388_: *mut LeanObject = core::ptr::null_mut();
    v___x_1388_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1385_,
        v_solveElim_1387_,
    );
    return v___x_1388_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim___redArg(
    mut v_t_1389_: *mut LeanObject,
    mut v_elim_1390_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1391_: *mut LeanObject = core::ptr::null_mut();
    v___x_1391_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1389_, v_elim_1390_);
    return v___x_1391_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_elim_elim(
    mut v_motive__7_1392_: *mut LeanObject,
    mut v_t_1393_: *mut LeanObject,
    mut v_h_1394_: *mut LeanObject,
    mut v_elim_1395_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
    v___x_1396_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1393_, v_elim_1395_);
    return v___x_1396_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim___redArg(
    mut v_t_1397_: *mut LeanObject,
    mut v_ofEq_1398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1399_: *mut LeanObject = core::ptr::null_mut();
    v___x_1399_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1397_, v_ofEq_1398_);
    return v___x_1399_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ofEq_elim(
    mut v_motive__7_1400_: *mut LeanObject,
    mut v_t_1401_: *mut LeanObject,
    mut v_h_1402_: *mut LeanObject,
    mut v_ofEq_1403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1404_: *mut LeanObject = core::ptr::null_mut();
    v___x_1404_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1401_, v_ofEq_1403_);
    return v___x_1404_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim___redArg(
    mut v_t_1405_: *mut LeanObject,
    mut v_subst_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1407_: *mut LeanObject = core::ptr::null_mut();
    v___x_1407_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1405_, v_subst_1406_);
    return v___x_1407_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_subst_elim(
    mut v_motive__7_1408_: *mut LeanObject,
    mut v_t_1409_: *mut LeanObject,
    mut v_h_1410_: *mut LeanObject,
    mut v_subst_1411_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1412_: *mut LeanObject = core::ptr::null_mut();
    v___x_1412_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1409_, v_subst_1411_);
    return v___x_1412_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim___redArg(
    mut v_t_1413_: *mut LeanObject,
    mut v_cooper_u2081_1414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1415_: *mut LeanObject = core::ptr::null_mut();
    v___x_1415_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1413_,
        v_cooper_u2081_1414_,
    );
    return v___x_1415_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2081_elim(
    mut v_motive__7_1416_: *mut LeanObject,
    mut v_t_1417_: *mut LeanObject,
    mut v_h_1418_: *mut LeanObject,
    mut v_cooper_u2081_1419_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    v___x_1420_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1417_,
        v_cooper_u2081_1419_,
    );
    return v___x_1420_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim___redArg(
    mut v_t_1421_: *mut LeanObject,
    mut v_cooper_u2082_1422_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    v___x_1423_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1421_,
        v_cooper_u2082_1422_,
    );
    return v___x_1423_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_cooper_u2082_elim(
    mut v_motive__7_1424_: *mut LeanObject,
    mut v_t_1425_: *mut LeanObject,
    mut v_h_1426_: *mut LeanObject,
    mut v_cooper_u2082_1427_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    v___x_1428_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1425_,
        v_cooper_u2082_1427_,
    );
    return v___x_1428_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim___redArg(
    mut v_t_1429_: *mut LeanObject,
    mut v_reorder_1430_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1431_: *mut LeanObject = core::ptr::null_mut();
    v___x_1431_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1429_, v_reorder_1430_);
    return v___x_1431_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_reorder_elim(
    mut v_motive__7_1432_: *mut LeanObject,
    mut v_t_1433_: *mut LeanObject,
    mut v_h_1434_: *mut LeanObject,
    mut v_reorder_1435_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1436_: *mut LeanObject = core::ptr::null_mut();
    v___x_1436_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(v_t_1433_, v_reorder_1435_);
    return v___x_1436_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1437_: *mut LeanObject,
    mut v_commRingNorm_1438_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1439_: *mut LeanObject = core::ptr::null_mut();
    v___x_1439_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1437_,
        v_commRingNorm_1438_,
    );
    return v___x_1439_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_commRingNorm_elim(
    mut v_motive__7_1440_: *mut LeanObject,
    mut v_t_1441_: *mut LeanObject,
    mut v_h_1442_: *mut LeanObject,
    mut v_commRingNorm_1443_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v___x_1444_ = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstrProof_ctorElim___redArg(
        v_t_1441_,
        v_commRingNorm_1443_,
    );
    return v___x_1444_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(
    mut v_x_1445_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1445_) {
        0 => {
            let mut v___x_1446_: *mut LeanObject = core::ptr::null_mut();
            v___x_1446_ = lean_unsigned_to_nat(0);
            return v___x_1446_;
        }
        1 => {
            let mut v___x_1447_: *mut LeanObject = core::ptr::null_mut();
            v___x_1447_ = lean_unsigned_to_nat(1);
            return v___x_1447_;
        }
        2 => {
            let mut v___x_1448_: *mut LeanObject = core::ptr::null_mut();
            v___x_1448_ = lean_unsigned_to_nat(2);
            return v___x_1448_;
        }
        3 => {
            let mut v___x_1449_: *mut LeanObject = core::ptr::null_mut();
            v___x_1449_ = lean_unsigned_to_nat(3);
            return v___x_1449_;
        }
        4 => {
            let mut v___x_1450_: *mut LeanObject = core::ptr::null_mut();
            v___x_1450_ = lean_unsigned_to_nat(4);
            return v___x_1450_;
        }
        5 => {
            let mut v___x_1451_: *mut LeanObject = core::ptr::null_mut();
            v___x_1451_ = lean_unsigned_to_nat(5);
            return v___x_1451_;
        }
        6 => {
            let mut v___x_1452_: *mut LeanObject = core::ptr::null_mut();
            v___x_1452_ = lean_unsigned_to_nat(6);
            return v___x_1452_;
        }
        7 => {
            let mut v___x_1453_: *mut LeanObject = core::ptr::null_mut();
            v___x_1453_ = lean_unsigned_to_nat(7);
            return v___x_1453_;
        }
        8 => {
            let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
            v___x_1454_ = lean_unsigned_to_nat(8);
            return v___x_1454_;
        }
        9 => {
            let mut v___x_1455_: *mut LeanObject = core::ptr::null_mut();
            v___x_1455_ = lean_unsigned_to_nat(9);
            return v___x_1455_;
        }
        10 => {
            let mut v___x_1456_: *mut LeanObject = core::ptr::null_mut();
            v___x_1456_ = lean_unsigned_to_nat(10);
            return v___x_1456_;
        }
        11 => {
            let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
            v___x_1457_ = lean_unsigned_to_nat(11);
            return v___x_1457_;
        }
        12 => {
            let mut v___x_1458_: *mut LeanObject = core::ptr::null_mut();
            v___x_1458_ = lean_unsigned_to_nat(12);
            return v___x_1458_;
        }
        13 => {
            let mut v___x_1459_: *mut LeanObject = core::ptr::null_mut();
            v___x_1459_ = lean_unsigned_to_nat(13);
            return v___x_1459_;
        }
        14 => {
            let mut v___x_1460_: *mut LeanObject = core::ptr::null_mut();
            v___x_1460_ = lean_unsigned_to_nat(14);
            return v___x_1460_;
        }
        15 => {
            let mut v___x_1461_: *mut LeanObject = core::ptr::null_mut();
            v___x_1461_ = lean_unsigned_to_nat(15);
            return v___x_1461_;
        }
        16 => {
            let mut v___x_1462_: *mut LeanObject = core::ptr::null_mut();
            v___x_1462_ = lean_unsigned_to_nat(16);
            return v___x_1462_;
        }
        _ => {
            let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
            v___x_1463_ = lean_unsigned_to_nat(17);
            return v___x_1463_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx___boxed(
    mut v_x_1464_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1465_: *mut LeanObject = core::ptr::null_mut();
    v_res_1465_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorIdx(v_x_1464_);
    lean_dec_ref(v_x_1464_);
    return v_res_1465_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
    mut v_t_1466_: *mut LeanObject,
    mut v_k_1467_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1466_) {
        1 => {
            let mut v_e_1468_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1469_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1470_: *mut LeanObject = core::ptr::null_mut();
            v_e_1468_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_e_1468_);
            v_p_1469_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_p_1469_);
            lean_dec_ref_known(v_t_1466_, 2);
            v___x_1470_ = lean_apply_2(v_k_1467_, v_e_1468_, v_p_1469_);
            return v___x_1470_;
        }
        2 => {
            let mut v_e_1471_: *mut LeanObject = core::ptr::null_mut();
            let mut v_pos_1472_: u8 = 0;
            let mut v_toIntThm_1473_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_1474_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_1475_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1476_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1477_: *mut LeanObject = core::ptr::null_mut();
            v_e_1471_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_e_1471_);
            v_pos_1472_ = lean_ctor_get_uint8(
                v_t_1466_,
                (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
            );
            v_toIntThm_1473_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_toIntThm_1473_);
            v_lhs_1474_ = lean_ctor_get(v_t_1466_, 2);
            lean_inc_ref(v_lhs_1474_);
            v_rhs_1475_ = lean_ctor_get(v_t_1466_, 3);
            lean_inc_ref(v_rhs_1475_);
            lean_dec_ref_known(v_t_1466_, 4);
            v___x_1476_ = lean_box((v_pos_1472_) as usize);
            v___x_1477_ = lean_apply_5(
                v_k_1467_,
                v_e_1471_,
                v___x_1476_,
                v_toIntThm_1473_,
                v_lhs_1474_,
                v_rhs_1475_,
            );
            return v___x_1477_;
        }
        5 => {
            let mut v_h_1478_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1479_: *mut LeanObject = core::ptr::null_mut();
            v_h_1478_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc(v_h_1478_);
            lean_dec_ref_known(v_t_1466_, 1);
            v___x_1479_ = lean_apply_1(v_k_1467_, v_h_1478_);
            return v___x_1479_;
        }
        8 => {
            let mut v_c_u2081_1480_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1481_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1480_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1480_);
            v_c_u2082_1481_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2082_1481_);
            lean_dec_ref_known(v_t_1466_, 2);
            v___x_1482_ = lean_apply_2(v_k_1467_, v_c_u2081_1480_, v_c_u2082_1481_);
            return v___x_1482_;
        }
        9 => {
            let mut v_c_u2081_1483_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1484_: *mut LeanObject = core::ptr::null_mut();
            let mut v_k_1485_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1483_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1483_);
            v_c_u2082_1484_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2082_1484_);
            v_k_1485_ = lean_ctor_get(v_t_1466_, 2);
            lean_inc(v_k_1485_);
            lean_dec_ref_known(v_t_1466_, 3);
            v___x_1486_ = lean_apply_3(v_k_1467_, v_c_u2081_1483_, v_c_u2082_1484_, v_k_1485_);
            return v___x_1486_;
        }
        10 => {
            let mut v_x_1487_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1488_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1489_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1490_: *mut LeanObject = core::ptr::null_mut();
            v_x_1487_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc(v_x_1487_);
            v_c_u2081_1488_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2081_1488_);
            v_c_u2082_1489_ = lean_ctor_get(v_t_1466_, 2);
            lean_inc_ref(v_c_u2082_1489_);
            lean_dec_ref_known(v_t_1466_, 3);
            v___x_1490_ = lean_apply_3(v_k_1467_, v_x_1487_, v_c_u2081_1488_, v_c_u2082_1489_);
            return v___x_1490_;
        }
        11 => {
            let mut v_c_u2081_1491_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1492_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1493_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1491_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1491_);
            v_c_u2082_1492_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2082_1492_);
            lean_dec_ref_known(v_t_1466_, 2);
            v___x_1493_ = lean_apply_2(v_k_1467_, v_c_u2081_1491_, v_c_u2082_1492_);
            return v___x_1493_;
        }
        12 => {
            let mut v_c_u2081_1494_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decVar_1495_: *mut LeanObject = core::ptr::null_mut();
            let mut v_h_1496_: *mut LeanObject = core::ptr::null_mut();
            let mut v_decVars_1497_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1498_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1494_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1494_);
            v_decVar_1495_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc(v_decVar_1495_);
            v_h_1496_ = lean_ctor_get(v_t_1466_, 2);
            lean_inc_ref(v_h_1496_);
            v_decVars_1497_ = lean_ctor_get(v_t_1466_, 3);
            lean_inc_ref(v_decVars_1497_);
            lean_dec_ref_known(v_t_1466_, 4);
            v___x_1498_ = lean_apply_4(
                v_k_1467_,
                v_c_u2081_1494_,
                v_decVar_1495_,
                v_h_1496_,
                v_decVars_1497_,
            );
            return v___x_1498_;
        }
        14 => {
            let mut v_c_u2081_1499_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1500_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1501_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1499_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1499_);
            v_c_u2082_1500_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2082_1500_);
            lean_dec_ref_known(v_t_1466_, 2);
            v___x_1501_ = lean_apply_2(v_k_1467_, v_c_u2081_1499_, v_c_u2082_1500_);
            return v___x_1501_;
        }
        15 => {
            let mut v_c_u2081_1502_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1503_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1504_: *mut LeanObject = core::ptr::null_mut();
            v_c_u2081_1502_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_u2081_1502_);
            v_c_u2082_1503_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_c_u2082_1503_);
            lean_dec_ref_known(v_t_1466_, 2);
            v___x_1504_ = lean_apply_2(v_k_1467_, v_c_u2081_1502_, v_c_u2082_1503_);
            return v___x_1504_;
        }
        17 => {
            let mut v_c_1505_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_1506_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1507_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
            v_c_1505_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_c_1505_);
            v_e_1506_ = lean_ctor_get(v_t_1466_, 1);
            lean_inc_ref(v_e_1506_);
            v_p_1507_ = lean_ctor_get(v_t_1466_, 2);
            lean_inc_ref(v_p_1507_);
            lean_dec_ref_known(v_t_1466_, 3);
            v___x_1508_ = lean_apply_3(v_k_1467_, v_c_1505_, v_e_1506_, v_p_1507_);
            return v___x_1508_;
        }
        _ => {
            let mut v_e_1509_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1510_: *mut LeanObject = core::ptr::null_mut();
            v_e_1509_ = lean_ctor_get(v_t_1466_, 0);
            lean_inc_ref(v_e_1509_);
            lean_dec_ref(v_t_1466_);
            v___x_1510_ = lean_apply_1(v_k_1467_, v_e_1509_);
            return v___x_1510_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(
    mut v_motive__9_1511_: *mut LeanObject,
    mut v_ctorIdx_1512_: *mut LeanObject,
    mut v_t_1513_: *mut LeanObject,
    mut v_h_1514_: *mut LeanObject,
    mut v_k_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1516_: *mut LeanObject = core::ptr::null_mut();
    v___x_1516_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1513_, v_k_1515_);
    return v___x_1516_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___boxed(
    mut v_motive__9_1517_: *mut LeanObject,
    mut v_ctorIdx_1518_: *mut LeanObject,
    mut v_t_1519_: *mut LeanObject,
    mut v_h_1520_: *mut LeanObject,
    mut v_k_1521_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1522_: *mut LeanObject = core::ptr::null_mut();
    v_res_1522_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim(
        v_motive__9_1517_,
        v_ctorIdx_1518_,
        v_t_1519_,
        v_h_1520_,
        v_k_1521_,
    );
    lean_dec(v_ctorIdx_1518_);
    return v_res_1522_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim___redArg(
    mut v_t_1523_: *mut LeanObject,
    mut v_core_1524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1525_: *mut LeanObject = core::ptr::null_mut();
    v___x_1525_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1523_, v_core_1524_);
    return v___x_1525_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_core_elim(
    mut v_motive__9_1526_: *mut LeanObject,
    mut v_t_1527_: *mut LeanObject,
    mut v_h_1528_: *mut LeanObject,
    mut v_core_1529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
    v___x_1530_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1527_, v_core_1529_);
    return v___x_1530_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim___redArg(
    mut v_t_1531_: *mut LeanObject,
    mut v_coreNeg_1532_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
    v___x_1533_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1531_, v_coreNeg_1532_);
    return v___x_1533_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreNeg_elim(
    mut v_motive__9_1534_: *mut LeanObject,
    mut v_t_1535_: *mut LeanObject,
    mut v_h_1536_: *mut LeanObject,
    mut v_coreNeg_1537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1538_: *mut LeanObject = core::ptr::null_mut();
    v___x_1538_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1535_, v_coreNeg_1537_);
    return v___x_1538_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim___redArg(
    mut v_t_1539_: *mut LeanObject,
    mut v_coreToInt_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1541_: *mut LeanObject = core::ptr::null_mut();
    v___x_1541_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1539_, v_coreToInt_1540_);
    return v___x_1541_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_coreToInt_elim(
    mut v_motive__9_1542_: *mut LeanObject,
    mut v_t_1543_: *mut LeanObject,
    mut v_h_1544_: *mut LeanObject,
    mut v_coreToInt_1545_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    v___x_1546_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1543_, v_coreToInt_1545_);
    return v___x_1546_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim___redArg(
    mut v_t_1547_: *mut LeanObject,
    mut v_ofNatNonneg_1548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1549_: *mut LeanObject = core::ptr::null_mut();
    v___x_1549_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1547_,
        v_ofNatNonneg_1548_,
    );
    return v___x_1549_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofNatNonneg_elim(
    mut v_motive__9_1550_: *mut LeanObject,
    mut v_t_1551_: *mut LeanObject,
    mut v_h_1552_: *mut LeanObject,
    mut v_ofNatNonneg_1553_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    v___x_1554_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1551_,
        v_ofNatNonneg_1553_,
    );
    return v___x_1554_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim___redArg(
    mut v_t_1555_: *mut LeanObject,
    mut v_bound_1556_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1557_: *mut LeanObject = core::ptr::null_mut();
    v___x_1557_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1555_, v_bound_1556_);
    return v___x_1557_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_bound_elim(
    mut v_motive__9_1558_: *mut LeanObject,
    mut v_t_1559_: *mut LeanObject,
    mut v_h_1560_: *mut LeanObject,
    mut v_bound_1561_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1562_: *mut LeanObject = core::ptr::null_mut();
    v___x_1562_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1559_, v_bound_1561_);
    return v___x_1562_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim___redArg(
    mut v_t_1563_: *mut LeanObject,
    mut v_dec_1564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
    v___x_1565_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1563_, v_dec_1564_);
    return v___x_1565_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dec_elim(
    mut v_motive__9_1566_: *mut LeanObject,
    mut v_t_1567_: *mut LeanObject,
    mut v_h_1568_: *mut LeanObject,
    mut v_dec_1569_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
    v___x_1570_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1567_, v_dec_1569_);
    return v___x_1570_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim___redArg(
    mut v_t_1571_: *mut LeanObject,
    mut v_norm_1572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1573_: *mut LeanObject = core::ptr::null_mut();
    v___x_1573_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1571_, v_norm_1572_);
    return v___x_1573_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_norm_elim(
    mut v_motive__9_1574_: *mut LeanObject,
    mut v_t_1575_: *mut LeanObject,
    mut v_h_1576_: *mut LeanObject,
    mut v_norm_1577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1578_: *mut LeanObject = core::ptr::null_mut();
    v___x_1578_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1575_, v_norm_1577_);
    return v___x_1578_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1579_: *mut LeanObject,
    mut v_divCoeffs_1580_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1581_: *mut LeanObject = core::ptr::null_mut();
    v___x_1581_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1579_, v_divCoeffs_1580_);
    return v___x_1581_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_divCoeffs_elim(
    mut v_motive__9_1582_: *mut LeanObject,
    mut v_t_1583_: *mut LeanObject,
    mut v_h_1584_: *mut LeanObject,
    mut v_divCoeffs_1585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1586_: *mut LeanObject = core::ptr::null_mut();
    v___x_1586_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1583_, v_divCoeffs_1585_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim___redArg(
    mut v_t_1587_: *mut LeanObject,
    mut v_combine_1588_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1589_: *mut LeanObject = core::ptr::null_mut();
    v___x_1589_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1587_, v_combine_1588_);
    return v___x_1589_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combine_elim(
    mut v_motive__9_1590_: *mut LeanObject,
    mut v_t_1591_: *mut LeanObject,
    mut v_h_1592_: *mut LeanObject,
    mut v_combine_1593_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1594_: *mut LeanObject = core::ptr::null_mut();
    v___x_1594_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1591_, v_combine_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim___redArg(
    mut v_t_1595_: *mut LeanObject,
    mut v_combineDivCoeffs_1596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1597_: *mut LeanObject = core::ptr::null_mut();
    v___x_1597_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1595_,
        v_combineDivCoeffs_1596_,
    );
    return v___x_1597_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_combineDivCoeffs_elim(
    mut v_motive__9_1598_: *mut LeanObject,
    mut v_t_1599_: *mut LeanObject,
    mut v_h_1600_: *mut LeanObject,
    mut v_combineDivCoeffs_1601_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1602_: *mut LeanObject = core::ptr::null_mut();
    v___x_1602_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1599_,
        v_combineDivCoeffs_1601_,
    );
    return v___x_1602_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim___redArg(
    mut v_t_1603_: *mut LeanObject,
    mut v_subst_1604_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1605_: *mut LeanObject = core::ptr::null_mut();
    v___x_1605_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1603_, v_subst_1604_);
    return v___x_1605_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_subst_elim(
    mut v_motive__9_1606_: *mut LeanObject,
    mut v_t_1607_: *mut LeanObject,
    mut v_h_1608_: *mut LeanObject,
    mut v_subst_1609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1607_, v_subst_1609_);
    return v___x_1610_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim___redArg(
    mut v_t_1611_: *mut LeanObject,
    mut v_ofLeDiseq_1612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1613_: *mut LeanObject = core::ptr::null_mut();
    v___x_1613_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1611_, v_ofLeDiseq_1612_);
    return v___x_1613_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofLeDiseq_elim(
    mut v_motive__9_1614_: *mut LeanObject,
    mut v_t_1615_: *mut LeanObject,
    mut v_h_1616_: *mut LeanObject,
    mut v_ofLeDiseq_1617_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1618_: *mut LeanObject = core::ptr::null_mut();
    v___x_1618_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1615_, v_ofLeDiseq_1617_);
    return v___x_1618_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim___redArg(
    mut v_t_1619_: *mut LeanObject,
    mut v_ofDiseqSplit_1620_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1621_: *mut LeanObject = core::ptr::null_mut();
    v___x_1621_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1619_,
        v_ofDiseqSplit_1620_,
    );
    return v___x_1621_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ofDiseqSplit_elim(
    mut v_motive__9_1622_: *mut LeanObject,
    mut v_t_1623_: *mut LeanObject,
    mut v_h_1624_: *mut LeanObject,
    mut v_ofDiseqSplit_1625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1623_,
        v_ofDiseqSplit_1625_,
    );
    return v___x_1626_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim___redArg(
    mut v_t_1627_: *mut LeanObject,
    mut v_cooper_1628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1629_: *mut LeanObject = core::ptr::null_mut();
    v___x_1629_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1627_, v_cooper_1628_);
    return v___x_1629_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_cooper_elim(
    mut v_motive__9_1630_: *mut LeanObject,
    mut v_t_1631_: *mut LeanObject,
    mut v_h_1632_: *mut LeanObject,
    mut v_cooper_1633_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1634_: *mut LeanObject = core::ptr::null_mut();
    v___x_1634_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1631_, v_cooper_1633_);
    return v___x_1634_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim___redArg(
    mut v_t_1635_: *mut LeanObject,
    mut v_dvdTight_1636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    v___x_1637_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1635_, v_dvdTight_1636_);
    return v___x_1637_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_dvdTight_elim(
    mut v_motive__9_1638_: *mut LeanObject,
    mut v_t_1639_: *mut LeanObject,
    mut v_h_1640_: *mut LeanObject,
    mut v_dvdTight_1641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    v___x_1642_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1639_, v_dvdTight_1641_);
    return v___x_1642_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim___redArg(
    mut v_t_1643_: *mut LeanObject,
    mut v_negDvdTight_1644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1645_: *mut LeanObject = core::ptr::null_mut();
    v___x_1645_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1643_,
        v_negDvdTight_1644_,
    );
    return v___x_1645_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_negDvdTight_elim(
    mut v_motive__9_1646_: *mut LeanObject,
    mut v_t_1647_: *mut LeanObject,
    mut v_h_1648_: *mut LeanObject,
    mut v_negDvdTight_1649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1650_: *mut LeanObject = core::ptr::null_mut();
    v___x_1650_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1647_,
        v_negDvdTight_1649_,
    );
    return v___x_1650_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim___redArg(
    mut v_t_1651_: *mut LeanObject,
    mut v_reorder_1652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1653_: *mut LeanObject = core::ptr::null_mut();
    v___x_1653_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1651_, v_reorder_1652_);
    return v___x_1653_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_reorder_elim(
    mut v_motive__9_1654_: *mut LeanObject,
    mut v_t_1655_: *mut LeanObject,
    mut v_h_1656_: *mut LeanObject,
    mut v_reorder_1657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
    v___x_1658_ =
        l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(v_t_1655_, v_reorder_1657_);
    return v___x_1658_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1659_: *mut LeanObject,
    mut v_commRingNorm_1660_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
    v___x_1661_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1659_,
        v_commRingNorm_1660_,
    );
    return v___x_1661_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_commRingNorm_elim(
    mut v_motive__9_1662_: *mut LeanObject,
    mut v_t_1663_: *mut LeanObject,
    mut v_h_1664_: *mut LeanObject,
    mut v_commRingNorm_1665_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1666_: *mut LeanObject = core::ptr::null_mut();
    v___x_1666_ = l_Lean_Meta_Grind_Arith_Cutsat_LeCnstrProof_ctorElim___redArg(
        v_t_1663_,
        v_commRingNorm_1665_,
    );
    return v___x_1666_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(
    mut v_x_1667_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1667_) {
        0 => {
            let mut v___x_1668_: *mut LeanObject = core::ptr::null_mut();
            v___x_1668_ = lean_unsigned_to_nat(0);
            return v___x_1668_;
        }
        1 => {
            let mut v___x_1669_: *mut LeanObject = core::ptr::null_mut();
            v___x_1669_ = lean_unsigned_to_nat(1);
            return v___x_1669_;
        }
        2 => {
            let mut v___x_1670_: *mut LeanObject = core::ptr::null_mut();
            v___x_1670_ = lean_unsigned_to_nat(2);
            return v___x_1670_;
        }
        3 => {
            let mut v___x_1671_: *mut LeanObject = core::ptr::null_mut();
            v___x_1671_ = lean_unsigned_to_nat(3);
            return v___x_1671_;
        }
        4 => {
            let mut v___x_1672_: *mut LeanObject = core::ptr::null_mut();
            v___x_1672_ = lean_unsigned_to_nat(4);
            return v___x_1672_;
        }
        5 => {
            let mut v___x_1673_: *mut LeanObject = core::ptr::null_mut();
            v___x_1673_ = lean_unsigned_to_nat(5);
            return v___x_1673_;
        }
        6 => {
            let mut v___x_1674_: *mut LeanObject = core::ptr::null_mut();
            v___x_1674_ = lean_unsigned_to_nat(6);
            return v___x_1674_;
        }
        7 => {
            let mut v___x_1675_: *mut LeanObject = core::ptr::null_mut();
            v___x_1675_ = lean_unsigned_to_nat(7);
            return v___x_1675_;
        }
        _ => {
            let mut v___x_1676_: *mut LeanObject = core::ptr::null_mut();
            v___x_1676_ = lean_unsigned_to_nat(8);
            return v___x_1676_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx___boxed(
    mut v_x_1677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1678_: *mut LeanObject = core::ptr::null_mut();
    v_res_1678_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorIdx(v_x_1677_);
    lean_dec_ref(v_x_1677_);
    return v_res_1678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
    mut v_t_1679_: *mut LeanObject,
    mut v_k_1680_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_1679_) {
        0 => {
            let mut v_a_1681_: *mut LeanObject = core::ptr::null_mut();
            let mut v_zero_1682_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
            v_a_1681_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc_ref(v_a_1681_);
            v_zero_1682_ = lean_ctor_get(v_t_1679_, 1);
            lean_inc_ref(v_zero_1682_);
            lean_dec_ref_known(v_t_1679_, 2);
            v___x_1683_ = lean_apply_2(v_k_1680_, v_a_1681_, v_zero_1682_);
            return v___x_1683_;
        }
        1 => {
            let mut v_a_1684_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1685_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2081_1686_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_u2082_1687_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1688_: *mut LeanObject = core::ptr::null_mut();
            v_a_1684_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc_ref(v_a_1684_);
            v_b_1685_ = lean_ctor_get(v_t_1679_, 1);
            lean_inc_ref(v_b_1685_);
            v_p_u2081_1686_ = lean_ctor_get(v_t_1679_, 2);
            lean_inc_ref(v_p_u2081_1686_);
            v_p_u2082_1687_ = lean_ctor_get(v_t_1679_, 3);
            lean_inc_ref(v_p_u2082_1687_);
            lean_dec_ref_known(v_t_1679_, 4);
            v___x_1688_ = lean_apply_4(
                v_k_1680_,
                v_a_1684_,
                v_b_1685_,
                v_p_u2081_1686_,
                v_p_u2082_1687_,
            );
            return v___x_1688_;
        }
        2 => {
            let mut v_a_1689_: *mut LeanObject = core::ptr::null_mut();
            let mut v_b_1690_: *mut LeanObject = core::ptr::null_mut();
            let mut v_toIntThm_1691_: *mut LeanObject = core::ptr::null_mut();
            let mut v_lhs_1692_: *mut LeanObject = core::ptr::null_mut();
            let mut v_rhs_1693_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1694_: *mut LeanObject = core::ptr::null_mut();
            v_a_1689_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc_ref(v_a_1689_);
            v_b_1690_ = lean_ctor_get(v_t_1679_, 1);
            lean_inc_ref(v_b_1690_);
            v_toIntThm_1691_ = lean_ctor_get(v_t_1679_, 2);
            lean_inc_ref(v_toIntThm_1691_);
            v_lhs_1692_ = lean_ctor_get(v_t_1679_, 3);
            lean_inc_ref(v_lhs_1692_);
            v_rhs_1693_ = lean_ctor_get(v_t_1679_, 4);
            lean_inc_ref(v_rhs_1693_);
            lean_dec_ref_known(v_t_1679_, 5);
            v___x_1694_ = lean_apply_5(
                v_k_1680_,
                v_a_1689_,
                v_b_1690_,
                v_toIntThm_1691_,
                v_lhs_1692_,
                v_rhs_1693_,
            );
            return v___x_1694_;
        }
        6 => {
            let mut v_x_1695_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2081_1696_: *mut LeanObject = core::ptr::null_mut();
            let mut v_c_u2082_1697_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1698_: *mut LeanObject = core::ptr::null_mut();
            v_x_1695_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc(v_x_1695_);
            v_c_u2081_1696_ = lean_ctor_get(v_t_1679_, 1);
            lean_inc_ref(v_c_u2081_1696_);
            v_c_u2082_1697_ = lean_ctor_get(v_t_1679_, 2);
            lean_inc_ref(v_c_u2082_1697_);
            lean_dec_ref_known(v_t_1679_, 3);
            v___x_1698_ = lean_apply_3(v_k_1680_, v_x_1695_, v_c_u2081_1696_, v_c_u2082_1697_);
            return v___x_1698_;
        }
        8 => {
            let mut v_c_1699_: *mut LeanObject = core::ptr::null_mut();
            let mut v_e_1700_: *mut LeanObject = core::ptr::null_mut();
            let mut v_p_1701_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
            v_c_1699_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc_ref(v_c_1699_);
            v_e_1700_ = lean_ctor_get(v_t_1679_, 1);
            lean_inc_ref(v_e_1700_);
            v_p_1701_ = lean_ctor_get(v_t_1679_, 2);
            lean_inc_ref(v_p_1701_);
            lean_dec_ref_known(v_t_1679_, 3);
            v___x_1702_ = lean_apply_3(v_k_1680_, v_c_1699_, v_e_1700_, v_p_1701_);
            return v___x_1702_;
        }
        _ => {
            let mut v_c_1703_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
            v_c_1703_ = lean_ctor_get(v_t_1679_, 0);
            lean_inc_ref(v_c_1703_);
            lean_dec_ref(v_t_1679_);
            v___x_1704_ = lean_apply_1(v_k_1680_, v_c_1703_);
            return v___x_1704_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(
    mut v_motive__11_1705_: *mut LeanObject,
    mut v_ctorIdx_1706_: *mut LeanObject,
    mut v_t_1707_: *mut LeanObject,
    mut v_h_1708_: *mut LeanObject,
    mut v_k_1709_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1710_: *mut LeanObject = core::ptr::null_mut();
    v___x_1710_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1707_, v_k_1709_);
    return v___x_1710_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___boxed(
    mut v_motive__11_1711_: *mut LeanObject,
    mut v_ctorIdx_1712_: *mut LeanObject,
    mut v_t_1713_: *mut LeanObject,
    mut v_h_1714_: *mut LeanObject,
    mut v_k_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1716_: *mut LeanObject = core::ptr::null_mut();
    v_res_1716_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim(
        v_motive__11_1711_,
        v_ctorIdx_1712_,
        v_t_1713_,
        v_h_1714_,
        v_k_1715_,
    );
    lean_dec(v_ctorIdx_1712_);
    return v_res_1716_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim___redArg(
    mut v_t_1717_: *mut LeanObject,
    mut v_core0_1718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1719_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1717_, v_core0_1718_);
    return v___x_1719_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core0_elim(
    mut v_motive__11_1720_: *mut LeanObject,
    mut v_t_1721_: *mut LeanObject,
    mut v_h_1722_: *mut LeanObject,
    mut v_core0_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1721_, v_core0_1723_);
    return v___x_1724_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim___redArg(
    mut v_t_1725_: *mut LeanObject,
    mut v_core_1726_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v___x_1727_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1725_, v_core_1726_);
    return v___x_1727_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_core_elim(
    mut v_motive__11_1728_: *mut LeanObject,
    mut v_t_1729_: *mut LeanObject,
    mut v_h_1730_: *mut LeanObject,
    mut v_core_1731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1732_: *mut LeanObject = core::ptr::null_mut();
    v___x_1732_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1729_, v_core_1731_);
    return v___x_1732_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim___redArg(
    mut v_t_1733_: *mut LeanObject,
    mut v_coreToInt_1734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    v___x_1735_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1733_,
        v_coreToInt_1734_,
    );
    return v___x_1735_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_coreToInt_elim(
    mut v_motive__11_1736_: *mut LeanObject,
    mut v_t_1737_: *mut LeanObject,
    mut v_h_1738_: *mut LeanObject,
    mut v_coreToInt_1739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    v___x_1740_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1737_,
        v_coreToInt_1739_,
    );
    return v___x_1740_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim___redArg(
    mut v_t_1741_: *mut LeanObject,
    mut v_norm_1742_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1743_: *mut LeanObject = core::ptr::null_mut();
    v___x_1743_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1741_, v_norm_1742_);
    return v___x_1743_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_norm_elim(
    mut v_motive__11_1744_: *mut LeanObject,
    mut v_t_1745_: *mut LeanObject,
    mut v_h_1746_: *mut LeanObject,
    mut v_norm_1747_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1748_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1745_, v_norm_1747_);
    return v___x_1748_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim___redArg(
    mut v_t_1749_: *mut LeanObject,
    mut v_divCoeffs_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    v___x_1751_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1749_,
        v_divCoeffs_1750_,
    );
    return v___x_1751_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_divCoeffs_elim(
    mut v_motive__11_1752_: *mut LeanObject,
    mut v_t_1753_: *mut LeanObject,
    mut v_h_1754_: *mut LeanObject,
    mut v_divCoeffs_1755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1756_: *mut LeanObject = core::ptr::null_mut();
    v___x_1756_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1753_,
        v_divCoeffs_1755_,
    );
    return v___x_1756_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim___redArg(
    mut v_t_1757_: *mut LeanObject,
    mut v_neg_1758_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1759_: *mut LeanObject = core::ptr::null_mut();
    v___x_1759_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1757_, v_neg_1758_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_neg_elim(
    mut v_motive__11_1760_: *mut LeanObject,
    mut v_t_1761_: *mut LeanObject,
    mut v_h_1762_: *mut LeanObject,
    mut v_neg_1763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1764_: *mut LeanObject = core::ptr::null_mut();
    v___x_1764_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1761_, v_neg_1763_);
    return v___x_1764_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim___redArg(
    mut v_t_1765_: *mut LeanObject,
    mut v_subst_1766_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    v___x_1767_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1765_, v_subst_1766_);
    return v___x_1767_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_subst_elim(
    mut v_motive__11_1768_: *mut LeanObject,
    mut v_t_1769_: *mut LeanObject,
    mut v_h_1770_: *mut LeanObject,
    mut v_subst_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1772_: *mut LeanObject = core::ptr::null_mut();
    v___x_1772_ =
        l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(v_t_1769_, v_subst_1771_);
    return v___x_1772_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim___redArg(
    mut v_t_1773_: *mut LeanObject,
    mut v_reorder_1774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    v___x_1775_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1773_,
        v_reorder_1774_,
    );
    return v___x_1775_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_reorder_elim(
    mut v_motive__11_1776_: *mut LeanObject,
    mut v_t_1777_: *mut LeanObject,
    mut v_h_1778_: *mut LeanObject,
    mut v_reorder_1779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1780_: *mut LeanObject = core::ptr::null_mut();
    v___x_1780_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1777_,
        v_reorder_1779_,
    );
    return v___x_1780_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim___redArg(
    mut v_t_1781_: *mut LeanObject,
    mut v_commRingNorm_1782_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
    v___x_1783_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1781_,
        v_commRingNorm_1782_,
    );
    return v___x_1783_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_commRingNorm_elim(
    mut v_motive__11_1784_: *mut LeanObject,
    mut v_t_1785_: *mut LeanObject,
    mut v_h_1786_: *mut LeanObject,
    mut v_commRingNorm_1787_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
    v___x_1788_ = l_Lean_Meta_Grind_Arith_Cutsat_DiseqCnstrProof_ctorElim___redArg(
        v_t_1785_,
        v_commRingNorm_1787_,
    );
    return v___x_1788_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(
    mut v_x_1789_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1789_) {
        0 => {
            let mut v___x_1790_: *mut LeanObject = core::ptr::null_mut();
            v___x_1790_ = lean_unsigned_to_nat(0);
            return v___x_1790_;
        }
        1 => {
            let mut v___x_1791_: *mut LeanObject = core::ptr::null_mut();
            v___x_1791_ = lean_unsigned_to_nat(1);
            return v___x_1791_;
        }
        2 => {
            let mut v___x_1792_: *mut LeanObject = core::ptr::null_mut();
            v___x_1792_ = lean_unsigned_to_nat(2);
            return v___x_1792_;
        }
        3 => {
            let mut v___x_1793_: *mut LeanObject = core::ptr::null_mut();
            v___x_1793_ = lean_unsigned_to_nat(3);
            return v___x_1793_;
        }
        _ => {
            let mut v___x_1794_: *mut LeanObject = core::ptr::null_mut();
            v___x_1794_ = lean_unsigned_to_nat(4);
            return v___x_1794_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx___boxed(
    mut v_x_1795_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1796_: *mut LeanObject = core::ptr::null_mut();
    v_res_1796_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorIdx(v_x_1795_);
    lean_dec_ref(v_x_1795_);
    return v_res_1796_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(
    mut v_t_1797_: *mut LeanObject,
    mut v_k_1798_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_t_1797_) == 4 {
        let mut v_c_u2081_1799_: *mut LeanObject = core::ptr::null_mut();
        let mut v_c_u2082_1800_: *mut LeanObject = core::ptr::null_mut();
        let mut v_c_u2083_1801_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
        v_c_u2081_1799_ = lean_ctor_get(v_t_1797_, 0);
        lean_inc_ref(v_c_u2081_1799_);
        v_c_u2082_1800_ = lean_ctor_get(v_t_1797_, 1);
        lean_inc_ref(v_c_u2082_1800_);
        v_c_u2083_1801_ = lean_ctor_get(v_t_1797_, 2);
        lean_inc_ref(v_c_u2083_1801_);
        lean_dec_ref_known(v_t_1797_, 3);
        v___x_1802_ = lean_apply_3(v_k_1798_, v_c_u2081_1799_, v_c_u2082_1800_, v_c_u2083_1801_);
        return v___x_1802_;
    } else {
        let mut v_c_1803_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
        v_c_1803_ = lean_ctor_get(v_t_1797_, 0);
        lean_inc_ref(v_c_1803_);
        lean_dec_ref(v_t_1797_);
        v___x_1804_ = lean_apply_1(v_k_1798_, v_c_1803_);
        return v___x_1804_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(
    mut v_motive__12_1805_: *mut LeanObject,
    mut v_ctorIdx_1806_: *mut LeanObject,
    mut v_t_1807_: *mut LeanObject,
    mut v_h_1808_: *mut LeanObject,
    mut v_k_1809_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    v___x_1810_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1807_, v_k_1809_);
    return v___x_1810_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___boxed(
    mut v_motive__12_1811_: *mut LeanObject,
    mut v_ctorIdx_1812_: *mut LeanObject,
    mut v_t_1813_: *mut LeanObject,
    mut v_h_1814_: *mut LeanObject,
    mut v_k_1815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1816_: *mut LeanObject = core::ptr::null_mut();
    v_res_1816_ = l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim(
        v_motive__12_1811_,
        v_ctorIdx_1812_,
        v_t_1813_,
        v_h_1814_,
        v_k_1815_,
    );
    lean_dec(v_ctorIdx_1812_);
    return v_res_1816_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim___redArg(
    mut v_t_1817_: *mut LeanObject,
    mut v_dvd_1818_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1819_: *mut LeanObject = core::ptr::null_mut();
    v___x_1819_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1817_, v_dvd_1818_);
    return v___x_1819_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_dvd_elim(
    mut v_motive__12_1820_: *mut LeanObject,
    mut v_t_1821_: *mut LeanObject,
    mut v_h_1822_: *mut LeanObject,
    mut v_dvd_1823_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1824_: *mut LeanObject = core::ptr::null_mut();
    v___x_1824_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1821_, v_dvd_1823_);
    return v___x_1824_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim___redArg(
    mut v_t_1825_: *mut LeanObject,
    mut v_le_1826_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1827_: *mut LeanObject = core::ptr::null_mut();
    v___x_1827_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1825_, v_le_1826_);
    return v___x_1827_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_le_elim(
    mut v_motive__12_1828_: *mut LeanObject,
    mut v_t_1829_: *mut LeanObject,
    mut v_h_1830_: *mut LeanObject,
    mut v_le_1831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1832_: *mut LeanObject = core::ptr::null_mut();
    v___x_1832_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1829_, v_le_1831_);
    return v___x_1832_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim___redArg(
    mut v_t_1833_: *mut LeanObject,
    mut v_eq_1834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1835_: *mut LeanObject = core::ptr::null_mut();
    v___x_1835_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1833_, v_eq_1834_);
    return v___x_1835_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_eq_elim(
    mut v_motive__12_1836_: *mut LeanObject,
    mut v_t_1837_: *mut LeanObject,
    mut v_h_1838_: *mut LeanObject,
    mut v_eq_1839_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1840_: *mut LeanObject = core::ptr::null_mut();
    v___x_1840_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1837_, v_eq_1839_);
    return v___x_1840_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim___redArg(
    mut v_t_1841_: *mut LeanObject,
    mut v_diseq_1842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1843_: *mut LeanObject = core::ptr::null_mut();
    v___x_1843_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1841_, v_diseq_1842_);
    return v___x_1843_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_diseq_elim(
    mut v_motive__12_1844_: *mut LeanObject,
    mut v_t_1845_: *mut LeanObject,
    mut v_h_1846_: *mut LeanObject,
    mut v_diseq_1847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1848_: *mut LeanObject = core::ptr::null_mut();
    v___x_1848_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1845_, v_diseq_1847_);
    return v___x_1848_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim___redArg(
    mut v_t_1849_: *mut LeanObject,
    mut v_cooper_1850_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    v___x_1851_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1849_, v_cooper_1850_);
    return v___x_1851_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_cooper_elim(
    mut v_motive__12_1852_: *mut LeanObject,
    mut v_t_1853_: *mut LeanObject,
    mut v_h_1854_: *mut LeanObject,
    mut v_cooper_1855_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1856_: *mut LeanObject = core::ptr::null_mut();
    v___x_1856_ =
        l_Lean_Meta_Grind_Arith_Cutsat_UnsatProof_ctorElim___redArg(v_t_1853_, v_cooper_1855_);
    return v___x_1856_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0()
-> *mut LeanObject {
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1858_: *mut LeanObject = core::ptr::null_mut();
    v___x_1857_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0,
    );
    v___x_1858_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1858_, 0, v___x_1857_);
    return v___x_1858_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3()
-> *mut LeanObject {
    let mut v___x_1862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut LeanObject = core::ptr::null_mut();
    v___x_1862_ = lean_box(0);
    v___x_1863_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__2;
    v___x_1864_ = l_Lean_Expr_const___override(v___x_1863_, v___x_1862_);
    return v___x_1864_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4()
-> *mut LeanObject {
    let mut v___x_1865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1866_: *mut LeanObject = core::ptr::null_mut();
    v___x_1865_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3,
    );
    v___x_1866_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1866_, 0, v___x_1865_);
    return v___x_1866_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5()
-> *mut LeanObject {
    let mut v___x_1867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut LeanObject = core::ptr::null_mut();
    v___x_1867_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__4,
    );
    v___x_1868_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0,
    );
    v___x_1869_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1869_, 0, v___x_1868_);
    lean_ctor_set(v___x_1869_, 1, v___x_1867_);
    return v___x_1869_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr() -> *mut LeanObject {
    let mut v___x_1870_: *mut LeanObject = core::ptr::null_mut();
    v___x_1870_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5,
    );
    return v___x_1870_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0()
-> *mut LeanObject {
    let mut v___x_1871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1872_: *mut LeanObject = core::ptr::null_mut();
    v___x_1871_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__3,
    );
    v___x_1872_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1872_, 0, v___x_1871_);
    return v___x_1872_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1()
-> *mut LeanObject {
    let mut v___x_1873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1876_: *mut LeanObject = core::ptr::null_mut();
    v___x_1873_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__0,
    );
    v___x_1874_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__0,
    );
    v___x_1875_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instHashablePoly__lean_hash___closed__0,
    );
    v___x_1876_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1876_, 0, v___x_1875_);
    lean_ctor_set(v___x_1876_, 1, v___x_1874_);
    lean_ctor_set(v___x_1876_, 2, v___x_1873_);
    return v___x_1876_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr() -> *mut LeanObject {
    let mut v___x_1877_: *mut LeanObject = core::ptr::null_mut();
    v___x_1877_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr___closed__1,
    );
    return v___x_1877_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0()
-> *mut LeanObject {
    let mut v___x_1878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: u8 = 0;
    let mut v___x_1881_: *mut LeanObject = core::ptr::null_mut();
    v___x_1878_ = lean_box(0);
    v___x_1879_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr___closed__5,
    );
    v___x_1880_ = 0;
    v___x_1881_ = lean_alloc_ctor(0, 3, (1) as u32);
    lean_ctor_set(v___x_1881_, 0, v___x_1879_);
    lean_ctor_set(v___x_1881_, 1, v___x_1879_);
    lean_ctor_set(v___x_1881_, 2, v___x_1878_);
    lean_ctor_set_uint8(
        v___x_1881_,
        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
        v___x_1880_,
    );
    return v___x_1881_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred() -> *mut LeanObject
{
    let mut v___x_1882_: *mut LeanObject = core::ptr::null_mut();
    v___x_1882_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0,
    );
    return v___x_1882_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1()
-> *mut LeanObject {
    let mut v___x_1885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1888_: *mut LeanObject = core::ptr::null_mut();
    v___x_1885_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__0;
    v___x_1886_ = lean_unsigned_to_nat(0);
    v___x_1887_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred___closed__0,
    );
    v___x_1888_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1888_, 0, v___x_1887_);
    lean_ctor_set(v___x_1888_, 1, v___x_1886_);
    lean_ctor_set(v___x_1888_, 2, v___x_1885_);
    return v___x_1888_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit() -> *mut LeanObject {
    let mut v___x_1889_: *mut LeanObject = core::ptr::null_mut();
    v___x_1889_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit___closed__1,
    );
    return v___x_1889_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1890_: *mut LeanObject = core::ptr::null_mut();
    v___x_1890_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1890_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_1891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1892_: *mut LeanObject = core::ptr::null_mut();
    v___x_1891_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__0);
    v___x_1892_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1892_, 0, v___x_1891_);
    return v___x_1892_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(
    mut v_00_u03b2_1893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1894_: *mut LeanObject = core::ptr::null_mut();
    v___x_1894_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0___closed__1);
    return v___x_1894_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0()
-> *mut LeanObject {
    let mut v___x_1895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut LeanObject = core::ptr::null_mut();
    v___x_1895_ = lean_unsigned_to_nat(32);
    v___x_1896_ = lean_mk_empty_array_with_capacity(v___x_1895_);
    v___x_1897_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1897_, 0, v___x_1896_);
    return v___x_1897_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1()
-> *mut LeanObject {
    let mut v___x_1898_: usize = 0;
    let mut v___x_1899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1903_: *mut LeanObject = core::ptr::null_mut();
    v___x_1898_ = 5usize;
    v___x_1899_ = lean_unsigned_to_nat(0);
    v___x_1900_ = lean_unsigned_to_nat(32);
    v___x_1901_ = lean_mk_empty_array_with_capacity(v___x_1900_);
    v___x_1902_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__0,
    );
    v___x_1903_ = lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    lean_ctor_set(v___x_1903_, 0, v___x_1902_);
    lean_ctor_set(v___x_1903_, 1, v___x_1901_);
    lean_ctor_set(v___x_1903_, 2, v___x_1899_);
    lean_ctor_set(v___x_1903_, 3, v___x_1899_);
    lean_ctor_set_usize(v___x_1903_, 4, v___x_1898_);
    return v___x_1903_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2()
-> *mut LeanObject {
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    v___x_1904_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_1904_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3()
-> *mut LeanObject {
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut LeanObject = core::ptr::null_mut();
    v___x_1905_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__2,
    );
    v___x_1906_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1906_, 0, v___x_1905_);
    return v___x_1906_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4()
-> *mut LeanObject {
    let mut v___x_1907_: *mut LeanObject = core::ptr::null_mut();
    v___x_1907_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default_spec__0(lean_box(0));
    return v___x_1907_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5()
-> *mut LeanObject {
    let mut v___x_1908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: u8 = 0;
    let mut v___x_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut LeanObject = core::ptr::null_mut();
    v___x_1908_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__4,
    );
    v___x_1909_ = lean_box(0);
    v___x_1910_ = 0;
    v___x_1911_ = lean_unsigned_to_nat(0);
    v___x_1912_ = lean_box(0);
    v___x_1913_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__3,
    );
    v___x_1914_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__1,
    );
    v___x_1915_ = lean_alloc_ctor(0, 23, (2) as u32);
    lean_ctor_set(v___x_1915_, 0, v___x_1914_);
    lean_ctor_set(v___x_1915_, 1, v___x_1913_);
    lean_ctor_set(v___x_1915_, 2, v___x_1914_);
    lean_ctor_set(v___x_1915_, 3, v___x_1913_);
    lean_ctor_set(v___x_1915_, 4, v___x_1913_);
    lean_ctor_set(v___x_1915_, 5, v___x_1913_);
    lean_ctor_set(v___x_1915_, 6, v___x_1914_);
    lean_ctor_set(v___x_1915_, 7, v___x_1914_);
    lean_ctor_set(v___x_1915_, 8, v___x_1914_);
    lean_ctor_set(v___x_1915_, 9, v___x_1914_);
    lean_ctor_set(v___x_1915_, 10, v___x_1914_);
    lean_ctor_set(v___x_1915_, 11, v___x_1912_);
    lean_ctor_set(v___x_1915_, 12, v___x_1914_);
    lean_ctor_set(v___x_1915_, 13, v___x_1914_);
    lean_ctor_set(v___x_1915_, 14, v___x_1911_);
    lean_ctor_set(v___x_1915_, 15, v___x_1909_);
    lean_ctor_set(v___x_1915_, 16, v___x_1913_);
    lean_ctor_set(v___x_1915_, 17, v___x_1908_);
    lean_ctor_set(v___x_1915_, 18, v___x_1913_);
    lean_ctor_set(v___x_1915_, 19, v___x_1914_);
    lean_ctor_set(v___x_1915_, 20, v___x_1913_);
    lean_ctor_set(v___x_1915_, 21, v___x_1913_);
    lean_ctor_set(v___x_1915_, 22, v___x_1913_);
    lean_ctor_set_uint8(
        v___x_1915_,
        (core::mem::size_of::<*mut LeanObject>() * 23) as u32,
        v___x_1910_,
    );
    lean_ctor_set_uint8(
        v___x_1915_,
        (core::mem::size_of::<*mut LeanObject>() * 23 + 1) as u32,
        v___x_1910_,
    );
    return v___x_1915_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default() -> *mut LeanObject {
    let mut v___x_1916_: *mut LeanObject = core::ptr::null_mut();
    v___x_1916_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5,
    );
    return v___x_1916_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState() -> *mut LeanObject {
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    v___x_1917_ = l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default;
    return v___x_1917_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(
    mut v___x_1918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1920_: *mut LeanObject = core::ptr::null_mut();
    v___x_1920_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_1920_, 0, v___x_1918_);
    return v___x_1920_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(
    mut v___x_1921_: *mut LeanObject,
    mut v___y_1922_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1923_: *mut LeanObject = core::ptr::null_mut();
    v_res_1923_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_(v___x_1921_);
    return v_res_1923_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_1924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1925_: *mut LeanObject = core::ptr::null_mut();
    v___x_1924_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5_once
        ),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default___closed__5,
    );
    v___f_1925_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___lam__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    lean_closure_set(v___f_1925_, 0, v___x_1924_);
    return v___f_1925_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___f_1927_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut LeanObject = core::ptr::null_mut();
    v___f_1927_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn___closed__0_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_);
    v___x_1928_ = l_Lean_Meta_Grind_registerSolverExtension___redArg(v___f_1927_);
    return v___x_1928_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2____boxed(
    mut v_a_1929_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1930_: *mut LeanObject = core::ptr::null_mut();
    v_res_1930_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
    return v_res_1930_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Int_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedLeCnstr);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedDvdCnstr);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplitPred);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedCooperSplit);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState_default);
    l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState =
        _init_l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState();
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_instInhabitedState);
    res = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_0__Lean_Meta_Grind_Arith_Cutsat_initFn_00___x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types_1820690160____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt = lean_io_result_get_value(res);
    lean_mark_persistent(l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt);
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Int_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_ToIntInfo(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
}

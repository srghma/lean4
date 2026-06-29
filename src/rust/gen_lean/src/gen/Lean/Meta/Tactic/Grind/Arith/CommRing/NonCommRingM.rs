// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.NonCommRingM
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Sym::Canon::l_Lean_Meta_Sym_canon;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Sym::SynthInstance::l_Lean_Meta_Sym_synthInstanceMeta_x3f;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg, l_Lean_Meta_Grind_Arith_CommRing_ringExt,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg;
use crate::ffi::lean_array_fset;
use crate::ffi::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::ffi::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt,
};
use crate::ffi::lean_st_ref_get;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__1_value
        ) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value:
    crate::leanh::LeanStringObject<39> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 114, 105, 110, 103, 73, 100,
        0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value:
    crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 119, 111, 32, 100,
        105, 102, 102, 101, 114, 101, 110, 116, 32, 114, 105, 110, 103, 115, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value:
    crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 13,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(
    mut v_ringId_835_: *mut crate::leanh::LeanObject,
    mut v_x_836_: *mut crate::leanh::LeanObject,
    mut v_a_837_: *mut crate::leanh::LeanObject,
    mut v_a_838_: *mut crate::leanh::LeanObject,
    mut v_a_839_: *mut crate::leanh::LeanObject,
    mut v_a_840_: *mut crate::leanh::LeanObject,
    mut v_a_841_: *mut crate::leanh::LeanObject,
    mut v_a_842_: *mut crate::leanh::LeanObject,
    mut v_a_843_: *mut crate::leanh::LeanObject,
    mut v_a_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_a_846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_846_);
    crate::leanh::lean_inc_ref(v_a_845_);
    crate::leanh::lean_inc(v_a_844_);
    crate::leanh::lean_inc_ref(v_a_843_);
    crate::leanh::lean_inc(v_a_842_);
    crate::leanh::lean_inc_ref(v_a_841_);
    crate::leanh::lean_inc(v_a_840_);
    crate::leanh::lean_inc_ref(v_a_839_);
    crate::leanh::lean_inc(v_a_838_);
    crate::leanh::lean_inc(v_a_837_);
    v___x_848_ = crate::leanh::lean_apply_12(
        v_x_836_,
        v_ringId_835_,
        v_a_837_,
        v_a_838_,
        v_a_839_,
        v_a_840_,
        v_a_841_,
        v_a_842_,
        v_a_843_,
        v_a_844_,
        v_a_845_,
        v_a_846_,
        crate::leanh::lean_box(0),
    );
    return v___x_848_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg___boxed(
    mut v_ringId_849_: *mut crate::leanh::LeanObject,
    mut v_x_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
    mut v_a_852_: *mut crate::leanh::LeanObject,
    mut v_a_853_: *mut crate::leanh::LeanObject,
    mut v_a_854_: *mut crate::leanh::LeanObject,
    mut v_a_855_: *mut crate::leanh::LeanObject,
    mut v_a_856_: *mut crate::leanh::LeanObject,
    mut v_a_857_: *mut crate::leanh::LeanObject,
    mut v_a_858_: *mut crate::leanh::LeanObject,
    mut v_a_859_: *mut crate::leanh::LeanObject,
    mut v_a_860_: *mut crate::leanh::LeanObject,
    mut v_a_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_862_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___redArg(
        v_ringId_849_,
        v_x_850_,
        v_a_851_,
        v_a_852_,
        v_a_853_,
        v_a_854_,
        v_a_855_,
        v_a_856_,
        v_a_857_,
        v_a_858_,
        v_a_859_,
        v_a_860_,
    );
    crate::leanh::lean_dec(v_a_860_);
    crate::leanh::lean_dec_ref(v_a_859_);
    crate::leanh::lean_dec(v_a_858_);
    crate::leanh::lean_dec_ref(v_a_857_);
    crate::leanh::lean_dec(v_a_856_);
    crate::leanh::lean_dec_ref(v_a_855_);
    crate::leanh::lean_dec(v_a_854_);
    crate::leanh::lean_dec_ref(v_a_853_);
    crate::leanh::lean_dec(v_a_852_);
    crate::leanh::lean_dec(v_a_851_);
    return v_res_862_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(
    mut v_00_u03b1_863_: *mut crate::leanh::LeanObject,
    mut v_ringId_864_: *mut crate::leanh::LeanObject,
    mut v_x_865_: *mut crate::leanh::LeanObject,
    mut v_a_866_: *mut crate::leanh::LeanObject,
    mut v_a_867_: *mut crate::leanh::LeanObject,
    mut v_a_868_: *mut crate::leanh::LeanObject,
    mut v_a_869_: *mut crate::leanh::LeanObject,
    mut v_a_870_: *mut crate::leanh::LeanObject,
    mut v_a_871_: *mut crate::leanh::LeanObject,
    mut v_a_872_: *mut crate::leanh::LeanObject,
    mut v_a_873_: *mut crate::leanh::LeanObject,
    mut v_a_874_: *mut crate::leanh::LeanObject,
    mut v_a_875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_875_);
    crate::leanh::lean_inc_ref(v_a_874_);
    crate::leanh::lean_inc(v_a_873_);
    crate::leanh::lean_inc_ref(v_a_872_);
    crate::leanh::lean_inc(v_a_871_);
    crate::leanh::lean_inc_ref(v_a_870_);
    crate::leanh::lean_inc(v_a_869_);
    crate::leanh::lean_inc_ref(v_a_868_);
    crate::leanh::lean_inc(v_a_867_);
    crate::leanh::lean_inc(v_a_866_);
    v___x_877_ = crate::leanh::lean_apply_12(
        v_x_865_,
        v_ringId_864_,
        v_a_866_,
        v_a_867_,
        v_a_868_,
        v_a_869_,
        v_a_870_,
        v_a_871_,
        v_a_872_,
        v_a_873_,
        v_a_874_,
        v_a_875_,
        crate::leanh::lean_box(0),
    );
    return v___x_877_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run___boxed(
    mut v_00_u03b1_878_: *mut crate::leanh::LeanObject,
    mut v_ringId_879_: *mut crate::leanh::LeanObject,
    mut v_x_880_: *mut crate::leanh::LeanObject,
    mut v_a_881_: *mut crate::leanh::LeanObject,
    mut v_a_882_: *mut crate::leanh::LeanObject,
    mut v_a_883_: *mut crate::leanh::LeanObject,
    mut v_a_884_: *mut crate::leanh::LeanObject,
    mut v_a_885_: *mut crate::leanh::LeanObject,
    mut v_a_886_: *mut crate::leanh::LeanObject,
    mut v_a_887_: *mut crate::leanh::LeanObject,
    mut v_a_888_: *mut crate::leanh::LeanObject,
    mut v_a_889_: *mut crate::leanh::LeanObject,
    mut v_a_890_: *mut crate::leanh::LeanObject,
    mut v_a_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_892_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_run(
        v_00_u03b1_878_,
        v_ringId_879_,
        v_x_880_,
        v_a_881_,
        v_a_882_,
        v_a_883_,
        v_a_884_,
        v_a_885_,
        v_a_886_,
        v_a_887_,
        v_a_888_,
        v_a_889_,
        v_a_890_,
    );
    crate::leanh::lean_dec(v_a_890_);
    crate::leanh::lean_dec_ref(v_a_889_);
    crate::leanh::lean_dec(v_a_888_);
    crate::leanh::lean_dec_ref(v_a_887_);
    crate::leanh::lean_dec(v_a_886_);
    crate::leanh::lean_dec_ref(v_a_885_);
    crate::leanh::lean_dec(v_a_884_);
    crate::leanh::lean_dec_ref(v_a_883_);
    crate::leanh::lean_dec(v_a_882_);
    crate::leanh::lean_dec(v_a_881_);
    return v_res_892_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(
    mut v_e_893_: *mut crate::leanh::LeanObject,
    mut v___y_894_: *mut crate::leanh::LeanObject,
    mut v___y_895_: *mut crate::leanh::LeanObject,
    mut v___y_896_: *mut crate::leanh::LeanObject,
    mut v___y_897_: *mut crate::leanh::LeanObject,
    mut v___y_898_: *mut crate::leanh::LeanObject,
    mut v___y_899_: *mut crate::leanh::LeanObject,
    mut v___y_900_: *mut crate::leanh::LeanObject,
    mut v___y_901_: *mut crate::leanh::LeanObject,
    mut v___y_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
    mut v___y_904_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_906_ = l_Lean_Meta_Sym_canon(
        v_e_893_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_,
    );
    if crate::leanh::lean_obj_tag(v___x_906_) == 0 {
        let mut v_a_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_907_ = crate::leanh::lean_ctor_get(v___x_906_, 0);
        crate::leanh::lean_inc(v_a_907_);
        crate::leanh::lean_dec_ref_known(v___x_906_, 1);
        v___x_908_ = l_Lean_Meta_Sym_shareCommon___redArg(v_a_907_, v___y_900_);
        return v___x_908_;
    } else {
        return v___x_906_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0___boxed(
    mut v_e_909_: *mut crate::leanh::LeanObject,
    mut v___y_910_: *mut crate::leanh::LeanObject,
    mut v___y_911_: *mut crate::leanh::LeanObject,
    mut v___y_912_: *mut crate::leanh::LeanObject,
    mut v___y_913_: *mut crate::leanh::LeanObject,
    mut v___y_914_: *mut crate::leanh::LeanObject,
    mut v___y_915_: *mut crate::leanh::LeanObject,
    mut v___y_916_: *mut crate::leanh::LeanObject,
    mut v___y_917_: *mut crate::leanh::LeanObject,
    mut v___y_918_: *mut crate::leanh::LeanObject,
    mut v___y_919_: *mut crate::leanh::LeanObject,
    mut v___y_920_: *mut crate::leanh::LeanObject,
    mut v___y_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_922_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__0(
        v_e_909_, v___y_910_, v___y_911_, v___y_912_, v___y_913_, v___y_914_, v___y_915_,
        v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_,
    );
    crate::leanh::lean_dec(v___y_920_);
    crate::leanh::lean_dec_ref(v___y_919_);
    crate::leanh::lean_dec(v___y_918_);
    crate::leanh::lean_dec_ref(v___y_917_);
    crate::leanh::lean_dec(v___y_916_);
    crate::leanh::lean_dec_ref(v___y_915_);
    crate::leanh::lean_dec(v___y_914_);
    crate::leanh::lean_dec_ref(v___y_913_);
    crate::leanh::lean_dec(v___y_912_);
    crate::leanh::lean_dec(v___y_911_);
    crate::leanh::lean_dec(v___y_910_);
    return v_res_922_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(
    mut v_e_923_: *mut crate::leanh::LeanObject,
    mut v___y_924_: *mut crate::leanh::LeanObject,
    mut v___y_925_: *mut crate::leanh::LeanObject,
    mut v___y_926_: *mut crate::leanh::LeanObject,
    mut v___y_927_: *mut crate::leanh::LeanObject,
    mut v___y_928_: *mut crate::leanh::LeanObject,
    mut v___y_929_: *mut crate::leanh::LeanObject,
    mut v___y_930_: *mut crate::leanh::LeanObject,
    mut v___y_931_: *mut crate::leanh::LeanObject,
    mut v___y_932_: *mut crate::leanh::LeanObject,
    mut v___y_933_: *mut crate::leanh::LeanObject,
    mut v___y_934_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_936_ = l_Lean_Meta_Sym_synthInstanceMeta_x3f(
        v_e_923_, v___y_931_, v___y_932_, v___y_933_, v___y_934_,
    );
    return v___x_936_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1___boxed(
    mut v_e_937_: *mut crate::leanh::LeanObject,
    mut v___y_938_: *mut crate::leanh::LeanObject,
    mut v___y_939_: *mut crate::leanh::LeanObject,
    mut v___y_940_: *mut crate::leanh::LeanObject,
    mut v___y_941_: *mut crate::leanh::LeanObject,
    mut v___y_942_: *mut crate::leanh::LeanObject,
    mut v___y_943_: *mut crate::leanh::LeanObject,
    mut v___y_944_: *mut crate::leanh::LeanObject,
    mut v___y_945_: *mut crate::leanh::LeanObject,
    mut v___y_946_: *mut crate::leanh::LeanObject,
    mut v___y_947_: *mut crate::leanh::LeanObject,
    mut v___y_948_: *mut crate::leanh::LeanObject,
    mut v___y_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_950_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadCanonNonCommRingM___lam__1(
        v_e_937_, v___y_938_, v___y_939_, v___y_940_, v___y_941_, v___y_942_, v___y_943_,
        v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_,
    );
    crate::leanh::lean_dec(v___y_948_);
    crate::leanh::lean_dec_ref(v___y_947_);
    crate::leanh::lean_dec(v___y_946_);
    crate::leanh::lean_dec_ref(v___y_945_);
    crate::leanh::lean_dec(v___y_944_);
    crate::leanh::lean_dec_ref(v___y_943_);
    crate::leanh::lean_dec(v___y_942_);
    crate::leanh::lean_dec_ref(v___y_941_);
    crate::leanh::lean_dec(v___y_940_);
    crate::leanh::lean_dec(v___y_939_);
    crate::leanh::lean_dec(v___y_938_);
    return v_res_950_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(
    mut v_msgData_957_: *mut crate::leanh::LeanObject,
    mut v___y_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_963_ = lean_st_ref_get(v___y_961_);
    v_env_964_ = crate::leanh::lean_ctor_get(v___x_963_, 0);
    crate::leanh::lean_inc_ref(v_env_964_);
    crate::leanh::lean_dec(v___x_963_);
    v___x_965_ = lean_st_ref_get(v___y_959_);
    v_mctx_966_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
    crate::leanh::lean_inc_ref(v_mctx_966_);
    crate::leanh::lean_dec(v___x_965_);
    v_lctx_967_ = crate::leanh::lean_ctor_get(v___y_958_, 2);
    v_options_968_ = crate::leanh::lean_ctor_get(v___y_960_, 2);
    crate::leanh::lean_inc_ref(v_options_968_);
    crate::leanh::lean_inc_ref(v_lctx_967_);
    v___x_969_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_969_, 0, v_env_964_);
    crate::leanh::lean_ctor_set(v___x_969_, 1, v_mctx_966_);
    crate::leanh::lean_ctor_set(v___x_969_, 2, v_lctx_967_);
    crate::leanh::lean_ctor_set(v___x_969_, 3, v_options_968_);
    v___x_970_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_970_, 0, v___x_969_);
    crate::leanh::lean_ctor_set(v___x_970_, 1, v_msgData_957_);
    v___x_971_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_971_, 0, v___x_970_);
    return v___x_971_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0___boxed(
    mut v_msgData_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v___y_974_: *mut crate::leanh::LeanObject,
    mut v___y_975_: *mut crate::leanh::LeanObject,
    mut v___y_976_: *mut crate::leanh::LeanObject,
    mut v___y_977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_978_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msgData_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_);
    crate::leanh::lean_dec(v___y_976_);
    crate::leanh::lean_dec_ref(v___y_975_);
    crate::leanh::lean_dec(v___y_974_);
    crate::leanh::lean_dec_ref(v___y_973_);
    return v_res_978_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(
    mut v_msg_979_: *mut crate::leanh::LeanObject,
    mut v___y_980_: *mut crate::leanh::LeanObject,
    mut v___y_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_990_: u8 = 0;
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_995_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_985_ = crate::leanh::lean_ctor_get(v___y_982_, 5);
                v___x_986_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0_spec__0(v_msg_979_, v___y_980_, v___y_981_, v___y_982_, v___y_983_);
                v_a_987_ = crate::leanh::lean_ctor_get(v___x_986_, 0);
                v_isSharedCheck_995_ = (!crate::leanh::lean_is_exclusive(v___x_986_)) as u8;
                if v_isSharedCheck_995_ == 0 {
                    v___x_989_ = v___x_986_;
                    v_isShared_990_ = v_isSharedCheck_995_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_987_);
                    crate::leanh::lean_dec(v___x_986_);
                    v___x_989_ = crate::leanh::lean_box(0);
                    v_isShared_990_ = v_isSharedCheck_995_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_985_);
                v___x_991_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_991_, 0, v_ref_985_);
                crate::leanh::lean_ctor_set(v___x_991_, 1, v_a_987_);
                if v_isShared_990_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_989_, 1);
                    crate::leanh::lean_ctor_set(v___x_989_, 0, v___x_991_);
                    v___x_993_ = v___x_989_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_994_, 0, v___x_991_);
                    v___x_993_ = v_reuseFailAlloc_994_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_993_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg___boxed(
    mut v_msg_996_: *mut crate::leanh::LeanObject,
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v___y_998_: *mut crate::leanh::LeanObject,
    mut v___y_999_: *mut crate::leanh::LeanObject,
    mut v___y_1000_: *mut crate::leanh::LeanObject,
    mut v___y_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1002_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_996_, v___y_997_, v___y_998_, v___y_999_, v___y_1000_);
    crate::leanh::lean_dec(v___y_1000_);
    crate::leanh::lean_dec_ref(v___y_999_);
    crate::leanh::lean_dec(v___y_998_);
    crate::leanh::lean_dec_ref(v___y_997_);
    return v_res_1002_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1004_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__0;
    v___x_1005_ = l_Lean_stringToMessageData(v___x_1004_);
    return v___x_1005_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
    mut v_a_1006_: *mut crate::leanh::LeanObject,
    mut v_a_1007_: *mut crate::leanh::LeanObject,
    mut v_a_1008_: *mut crate::leanh::LeanObject,
    mut v_a_1009_: *mut crate::leanh::LeanObject,
    mut v_a_1010_: *mut crate::leanh::LeanObject,
    mut v_a_1011_: *mut crate::leanh::LeanObject,
    mut v_a_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_a_1014_: *mut crate::leanh::LeanObject,
    mut v_a_1015_: *mut crate::leanh::LeanObject,
    mut v_a_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v_ncRings_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1032_: u8 = 0;
    let mut v_a_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1036_: u8 = 0;
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1040_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1018_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1007_, v_a_1015_);
                if crate::leanh::lean_obj_tag(v___x_1018_) == 0 {
                    v_a_1019_ = crate::leanh::lean_ctor_get(v___x_1018_, 0);
                    v_isSharedCheck_1032_ = (!crate::leanh::lean_is_exclusive(v___x_1018_)) as u8;
                    if v_isSharedCheck_1032_ == 0 {
                        v___x_1021_ = v___x_1018_;
                        v_isShared_1022_ = v_isSharedCheck_1032_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1019_);
                        crate::leanh::lean_dec(v___x_1018_);
                        v___x_1021_ = crate::leanh::lean_box(0);
                        v_isShared_1022_ = v_isSharedCheck_1032_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1033_ = crate::leanh::lean_ctor_get(v___x_1018_, 0);
                    v_isSharedCheck_1040_ = (!crate::leanh::lean_is_exclusive(v___x_1018_)) as u8;
                    if v_isSharedCheck_1040_ == 0 {
                        v___x_1035_ = v___x_1018_;
                        v_isShared_1036_ = v_isSharedCheck_1040_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1033_);
                        crate::leanh::lean_dec(v___x_1018_);
                        v___x_1035_ = crate::leanh::lean_box(0);
                        v_isShared_1036_ = v_isSharedCheck_1040_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_ncRings_1023_ = crate::leanh::lean_ctor_get(v_a_1019_, 6);
                crate::leanh::lean_inc_ref(v_ncRings_1023_);
                crate::leanh::lean_dec(v_a_1019_);
                v___x_1024_ = lean_array_get_size(v_ncRings_1023_);
                v___x_1025_ = lean_nat_dec_lt(v_a_1006_, v___x_1024_);
                if v___x_1025_ == 0 {
                    crate::leanh::lean_dec_ref(v_ncRings_1023_);
                    crate::leanh::lean_del_object(v___x_1021_);
                    v___x_1026_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___closed__1,
                    );
                    v___x_1027_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v___x_1026_, v_a_1013_, v_a_1014_, v_a_1015_, v_a_1016_);
                    return v___x_1027_;
                } else {
                    v___x_1028_ = lean_array_fget(v_ncRings_1023_, v_a_1006_);
                    crate::leanh::lean_dec_ref(v_ncRings_1023_);
                    if v_isShared_1022_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1021_, 0, v___x_1028_);
                        v___x_1030_ = v___x_1021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1031_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1031_, 0, v___x_1028_);
                        v___x_1030_ = v_reuseFailAlloc_1031_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1030_;
            }
            3 => {
                if v_isShared_1036_ == 0 {
                    v___x_1038_ = v___x_1035_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1039_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_a_1033_);
                    v___x_1038_ = v_reuseFailAlloc_1039_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1038_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed(
    mut v_a_1041_: *mut crate::leanh::LeanObject,
    mut v_a_1042_: *mut crate::leanh::LeanObject,
    mut v_a_1043_: *mut crate::leanh::LeanObject,
    mut v_a_1044_: *mut crate::leanh::LeanObject,
    mut v_a_1045_: *mut crate::leanh::LeanObject,
    mut v_a_1046_: *mut crate::leanh::LeanObject,
    mut v_a_1047_: *mut crate::leanh::LeanObject,
    mut v_a_1048_: *mut crate::leanh::LeanObject,
    mut v_a_1049_: *mut crate::leanh::LeanObject,
    mut v_a_1050_: *mut crate::leanh::LeanObject,
    mut v_a_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing(
        v_a_1041_, v_a_1042_, v_a_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_,
        v_a_1049_, v_a_1050_, v_a_1051_,
    );
    crate::leanh::lean_dec(v_a_1051_);
    crate::leanh::lean_dec_ref(v_a_1050_);
    crate::leanh::lean_dec(v_a_1049_);
    crate::leanh::lean_dec_ref(v_a_1048_);
    crate::leanh::lean_dec(v_a_1047_);
    crate::leanh::lean_dec_ref(v_a_1046_);
    crate::leanh::lean_dec(v_a_1045_);
    crate::leanh::lean_dec_ref(v_a_1044_);
    crate::leanh::lean_dec(v_a_1043_);
    crate::leanh::lean_dec(v_a_1042_);
    crate::leanh::lean_dec(v_a_1041_);
    return v_res_1053_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(
    mut v_00_u03b1_1054_: *mut crate::leanh::LeanObject,
    mut v_msg_1055_: *mut crate::leanh::LeanObject,
    mut v___y_1056_: *mut crate::leanh::LeanObject,
    mut v___y_1057_: *mut crate::leanh::LeanObject,
    mut v___y_1058_: *mut crate::leanh::LeanObject,
    mut v___y_1059_: *mut crate::leanh::LeanObject,
    mut v___y_1060_: *mut crate::leanh::LeanObject,
    mut v___y_1061_: *mut crate::leanh::LeanObject,
    mut v___y_1062_: *mut crate::leanh::LeanObject,
    mut v___y_1063_: *mut crate::leanh::LeanObject,
    mut v___y_1064_: *mut crate::leanh::LeanObject,
    mut v___y_1065_: *mut crate::leanh::LeanObject,
    mut v___y_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1068_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___redArg(v_msg_1055_, v___y_1063_, v___y_1064_, v___y_1065_, v___y_1066_);
    return v___x_1068_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0___boxed(
    mut v_00_u03b1_1069_: *mut crate::leanh::LeanObject,
    mut v_msg_1070_: *mut crate::leanh::LeanObject,
    mut v___y_1071_: *mut crate::leanh::LeanObject,
    mut v___y_1072_: *mut crate::leanh::LeanObject,
    mut v___y_1073_: *mut crate::leanh::LeanObject,
    mut v___y_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
    mut v___y_1078_: *mut crate::leanh::LeanObject,
    mut v___y_1079_: *mut crate::leanh::LeanObject,
    mut v___y_1080_: *mut crate::leanh::LeanObject,
    mut v___y_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1083_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing_spec__0(
            v_00_u03b1_1069_,
            v_msg_1070_,
            v___y_1071_,
            v___y_1072_,
            v___y_1073_,
            v___y_1074_,
            v___y_1075_,
            v___y_1076_,
            v___y_1077_,
            v___y_1078_,
            v___y_1079_,
            v___y_1080_,
            v___y_1081_,
        );
    crate::leanh::lean_dec(v___y_1081_);
    crate::leanh::lean_dec_ref(v___y_1080_);
    crate::leanh::lean_dec(v___y_1079_);
    crate::leanh::lean_dec_ref(v___y_1078_);
    crate::leanh::lean_dec(v___y_1077_);
    crate::leanh::lean_dec_ref(v___y_1076_);
    crate::leanh::lean_dec(v___y_1075_);
    crate::leanh::lean_dec_ref(v___y_1074_);
    crate::leanh::lean_dec(v___y_1073_);
    crate::leanh::lean_dec(v___y_1072_);
    crate::leanh::lean_dec(v___y_1071_);
    return v_res_1083_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_f_1085_: *mut crate::leanh::LeanObject,
    mut v_s_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_1100_: u8 = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: u8 = 0;
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v_v_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1114_: u8 = 0;
    let mut v_unused_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_1087_ = crate::leanh::lean_ctor_get(v_s_1086_, 0);
                v_typeIdOf_1088_ = crate::leanh::lean_ctor_get(v_s_1086_, 1);
                v_exprToRingId_1089_ = crate::leanh::lean_ctor_get(v_s_1086_, 2);
                v_semirings_1090_ = crate::leanh::lean_ctor_get(v_s_1086_, 3);
                v_stypeIdOf_1091_ = crate::leanh::lean_ctor_get(v_s_1086_, 4);
                v_exprToSemiringId_1092_ = crate::leanh::lean_ctor_get(v_s_1086_, 5);
                v_ncRings_1093_ = crate::leanh::lean_ctor_get(v_s_1086_, 6);
                v_exprToNCRingId_1094_ = crate::leanh::lean_ctor_get(v_s_1086_, 7);
                v_nctypeIdOf_1095_ = crate::leanh::lean_ctor_get(v_s_1086_, 8);
                v_ncSemirings_1096_ = crate::leanh::lean_ctor_get(v_s_1086_, 9);
                v_exprToNCSemiringId_1097_ = crate::leanh::lean_ctor_get(v_s_1086_, 10);
                v_ncstypeIdOf_1098_ = crate::leanh::lean_ctor_get(v_s_1086_, 11);
                v_steps_1099_ = crate::leanh::lean_ctor_get(v_s_1086_, 12);
                v_reportedMaxDegreeIssue_1100_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1086_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v___x_1101_ = lean_array_get_size(v_ncRings_1093_);
                v___x_1102_ = lean_nat_dec_lt(v_a_1084_, v___x_1101_);
                if v___x_1102_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_1085_);
                    return v_s_1086_;
                } else {
                    crate::leanh::lean_inc(v_steps_1099_);
                    crate::leanh::lean_inc_ref(v_ncstypeIdOf_1098_);
                    crate::leanh::lean_inc_ref(v_exprToNCSemiringId_1097_);
                    crate::leanh::lean_inc_ref(v_ncSemirings_1096_);
                    crate::leanh::lean_inc_ref(v_nctypeIdOf_1095_);
                    crate::leanh::lean_inc_ref(v_exprToNCRingId_1094_);
                    crate::leanh::lean_inc_ref(v_ncRings_1093_);
                    crate::leanh::lean_inc_ref(v_exprToSemiringId_1092_);
                    crate::leanh::lean_inc_ref(v_stypeIdOf_1091_);
                    crate::leanh::lean_inc_ref(v_semirings_1090_);
                    crate::leanh::lean_inc_ref(v_exprToRingId_1089_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_1088_);
                    crate::leanh::lean_inc_ref(v_rings_1087_);
                    v_isSharedCheck_1114_ = (!crate::leanh::lean_is_exclusive(v_s_1086_)) as u8;
                    if v_isSharedCheck_1114_ == 0 {
                        v_unused_1115_ = crate::leanh::lean_ctor_get(v_s_1086_, 12);
                        crate::leanh::lean_dec(v_unused_1115_);
                        v_unused_1116_ = crate::leanh::lean_ctor_get(v_s_1086_, 11);
                        crate::leanh::lean_dec(v_unused_1116_);
                        v_unused_1117_ = crate::leanh::lean_ctor_get(v_s_1086_, 10);
                        crate::leanh::lean_dec(v_unused_1117_);
                        v_unused_1118_ = crate::leanh::lean_ctor_get(v_s_1086_, 9);
                        crate::leanh::lean_dec(v_unused_1118_);
                        v_unused_1119_ = crate::leanh::lean_ctor_get(v_s_1086_, 8);
                        crate::leanh::lean_dec(v_unused_1119_);
                        v_unused_1120_ = crate::leanh::lean_ctor_get(v_s_1086_, 7);
                        crate::leanh::lean_dec(v_unused_1120_);
                        v_unused_1121_ = crate::leanh::lean_ctor_get(v_s_1086_, 6);
                        crate::leanh::lean_dec(v_unused_1121_);
                        v_unused_1122_ = crate::leanh::lean_ctor_get(v_s_1086_, 5);
                        crate::leanh::lean_dec(v_unused_1122_);
                        v_unused_1123_ = crate::leanh::lean_ctor_get(v_s_1086_, 4);
                        crate::leanh::lean_dec(v_unused_1123_);
                        v_unused_1124_ = crate::leanh::lean_ctor_get(v_s_1086_, 3);
                        crate::leanh::lean_dec(v_unused_1124_);
                        v_unused_1125_ = crate::leanh::lean_ctor_get(v_s_1086_, 2);
                        crate::leanh::lean_dec(v_unused_1125_);
                        v_unused_1126_ = crate::leanh::lean_ctor_get(v_s_1086_, 1);
                        crate::leanh::lean_dec(v_unused_1126_);
                        v_unused_1127_ = crate::leanh::lean_ctor_get(v_s_1086_, 0);
                        crate::leanh::lean_dec(v_unused_1127_);
                        v___x_1104_ = v_s_1086_;
                        v_isShared_1105_ = v_isSharedCheck_1114_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_1086_);
                        v___x_1104_ = crate::leanh::lean_box(0);
                        v_isShared_1105_ = v_isSharedCheck_1114_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1106_ = lean_array_fget(v_ncRings_1093_, v_a_1084_);
                v___x_1107_ = crate::leanh::lean_box(0);
                v_xs_x27_1108_ = lean_array_fset(v_ncRings_1093_, v_a_1084_, v___x_1107_);
                v___x_1109_ = crate::leanh::lean_apply_1(v_f_1085_, v_v_1106_);
                v___x_1110_ = lean_array_fset(v_xs_x27_1108_, v_a_1084_, v___x_1109_);
                if v_isShared_1105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1104_, 6, v___x_1110_);
                    v___x_1112_ = v___x_1104_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1113_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 0, v_rings_1087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 1, v_typeIdOf_1088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 2, v_exprToRingId_1089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 3, v_semirings_1090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 4, v_stypeIdOf_1091_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1113_,
                        5,
                        v_exprToSemiringId_1092_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 6, v___x_1110_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 7, v_exprToNCRingId_1094_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 8, v_nctypeIdOf_1095_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 9, v_ncSemirings_1096_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1113_,
                        10,
                        v_exprToNCSemiringId_1097_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 11, v_ncstypeIdOf_1098_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1113_, 12, v_steps_1099_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1113_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_1100_,
                    );
                    v___x_1112_ = v_reuseFailAlloc_1113_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1112_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed(
    mut v_a_1128_: *mut crate::leanh::LeanObject,
    mut v_f_1129_: *mut crate::leanh::LeanObject,
    mut v_s_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0(
        v_a_1128_, v_f_1129_, v_s_1130_,
    );
    crate::leanh::lean_dec(v_a_1128_);
    return v_res_1131_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(
    mut v_f_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_1133_);
    v___f_1136_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1136_, 0, v_a_1133_);
    crate::leanh::lean_closure_set(v___f_1136_, 1, v_f_1132_);
    v___x_1137_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
    v___x_1138_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1137_, v___f_1136_, v_a_1134_);
    return v___x_1138_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg___boxed(
    mut v_f_1139_: *mut crate::leanh::LeanObject,
    mut v_a_1140_: *mut crate::leanh::LeanObject,
    mut v_a_1141_: *mut crate::leanh::LeanObject,
    mut v_a_1142_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1143_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(
        v_f_1139_, v_a_1140_, v_a_1141_,
    );
    crate::leanh::lean_dec(v_a_1141_);
    crate::leanh::lean_dec(v_a_1140_);
    return v_res_1143_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(
    mut v_f_1144_: *mut crate::leanh::LeanObject,
    mut v_a_1145_: *mut crate::leanh::LeanObject,
    mut v_a_1146_: *mut crate::leanh::LeanObject,
    mut v_a_1147_: *mut crate::leanh::LeanObject,
    mut v_a_1148_: *mut crate::leanh::LeanObject,
    mut v_a_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
    mut v_a_1154_: *mut crate::leanh::LeanObject,
    mut v_a_1155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1157_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___redArg(
        v_f_1144_, v_a_1145_, v_a_1146_,
    );
    return v___x_1157_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing___boxed(
    mut v_f_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
    mut v_a_1164_: *mut crate::leanh::LeanObject,
    mut v_a_1165_: *mut crate::leanh::LeanObject,
    mut v_a_1166_: *mut crate::leanh::LeanObject,
    mut v_a_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1171_ = l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_modifyRing(
        v_f_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_, v_a_1163_, v_a_1164_, v_a_1165_,
        v_a_1166_, v_a_1167_, v_a_1168_, v_a_1169_,
    );
    crate::leanh::lean_dec(v_a_1169_);
    crate::leanh::lean_dec_ref(v_a_1168_);
    crate::leanh::lean_dec(v_a_1167_);
    crate::leanh::lean_dec_ref(v_a_1166_);
    crate::leanh::lean_dec(v_a_1165_);
    crate::leanh::lean_dec_ref(v_a_1164_);
    crate::leanh::lean_dec(v_a_1163_);
    crate::leanh::lean_dec_ref(v_a_1162_);
    crate::leanh::lean_dec(v_a_1161_);
    crate::leanh::lean_dec(v_a_1160_);
    crate::leanh::lean_dec(v_a_1159_);
    return v_res_1171_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1173_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__0;
    v___x_1174_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_CommRing_NonCommRingM_getRing___boxed as *mut core::ffi::c_void,
        12,
        0,
    );
    v___x_1175_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1175_, 0, v___x_1174_);
    crate::leanh::lean_ctor_set(v___x_1175_, 1, v___x_1173_);
    return v___x_1175_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1176_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1_once
        ),
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM___closed__1,
    );
    return v___x_1176_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_1177_: *mut crate::leanh::LeanObject,
    mut v_vals_1178_: *mut crate::leanh::LeanObject,
    mut v_i_1179_: *mut crate::leanh::LeanObject,
    mut v_k_1180_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1182_: u8 = 0;
    let mut v___x_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: u8 = 0;
    let mut v___x_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1181_ = lean_array_get_size(v_keys_1177_);
                v___x_1182_ = lean_nat_dec_lt(v_i_1179_, v___x_1181_);
                if v___x_1182_ == 0 {
                    crate::leanh::lean_dec(v_i_1179_);
                    v___x_1183_ = crate::leanh::lean_box(0);
                    return v___x_1183_;
                } else {
                    v_k_x27_1184_ = lean_array_fget_borrowed(v_keys_1177_, v_i_1179_);
                    v___x_1185_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1180_,
                            v_k_x27_1184_,
                        );
                    if v___x_1185_ == 0 {
                        v___x_1186_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1187_ = lean_nat_add(v_i_1179_, v___x_1186_);
                        crate::leanh::lean_dec(v_i_1179_);
                        v_i_1179_ = v___x_1187_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1189_ = lean_array_fget_borrowed(v_vals_1178_, v_i_1179_);
                        crate::leanh::lean_dec(v_i_1179_);
                        crate::leanh::lean_inc(v___x_1189_);
                        v___x_1190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1190_, 0, v___x_1189_);
                        return v___x_1190_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_1191_: *mut crate::leanh::LeanObject,
    mut v_vals_1192_: *mut crate::leanh::LeanObject,
    mut v_i_1193_: *mut crate::leanh::LeanObject,
    mut v_k_1194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1195_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1191_, v_vals_1192_, v_i_1193_, v_k_1194_);
    crate::leanh::lean_dec_ref(v_k_1194_);
    crate::leanh::lean_dec_ref(v_vals_1192_);
    crate::leanh::lean_dec_ref(v_keys_1191_);
    return v_res_1195_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_1196_: usize = 0;
    let mut v___x_1197_: usize = 0;
    let mut v___x_1198_: usize = 0;
    v___x_1196_ = 5usize;
    v___x_1197_ = 1usize;
    v___x_1198_ = lean_usize_shift_left(v___x_1197_, v___x_1196_);
    return v___x_1198_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_1199_: usize = 0;
    let mut v___x_1200_: usize = 0;
    let mut v___x_1201_: usize = 0;
    v___x_1199_ = 1usize;
    v___x_1200_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_1201_ = lean_usize_sub(v___x_1200_, v___x_1199_);
    return v___x_1201_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(
    mut v_x_1202_: *mut crate::leanh::LeanObject,
    mut v_x_1203_: usize,
    mut v_x_1204_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1207_: usize = 0;
    let mut v___x_1208_: usize = 0;
    let mut v___x_1209_: usize = 0;
    let mut v_j_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1214_: u8 = 0;
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: usize = 0;
    let mut v___x_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1202_) == 0 {
                    v_es_1205_ = crate::leanh::lean_ctor_get(v_x_1202_, 0);
                    v___x_1206_ = crate::leanh::lean_box(2);
                    v___x_1207_ = 5usize;
                    v___x_1208_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1209_ = lean_usize_land(v_x_1203_, v___x_1208_);
                    v_j_1210_ = lean_usize_to_nat(v___x_1209_);
                    v___x_1211_ = lean_array_get_borrowed(v___x_1206_, v_es_1205_, v_j_1210_);
                    crate::leanh::lean_dec(v_j_1210_);
                    match crate::leanh::lean_obj_tag(v___x_1211_) {
                        0 => {
                            v_key_1212_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                            v_val_1213_ = crate::leanh::lean_ctor_get(v___x_1211_, 1);
                            v___x_1214_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1204_, v_key_1212_);
                            if v___x_1214_ == 0 {
                                v___x_1215_ = crate::leanh::lean_box(0);
                                return v___x_1215_;
                            } else {
                                crate::leanh::lean_inc(v_val_1213_);
                                v___x_1216_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1216_, 0, v_val_1213_);
                                return v___x_1216_;
                            }
                        }
                        1 => {
                            v_node_1217_ = crate::leanh::lean_ctor_get(v___x_1211_, 0);
                            v___x_1218_ = lean_usize_shift_right(v_x_1203_, v___x_1207_);
                            v_x_1202_ = v_node_1217_;
                            v_x_1203_ = v___x_1218_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1220_ = crate::leanh::lean_box(0);
                            return v___x_1220_;
                        }
                    }
                } else {
                    v_ks_1221_ = crate::leanh::lean_ctor_get(v_x_1202_, 0);
                    v_vs_1222_ = crate::leanh::lean_ctor_get(v_x_1202_, 1);
                    v___x_1223_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1224_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_1221_, v_vs_1222_, v___x_1223_, v_x_1204_);
                    return v___x_1224_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_x_1227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_867__boxed_1228_: usize = 0;
    let mut v_res_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_1228_ = crate::leanh::lean_unbox_usize(v_x_1226_);
    crate::leanh::lean_dec(v_x_1226_);
    v_res_1229_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_1225_, v_x_867__boxed_1228_, v_x_1227_);
    crate::leanh::lean_dec_ref(v_x_1227_);
    crate::leanh::lean_dec_ref(v_x_1225_);
    return v_res_1229_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(
    mut v_x_1230_: *mut crate::leanh::LeanObject,
    mut v_x_1231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1232_: u64 = 0;
    let mut v___x_1233_: usize = 0;
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1232_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1231_);
    v___x_1233_ = lean_uint64_to_usize(v___x_1232_);
    v___x_1234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_1230_, v___x_1233_, v_x_1231_);
    return v___x_1234_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg___boxed(
    mut v_x_1235_: *mut crate::leanh::LeanObject,
    mut v_x_1236_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1237_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_1235_, v_x_1236_);
    crate::leanh::lean_dec_ref(v_x_1236_);
    crate::leanh::lean_dec_ref(v_x_1235_);
    return v_res_1237_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(
    mut v_e_1238_: *mut crate::leanh::LeanObject,
    mut v_a_1239_: *mut crate::leanh::LeanObject,
    mut v_a_1240_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1246_: u8 = 0;
    let mut v_exprToNCRingId_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1252_: u8 = 0;
    let mut v_a_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1256_: u8 = 0;
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1260_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1242_ =
                    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_1239_, v_a_1240_);
                if crate::leanh::lean_obj_tag(v___x_1242_) == 0 {
                    v_a_1243_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1252_ = (!crate::leanh::lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1252_ == 0 {
                        v___x_1245_ = v___x_1242_;
                        v_isShared_1246_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1243_);
                        crate::leanh::lean_dec(v___x_1242_);
                        v___x_1245_ = crate::leanh::lean_box(0);
                        v_isShared_1246_ = v_isSharedCheck_1252_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_1253_ = crate::leanh::lean_ctor_get(v___x_1242_, 0);
                    v_isSharedCheck_1260_ = (!crate::leanh::lean_is_exclusive(v___x_1242_)) as u8;
                    if v_isSharedCheck_1260_ == 0 {
                        v___x_1255_ = v___x_1242_;
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1253_);
                        crate::leanh::lean_dec(v___x_1242_);
                        v___x_1255_ = crate::leanh::lean_box(0);
                        v_isShared_1256_ = v_isSharedCheck_1260_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToNCRingId_1247_ = crate::leanh::lean_ctor_get(v_a_1243_, 7);
                crate::leanh::lean_inc_ref(v_exprToNCRingId_1247_);
                crate::leanh::lean_dec(v_a_1243_);
                v___x_1248_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_exprToNCRingId_1247_, v_e_1238_);
                crate::leanh::lean_dec_ref(v_exprToNCRingId_1247_);
                if v_isShared_1246_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1245_, 0, v___x_1248_);
                    v___x_1250_ = v___x_1245_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1251_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1251_, 0, v___x_1248_);
                    v___x_1250_ = v_reuseFailAlloc_1251_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1250_;
            }
            3 => {
                if v_isShared_1256_ == 0 {
                    v___x_1258_ = v___x_1255_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1259_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1259_, 0, v_a_1253_);
                    v___x_1258_ = v_reuseFailAlloc_1259_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg___boxed(
    mut v_e_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
    mut v_a_1264_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1265_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(
        v_e_1261_, v_a_1262_, v_a_1263_,
    );
    crate::leanh::lean_dec_ref(v_a_1263_);
    crate::leanh::lean_dec(v_a_1262_);
    crate::leanh::lean_dec_ref(v_e_1261_);
    return v_res_1265_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(
    mut v_e_1266_: *mut crate::leanh::LeanObject,
    mut v_a_1267_: *mut crate::leanh::LeanObject,
    mut v_a_1268_: *mut crate::leanh::LeanObject,
    mut v_a_1269_: *mut crate::leanh::LeanObject,
    mut v_a_1270_: *mut crate::leanh::LeanObject,
    mut v_a_1271_: *mut crate::leanh::LeanObject,
    mut v_a_1272_: *mut crate::leanh::LeanObject,
    mut v_a_1273_: *mut crate::leanh::LeanObject,
    mut v_a_1274_: *mut crate::leanh::LeanObject,
    mut v_a_1275_: *mut crate::leanh::LeanObject,
    mut v_a_1276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1278_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(
        v_e_1266_, v_a_1267_, v_a_1275_,
    );
    return v___x_1278_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___boxed(
    mut v_e_1279_: *mut crate::leanh::LeanObject,
    mut v_a_1280_: *mut crate::leanh::LeanObject,
    mut v_a_1281_: *mut crate::leanh::LeanObject,
    mut v_a_1282_: *mut crate::leanh::LeanObject,
    mut v_a_1283_: *mut crate::leanh::LeanObject,
    mut v_a_1284_: *mut crate::leanh::LeanObject,
    mut v_a_1285_: *mut crate::leanh::LeanObject,
    mut v_a_1286_: *mut crate::leanh::LeanObject,
    mut v_a_1287_: *mut crate::leanh::LeanObject,
    mut v_a_1288_: *mut crate::leanh::LeanObject,
    mut v_a_1289_: *mut crate::leanh::LeanObject,
    mut v_a_1290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f(
        v_e_1279_, v_a_1280_, v_a_1281_, v_a_1282_, v_a_1283_, v_a_1284_, v_a_1285_, v_a_1286_,
        v_a_1287_, v_a_1288_, v_a_1289_,
    );
    crate::leanh::lean_dec(v_a_1289_);
    crate::leanh::lean_dec_ref(v_a_1288_);
    crate::leanh::lean_dec(v_a_1287_);
    crate::leanh::lean_dec_ref(v_a_1286_);
    crate::leanh::lean_dec(v_a_1285_);
    crate::leanh::lean_dec_ref(v_a_1284_);
    crate::leanh::lean_dec(v_a_1283_);
    crate::leanh::lean_dec_ref(v_a_1282_);
    crate::leanh::lean_dec(v_a_1281_);
    crate::leanh::lean_dec(v_a_1280_);
    crate::leanh::lean_dec_ref(v_e_1279_);
    return v_res_1291_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(
    mut v_00_u03b2_1292_: *mut crate::leanh::LeanObject,
    mut v_x_1293_: *mut crate::leanh::LeanObject,
    mut v_x_1294_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1295_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___redArg(v_x_1293_, v_x_1294_);
    return v___x_1295_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0___boxed(
    mut v_00_u03b2_1296_: *mut crate::leanh::LeanObject,
    mut v_x_1297_: *mut crate::leanh::LeanObject,
    mut v_x_1298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1299_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0(v_00_u03b2_1296_, v_x_1297_, v_x_1298_);
    crate::leanh::lean_dec_ref(v_x_1298_);
    crate::leanh::lean_dec_ref(v_x_1297_);
    return v_res_1299_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(
    mut v_00_u03b2_1300_: *mut crate::leanh::LeanObject,
    mut v_x_1301_: *mut crate::leanh::LeanObject,
    mut v_x_1302_: usize,
    mut v_x_1303_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1304_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg(v_x_1301_, v_x_1302_, v_x_1303_);
    return v___x_1304_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_1305_: *mut crate::leanh::LeanObject,
    mut v_x_1306_: *mut crate::leanh::LeanObject,
    mut v_x_1307_: *mut crate::leanh::LeanObject,
    mut v_x_1308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_984__boxed_1309_: usize = 0;
    let mut v_res_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_1309_ = crate::leanh::lean_unbox_usize(v_x_1307_);
    crate::leanh::lean_dec(v_x_1307_);
    v_res_1310_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0(v_00_u03b2_1305_, v_x_1306_, v_x_984__boxed_1309_, v_x_1308_);
    crate::leanh::lean_dec_ref(v_x_1308_);
    crate::leanh::lean_dec_ref(v_x_1306_);
    return v_res_1310_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1311_: *mut crate::leanh::LeanObject,
    mut v_keys_1312_: *mut crate::leanh::LeanObject,
    mut v_vals_1313_: *mut crate::leanh::LeanObject,
    mut v_heq_1314_: *mut crate::leanh::LeanObject,
    mut v_i_1315_: *mut crate::leanh::LeanObject,
    mut v_k_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1317_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_1312_, v_vals_1313_, v_i_1315_, v_k_1316_);
    return v___x_1317_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_1318_: *mut crate::leanh::LeanObject,
    mut v_keys_1319_: *mut crate::leanh::LeanObject,
    mut v_vals_1320_: *mut crate::leanh::LeanObject,
    mut v_heq_1321_: *mut crate::leanh::LeanObject,
    mut v_i_1322_: *mut crate::leanh::LeanObject,
    mut v_k_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1324_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_1318_, v_keys_1319_, v_vals_1320_, v_heq_1321_, v_i_1322_, v_k_1323_);
    crate::leanh::lean_dec_ref(v_k_1323_);
    crate::leanh::lean_dec_ref(v_vals_1320_);
    crate::leanh::lean_dec_ref(v_keys_1319_);
    return v_res_1324_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_1325_: *mut crate::leanh::LeanObject,
    mut v_x_1326_: *mut crate::leanh::LeanObject,
    mut v_x_1327_: *mut crate::leanh::LeanObject,
    mut v_x_1328_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1333_: u8 = 0;
    let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1342_: u8 = 0;
    let mut v___x_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1354_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1329_ = crate::leanh::lean_ctor_get(v_x_1325_, 0);
                v_vs_1330_ = crate::leanh::lean_ctor_get(v_x_1325_, 1);
                v_isSharedCheck_1354_ = (!crate::leanh::lean_is_exclusive(v_x_1325_)) as u8;
                if v_isSharedCheck_1354_ == 0 {
                    v___x_1332_ = v_x_1325_;
                    v_isShared_1333_ = v_isSharedCheck_1354_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_1330_);
                    crate::leanh::lean_inc(v_ks_1329_);
                    crate::leanh::lean_dec(v_x_1325_);
                    v___x_1332_ = crate::leanh::lean_box(0);
                    v_isShared_1333_ = v_isSharedCheck_1354_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1334_ = lean_array_get_size(v_ks_1329_);
                v___x_1335_ = lean_nat_dec_lt(v_x_1326_, v___x_1334_);
                if v___x_1335_ == 0 {
                    crate::leanh::lean_dec(v_x_1326_);
                    v___x_1336_ = lean_array_push(v_ks_1329_, v_x_1327_);
                    v___x_1337_ = lean_array_push(v_vs_1330_, v_x_1328_);
                    if v_isShared_1333_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1332_, 1, v___x_1337_);
                        crate::leanh::lean_ctor_set(v___x_1332_, 0, v___x_1336_);
                        v___x_1339_ = v___x_1332_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1340_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 0, v___x_1336_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1340_, 1, v___x_1337_);
                        v___x_1339_ = v_reuseFailAlloc_1340_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1341_ = lean_array_fget_borrowed(v_ks_1329_, v_x_1326_);
                    v___x_1342_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_1327_,
                            v_k_x27_1341_,
                        );
                    if v___x_1342_ == 0 {
                        if v_isShared_1333_ == 0 {
                            v___x_1344_ = v___x_1332_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1348_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 0, v_ks_1329_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1348_, 1, v_vs_1330_);
                            v___x_1344_ = v_reuseFailAlloc_1348_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1349_ = lean_array_fset(v_ks_1329_, v_x_1326_, v_x_1327_);
                        v___x_1350_ = lean_array_fset(v_vs_1330_, v_x_1326_, v_x_1328_);
                        crate::leanh::lean_dec(v_x_1326_);
                        if v_isShared_1333_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_1332_, 1, v___x_1350_);
                            crate::leanh::lean_ctor_set(v___x_1332_, 0, v___x_1349_);
                            v___x_1352_ = v___x_1332_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1353_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1349_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_1353_, 1, v___x_1350_);
                            v___x_1352_ = v_reuseFailAlloc_1353_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1339_;
            }
            3 => {
                v___x_1345_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1346_ = lean_nat_add(v_x_1326_, v___x_1345_);
                crate::leanh::lean_dec(v_x_1326_);
                v_x_1325_ = v___x_1344_;
                v_x_1326_ = v___x_1346_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1352_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(
    mut v_n_1355_: *mut crate::leanh::LeanObject,
    mut v_k_1356_: *mut crate::leanh::LeanObject,
    mut v_v_1357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1358_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1359_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_1355_, v___x_1358_, v_k_1356_, v_v_1357_);
    return v___x_1359_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1360_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1360_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(
    mut v_x_1361_: *mut crate::leanh::LeanObject,
    mut v_x_1362_: usize,
    mut v_x_1363_: usize,
    mut v_x_1364_: *mut crate::leanh::LeanObject,
    mut v_x_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: usize = 0;
    let mut v___x_1368_: usize = 0;
    let mut v___x_1369_: usize = 0;
    let mut v___x_1370_: usize = 0;
    let mut v_j_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1373_: u8 = 0;
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1376_: u8 = 0;
    let mut v_v_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1390_: u8 = 0;
    let mut v___x_1391_: u8 = 0;
    let mut v___x_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1397_: u8 = 0;
    let mut v_node_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1401_: u8 = 0;
    let mut v___x_1402_: usize = 0;
    let mut v___x_1403_: usize = 0;
    let mut v___x_1404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1408_: u8 = 0;
    let mut v___x_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1410_: u8 = 0;
    let mut v_unused_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1416_: u8 = 0;
    let mut v___x_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1421_: u8 = 0;
    let mut v_ks_1422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1427_: usize = 0;
    let mut v___x_1428_: u8 = 0;
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1431_: u8 = 0;
    let mut v_reuseFailAlloc_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1433_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1361_) == 0 {
                    v_es_1366_ = crate::leanh::lean_ctor_get(v_x_1361_, 0);
                    v___x_1367_ = 5usize;
                    v___x_1368_ = 1usize;
                    v___x_1369_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_1370_ = lean_usize_land(v_x_1362_, v___x_1369_);
                    v_j_1371_ = lean_usize_to_nat(v___x_1370_);
                    v___x_1372_ = lean_array_get_size(v_es_1366_);
                    v___x_1373_ = lean_nat_dec_lt(v_j_1371_, v___x_1372_);
                    if v___x_1373_ == 0 {
                        crate::leanh::lean_dec(v_j_1371_);
                        crate::leanh::lean_dec(v_x_1365_);
                        crate::leanh::lean_dec_ref(v_x_1364_);
                        return v_x_1361_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_1366_);
                        v_isSharedCheck_1410_ = (!crate::leanh::lean_is_exclusive(v_x_1361_)) as u8;
                        if v_isSharedCheck_1410_ == 0 {
                            v_unused_1411_ = crate::leanh::lean_ctor_get(v_x_1361_, 0);
                            crate::leanh::lean_dec(v_unused_1411_);
                            v___x_1375_ = v_x_1361_;
                            v_isShared_1376_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_1361_);
                            v___x_1375_ = crate::leanh::lean_box(0);
                            v_isShared_1376_ = v_isSharedCheck_1410_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1412_ = crate::leanh::lean_ctor_get(v_x_1361_, 0);
                    v_vs_1413_ = crate::leanh::lean_ctor_get(v_x_1361_, 1);
                    v_isSharedCheck_1433_ = (!crate::leanh::lean_is_exclusive(v_x_1361_)) as u8;
                    if v_isSharedCheck_1433_ == 0 {
                        v___x_1415_ = v_x_1361_;
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_1413_);
                        crate::leanh::lean_inc(v_ks_1412_);
                        crate::leanh::lean_dec(v_x_1361_);
                        v___x_1415_ = crate::leanh::lean_box(0);
                        v_isShared_1416_ = v_isSharedCheck_1433_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1377_ = lean_array_fget(v_es_1366_, v_j_1371_);
                v___x_1378_ = crate::leanh::lean_box(0);
                v_xs_x27_1379_ = lean_array_fset(v_es_1366_, v_j_1371_, v___x_1378_);
                match crate::leanh::lean_obj_tag(v_v_1377_) {
                    0 => {
                        v_key_1386_ = crate::leanh::lean_ctor_get(v_v_1377_, 0);
                        v_val_1387_ = crate::leanh::lean_ctor_get(v_v_1377_, 1);
                        v_isSharedCheck_1397_ = (!crate::leanh::lean_is_exclusive(v_v_1377_)) as u8;
                        if v_isSharedCheck_1397_ == 0 {
                            v___x_1389_ = v_v_1377_;
                            v_isShared_1390_ = v_isSharedCheck_1397_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1387_);
                            crate::leanh::lean_inc(v_key_1386_);
                            crate::leanh::lean_dec(v_v_1377_);
                            v___x_1389_ = crate::leanh::lean_box(0);
                            v_isShared_1390_ = v_isSharedCheck_1397_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1398_ = crate::leanh::lean_ctor_get(v_v_1377_, 0);
                        v_isSharedCheck_1408_ = (!crate::leanh::lean_is_exclusive(v_v_1377_)) as u8;
                        if v_isSharedCheck_1408_ == 0 {
                            v___x_1400_ = v_v_1377_;
                            v_isShared_1401_ = v_isSharedCheck_1408_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1398_);
                            crate::leanh::lean_dec(v_v_1377_);
                            v___x_1400_ = crate::leanh::lean_box(0);
                            v_isShared_1401_ = v_isSharedCheck_1408_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1409_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1409_, 0, v_x_1364_);
                        crate::leanh::lean_ctor_set(v___x_1409_, 1, v_x_1365_);
                        v___y_1381_ = v___x_1409_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1382_ = lean_array_fset(v_xs_x27_1379_, v_j_1371_, v___y_1381_);
                crate::leanh::lean_dec(v_j_1371_);
                if v_isShared_1376_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1382_);
                    v___x_1384_ = v___x_1375_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1385_, 0, v___x_1382_);
                    v___x_1384_ = v_reuseFailAlloc_1385_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1384_;
            }
            4 => {
                v___x_1391_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_1364_,
                        v_key_1386_,
                    );
                if v___x_1391_ == 0 {
                    crate::leanh::lean_del_object(v___x_1389_);
                    v___x_1392_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1386_,
                        v_val_1387_,
                        v_x_1364_,
                        v_x_1365_,
                    );
                    v___x_1393_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1393_, 0, v___x_1392_);
                    v___y_1381_ = v___x_1393_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_1387_);
                    crate::leanh::lean_dec(v_key_1386_);
                    if v_isShared_1390_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1389_, 1, v_x_1365_);
                        crate::leanh::lean_ctor_set(v___x_1389_, 0, v_x_1364_);
                        v___x_1395_ = v___x_1389_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1396_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 0, v_x_1364_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1396_, 1, v_x_1365_);
                        v___x_1395_ = v_reuseFailAlloc_1396_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1381_ = v___x_1395_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1402_ = lean_usize_shift_right(v_x_1362_, v___x_1367_);
                v___x_1403_ = lean_usize_add(v_x_1363_, v___x_1368_);
                v___x_1404_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_node_1398_, v___x_1402_, v___x_1403_, v_x_1364_, v_x_1365_);
                if v_isShared_1401_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1400_, 0, v___x_1404_);
                    v___x_1406_ = v___x_1400_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1407_, 0, v___x_1404_);
                    v___x_1406_ = v_reuseFailAlloc_1407_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1381_ = v___x_1406_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1416_ == 0 {
                    v___x_1418_ = v___x_1415_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1432_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 0, v_ks_1412_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1432_, 1, v_vs_1413_);
                    v___x_1418_ = v_reuseFailAlloc_1432_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1419_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v___x_1418_, v_x_1364_, v_x_1365_);
                v___x_1427_ = 7usize;
                v___x_1428_ = lean_usize_dec_le(v___x_1427_, v_x_1363_);
                if v___x_1428_ == 0 {
                    v___x_1429_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1419_);
                    v___x_1430_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_1431_ = lean_nat_dec_lt(v___x_1429_, v___x_1430_);
                    crate::leanh::lean_dec(v___x_1429_);
                    v___y_1421_ = v___x_1431_;
                    state = 10;
                    continue;
                } else {
                    v___y_1421_ = v___x_1428_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1421_ == 0 {
                    v_ks_1422_ = crate::leanh::lean_ctor_get(v_newNode_1419_, 0);
                    crate::leanh::lean_inc_ref(v_ks_1422_);
                    v_vs_1423_ = crate::leanh::lean_ctor_get(v_newNode_1419_, 1);
                    crate::leanh::lean_inc_ref(v_vs_1423_);
                    crate::leanh::lean_dec_ref(v_newNode_1419_);
                    v___x_1424_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1425_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___closed__0);
                    v___x_1426_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_x_1363_, v_ks_1422_, v_vs_1423_, v___x_1424_, v___x_1425_);
                    crate::leanh::lean_dec_ref(v_vs_1423_);
                    crate::leanh::lean_dec_ref(v_ks_1422_);
                    return v___x_1426_;
                } else {
                    return v_newNode_1419_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_1434_: usize,
    mut v_keys_1435_: *mut crate::leanh::LeanObject,
    mut v_vals_1436_: *mut crate::leanh::LeanObject,
    mut v_i_1437_: *mut crate::leanh::LeanObject,
    mut v_entries_1438_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1440_: u8 = 0;
    let mut v_k_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1443_: u64 = 0;
    let mut v_h_1444_: usize = 0;
    let mut v___x_1445_: usize = 0;
    let mut v___x_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1447_: usize = 0;
    let mut v___x_1448_: usize = 0;
    let mut v___x_1449_: usize = 0;
    let mut v_h_1450_: usize = 0;
    let mut v___x_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1439_ = lean_array_get_size(v_keys_1435_);
                v___x_1440_ = lean_nat_dec_lt(v_i_1437_, v___x_1439_);
                if v___x_1440_ == 0 {
                    crate::leanh::lean_dec(v_i_1437_);
                    return v_entries_1438_;
                } else {
                    v_k_1441_ = lean_array_fget_borrowed(v_keys_1435_, v_i_1437_);
                    v_v_1442_ = lean_array_fget_borrowed(v_vals_1436_, v_i_1437_);
                    v___x_1443_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_1441_);
                    v_h_1444_ = lean_uint64_to_usize(v___x_1443_);
                    v___x_1445_ = 5usize;
                    v___x_1446_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1447_ = 1usize;
                    v___x_1448_ = lean_usize_sub(v_depth_1434_, v___x_1447_);
                    v___x_1449_ = lean_usize_mul(v___x_1445_, v___x_1448_);
                    v_h_1450_ = lean_usize_shift_right(v_h_1444_, v___x_1449_);
                    v___x_1451_ = lean_nat_add(v_i_1437_, v___x_1446_);
                    crate::leanh::lean_dec(v_i_1437_);
                    crate::leanh::lean_inc(v_v_1442_);
                    crate::leanh::lean_inc(v_k_1441_);
                    v___x_1452_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_entries_1438_, v_h_1450_, v_depth_1434_, v_k_1441_, v_v_1442_);
                    v_i_1437_ = v___x_1451_;
                    v_entries_1438_ = v___x_1452_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_1454_: *mut crate::leanh::LeanObject,
    mut v_keys_1455_: *mut crate::leanh::LeanObject,
    mut v_vals_1456_: *mut crate::leanh::LeanObject,
    mut v_i_1457_: *mut crate::leanh::LeanObject,
    mut v_entries_1458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1459_: usize = 0;
    let mut v_res_1460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1459_ = crate::leanh::lean_unbox_usize(v_depth_1454_);
    crate::leanh::lean_dec(v_depth_1454_);
    v_res_1460_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1459_, v_keys_1455_, v_vals_1456_, v_i_1457_, v_entries_1458_);
    crate::leanh::lean_dec_ref(v_vals_1456_);
    crate::leanh::lean_dec_ref(v_keys_1455_);
    return v_res_1460_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg___boxed(
    mut v_x_1461_: *mut crate::leanh::LeanObject,
    mut v_x_1462_: *mut crate::leanh::LeanObject,
    mut v_x_1463_: *mut crate::leanh::LeanObject,
    mut v_x_1464_: *mut crate::leanh::LeanObject,
    mut v_x_1465_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8276__boxed_1466_: usize = 0;
    let mut v_x_8277__boxed_1467_: usize = 0;
    let mut v_res_1468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8276__boxed_1466_ = crate::leanh::lean_unbox_usize(v_x_1462_);
    crate::leanh::lean_dec(v_x_1462_);
    v_x_8277__boxed_1467_ = crate::leanh::lean_unbox_usize(v_x_1463_);
    crate::leanh::lean_dec(v_x_1463_);
    v_res_1468_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_1461_, v_x_8276__boxed_1466_, v_x_8277__boxed_1467_, v_x_1464_, v_x_1465_);
    return v_res_1468_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(
    mut v_x_1469_: *mut crate::leanh::LeanObject,
    mut v_x_1470_: *mut crate::leanh::LeanObject,
    mut v_x_1471_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1472_: u64 = 0;
    let mut v___x_1473_: usize = 0;
    let mut v___x_1474_: usize = 0;
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1472_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1470_);
    v___x_1473_ = lean_uint64_to_usize(v___x_1472_);
    v___x_1474_ = 1usize;
    v___x_1475_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_1469_, v___x_1473_, v___x_1474_, v_x_1470_, v_x_1471_);
    return v___x_1475_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(
    mut v_e_1476_: *mut crate::leanh::LeanObject,
    mut v_a_1477_: *mut crate::leanh::LeanObject,
    mut v_s_1478_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_rings_1479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToRingId_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_semirings_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stypeIdOf_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToSemiringId_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncRings_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCRingId_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nctypeIdOf_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncSemirings_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNCSemiringId_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ncstypeIdOf_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_steps_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reportedMaxDegreeIssue_1492_: u8 = 0;
    let mut v___x_1494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1495_: u8 = 0;
    let mut v___x_1496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_rings_1479_ = crate::leanh::lean_ctor_get(v_s_1478_, 0);
                v_typeIdOf_1480_ = crate::leanh::lean_ctor_get(v_s_1478_, 1);
                v_exprToRingId_1481_ = crate::leanh::lean_ctor_get(v_s_1478_, 2);
                v_semirings_1482_ = crate::leanh::lean_ctor_get(v_s_1478_, 3);
                v_stypeIdOf_1483_ = crate::leanh::lean_ctor_get(v_s_1478_, 4);
                v_exprToSemiringId_1484_ = crate::leanh::lean_ctor_get(v_s_1478_, 5);
                v_ncRings_1485_ = crate::leanh::lean_ctor_get(v_s_1478_, 6);
                v_exprToNCRingId_1486_ = crate::leanh::lean_ctor_get(v_s_1478_, 7);
                v_nctypeIdOf_1487_ = crate::leanh::lean_ctor_get(v_s_1478_, 8);
                v_ncSemirings_1488_ = crate::leanh::lean_ctor_get(v_s_1478_, 9);
                v_exprToNCSemiringId_1489_ = crate::leanh::lean_ctor_get(v_s_1478_, 10);
                v_ncstypeIdOf_1490_ = crate::leanh::lean_ctor_get(v_s_1478_, 11);
                v_steps_1491_ = crate::leanh::lean_ctor_get(v_s_1478_, 12);
                v_reportedMaxDegreeIssue_1492_ = crate::leanh::lean_ctor_get_uint8(
                    v_s_1478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                );
                v_isSharedCheck_1500_ = (!crate::leanh::lean_is_exclusive(v_s_1478_)) as u8;
                if v_isSharedCheck_1500_ == 0 {
                    v___x_1494_ = v_s_1478_;
                    v_isShared_1495_ = v_isSharedCheck_1500_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_steps_1491_);
                    crate::leanh::lean_inc(v_ncstypeIdOf_1490_);
                    crate::leanh::lean_inc(v_exprToNCSemiringId_1489_);
                    crate::leanh::lean_inc(v_ncSemirings_1488_);
                    crate::leanh::lean_inc(v_nctypeIdOf_1487_);
                    crate::leanh::lean_inc(v_exprToNCRingId_1486_);
                    crate::leanh::lean_inc(v_ncRings_1485_);
                    crate::leanh::lean_inc(v_exprToSemiringId_1484_);
                    crate::leanh::lean_inc(v_stypeIdOf_1483_);
                    crate::leanh::lean_inc(v_semirings_1482_);
                    crate::leanh::lean_inc(v_exprToRingId_1481_);
                    crate::leanh::lean_inc(v_typeIdOf_1480_);
                    crate::leanh::lean_inc(v_rings_1479_);
                    crate::leanh::lean_dec(v_s_1478_);
                    v___x_1494_ = crate::leanh::lean_box(0);
                    v_isShared_1495_ = v_isSharedCheck_1500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_1477_);
                v___x_1496_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_exprToNCRingId_1486_, v_e_1476_, v_a_1477_);
                if v_isShared_1495_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1494_, 7, v___x_1496_);
                    v___x_1498_ = v___x_1494_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1499_ = crate::leanh::lean_alloc_ctor(0, 13, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_rings_1479_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 1, v_typeIdOf_1480_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 2, v_exprToRingId_1481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 3, v_semirings_1482_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 4, v_stypeIdOf_1483_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1499_,
                        5,
                        v_exprToSemiringId_1484_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 6, v_ncRings_1485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 7, v___x_1496_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 8, v_nctypeIdOf_1487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 9, v_ncSemirings_1488_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1499_,
                        10,
                        v_exprToNCSemiringId_1489_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 11, v_ncstypeIdOf_1490_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1499_, 12, v_steps_1491_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1499_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 13) as u32,
                        v_reportedMaxDegreeIssue_1492_,
                    );
                    v___x_1498_ = v_reuseFailAlloc_1499_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1498_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed(
    mut v_e_1501_: *mut crate::leanh::LeanObject,
    mut v_a_1502_: *mut crate::leanh::LeanObject,
    mut v_s_1503_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1504_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0(
        v_e_1501_, v_a_1502_, v_s_1503_,
    );
    crate::leanh::lean_dec(v_a_1502_);
    return v_res_1504_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1506_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__0;
    v___x_1507_ = l_Lean_stringToMessageData(v___x_1506_);
    return v___x_1507_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(
    mut v_e_1508_: *mut crate::leanh::LeanObject,
    mut v_a_1509_: *mut crate::leanh::LeanObject,
    mut v_a_1510_: *mut crate::leanh::LeanObject,
    mut v_a_1511_: *mut crate::leanh::LeanObject,
    mut v_a_1512_: *mut crate::leanh::LeanObject,
    mut v_a_1513_: *mut crate::leanh::LeanObject,
    mut v_a_1514_: *mut crate::leanh::LeanObject,
    mut v_a_1515_: *mut crate::leanh::LeanObject,
    mut v_a_1516_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1524_: u8 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1535_: u8 = 0;
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1539_: u8 = 0;
    let mut v___f_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v___x_1548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1521_ = l_Lean_Meta_Grind_Arith_CommRing_getTermNonCommRingId_x3f___redArg(
                    v_e_1508_, v_a_1510_, v_a_1515_,
                );
                if crate::leanh::lean_obj_tag(v___x_1521_) == 0 {
                    v_a_1522_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                    crate::leanh::lean_inc(v_a_1522_);
                    crate::leanh::lean_dec_ref_known(v___x_1521_, 1);
                    if crate::leanh::lean_obj_tag(v_a_1522_) == 1 {
                        v_val_1523_ = crate::leanh::lean_ctor_get(v_a_1522_, 0);
                        crate::leanh::lean_inc(v_val_1523_);
                        crate::leanh::lean_dec_ref_known(v_a_1522_, 1);
                        v___x_1524_ = lean_nat_dec_eq(v_val_1523_, v_a_1509_);
                        crate::leanh::lean_dec(v_val_1523_);
                        if v___x_1524_ == 0 {
                            v___x_1525_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_1511_);
                            if crate::leanh::lean_obj_tag(v___x_1525_) == 0 {
                                v_a_1526_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                crate::leanh::lean_inc(v_a_1526_);
                                crate::leanh::lean_dec_ref_known(v___x_1525_, 1);
                                v___x_1527_ = (crate::leanh::lean_unbox(v_a_1526_) as u8);
                                crate::leanh::lean_dec(v_a_1526_);
                                if v___x_1527_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_1508_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_1528_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___closed__1);
                                    v___x_1529_ = l_Lean_indentExpr(v_e_1508_);
                                    v___x_1530_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1530_, 0, v___x_1528_);
                                    crate::leanh::lean_ctor_set(v___x_1530_, 1, v___x_1529_);
                                    v___x_1531_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_1530_,
                                        v_a_1511_,
                                        v_a_1512_,
                                        v_a_1513_,
                                        v_a_1514_,
                                        v_a_1515_,
                                        v_a_1516_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_1531_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1531_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_1531_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_1508_);
                                v_a_1532_ = crate::leanh::lean_ctor_get(v___x_1525_, 0);
                                v_isSharedCheck_1539_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1525_)) as u8;
                                if v_isSharedCheck_1539_ == 0 {
                                    v___x_1534_ = v___x_1525_;
                                    v_isShared_1535_ = v_isSharedCheck_1539_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1532_);
                                    crate::leanh::lean_dec(v___x_1525_);
                                    v___x_1534_ = crate::leanh::lean_box(0);
                                    v_isShared_1535_ = v_isSharedCheck_1539_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_1508_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1522_);
                        crate::leanh::lean_inc(v_a_1509_);
                        v___f_1540_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_1540_, 0, v_e_1508_);
                        crate::leanh::lean_closure_set(v___f_1540_, 1, v_a_1509_);
                        v___x_1541_ = l_Lean_Meta_Grind_Arith_CommRing_ringExt;
                        v___x_1542_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_1541_, v___f_1540_, v_a_1510_);
                        return v___x_1542_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_1508_);
                    v_a_1543_ = crate::leanh::lean_ctor_get(v___x_1521_, 0);
                    v_isSharedCheck_1550_ = (!crate::leanh::lean_is_exclusive(v___x_1521_)) as u8;
                    if v_isSharedCheck_1550_ == 0 {
                        v___x_1545_ = v___x_1521_;
                        v_isShared_1546_ = v_isSharedCheck_1550_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1543_);
                        crate::leanh::lean_dec(v___x_1521_);
                        v___x_1545_ = crate::leanh::lean_box(0);
                        v_isShared_1546_ = v_isSharedCheck_1550_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1519_ = crate::leanh::lean_box(0);
                v___x_1520_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1520_, 0, v___x_1519_);
                return v___x_1520_;
            }
            2 => {
                if v_isShared_1535_ == 0 {
                    v___x_1537_ = v___x_1534_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
                    v___x_1537_ = v_reuseFailAlloc_1538_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1537_;
            }
            4 => {
                if v_isShared_1546_ == 0 {
                    v___x_1548_ = v___x_1545_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1549_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1549_, 0, v_a_1543_);
                    v___x_1548_ = v_reuseFailAlloc_1549_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg___boxed(
    mut v_e_1551_: *mut crate::leanh::LeanObject,
    mut v_a_1552_: *mut crate::leanh::LeanObject,
    mut v_a_1553_: *mut crate::leanh::LeanObject,
    mut v_a_1554_: *mut crate::leanh::LeanObject,
    mut v_a_1555_: *mut crate::leanh::LeanObject,
    mut v_a_1556_: *mut crate::leanh::LeanObject,
    mut v_a_1557_: *mut crate::leanh::LeanObject,
    mut v_a_1558_: *mut crate::leanh::LeanObject,
    mut v_a_1559_: *mut crate::leanh::LeanObject,
    mut v_a_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(
        v_e_1551_, v_a_1552_, v_a_1553_, v_a_1554_, v_a_1555_, v_a_1556_, v_a_1557_, v_a_1558_,
        v_a_1559_,
    );
    crate::leanh::lean_dec(v_a_1559_);
    crate::leanh::lean_dec_ref(v_a_1558_);
    crate::leanh::lean_dec(v_a_1557_);
    crate::leanh::lean_dec_ref(v_a_1556_);
    crate::leanh::lean_dec(v_a_1555_);
    crate::leanh::lean_dec_ref(v_a_1554_);
    crate::leanh::lean_dec(v_a_1553_);
    crate::leanh::lean_dec(v_a_1552_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(
    mut v_e_1562_: *mut crate::leanh::LeanObject,
    mut v_a_1563_: *mut crate::leanh::LeanObject,
    mut v_a_1564_: *mut crate::leanh::LeanObject,
    mut v_a_1565_: *mut crate::leanh::LeanObject,
    mut v_a_1566_: *mut crate::leanh::LeanObject,
    mut v_a_1567_: *mut crate::leanh::LeanObject,
    mut v_a_1568_: *mut crate::leanh::LeanObject,
    mut v_a_1569_: *mut crate::leanh::LeanObject,
    mut v_a_1570_: *mut crate::leanh::LeanObject,
    mut v_a_1571_: *mut crate::leanh::LeanObject,
    mut v_a_1572_: *mut crate::leanh::LeanObject,
    mut v_a_1573_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1575_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(
        v_e_1562_, v_a_1563_, v_a_1564_, v_a_1568_, v_a_1569_, v_a_1570_, v_a_1571_, v_a_1572_,
        v_a_1573_,
    );
    return v___x_1575_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___boxed(
    mut v_e_1576_: *mut crate::leanh::LeanObject,
    mut v_a_1577_: *mut crate::leanh::LeanObject,
    mut v_a_1578_: *mut crate::leanh::LeanObject,
    mut v_a_1579_: *mut crate::leanh::LeanObject,
    mut v_a_1580_: *mut crate::leanh::LeanObject,
    mut v_a_1581_: *mut crate::leanh::LeanObject,
    mut v_a_1582_: *mut crate::leanh::LeanObject,
    mut v_a_1583_: *mut crate::leanh::LeanObject,
    mut v_a_1584_: *mut crate::leanh::LeanObject,
    mut v_a_1585_: *mut crate::leanh::LeanObject,
    mut v_a_1586_: *mut crate::leanh::LeanObject,
    mut v_a_1587_: *mut crate::leanh::LeanObject,
    mut v_a_1588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1589_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId(
        v_e_1576_, v_a_1577_, v_a_1578_, v_a_1579_, v_a_1580_, v_a_1581_, v_a_1582_, v_a_1583_,
        v_a_1584_, v_a_1585_, v_a_1586_, v_a_1587_,
    );
    crate::leanh::lean_dec(v_a_1587_);
    crate::leanh::lean_dec_ref(v_a_1586_);
    crate::leanh::lean_dec(v_a_1585_);
    crate::leanh::lean_dec_ref(v_a_1584_);
    crate::leanh::lean_dec(v_a_1583_);
    crate::leanh::lean_dec_ref(v_a_1582_);
    crate::leanh::lean_dec(v_a_1581_);
    crate::leanh::lean_dec_ref(v_a_1580_);
    crate::leanh::lean_dec(v_a_1579_);
    crate::leanh::lean_dec(v_a_1578_);
    crate::leanh::lean_dec(v_a_1577_);
    return v_res_1589_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0(
    mut v_00_u03b2_1590_: *mut crate::leanh::LeanObject,
    mut v_x_1591_: *mut crate::leanh::LeanObject,
    mut v_x_1592_: *mut crate::leanh::LeanObject,
    mut v_x_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1594_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0___redArg(v_x_1591_, v_x_1592_, v_x_1593_);
    return v___x_1594_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(
    mut v_00_u03b2_1595_: *mut crate::leanh::LeanObject,
    mut v_x_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: usize,
    mut v_x_1598_: usize,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
    mut v_x_1600_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1601_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___redArg(v_x_1596_, v_x_1597_, v_x_1598_, v_x_1599_, v_x_1600_);
    return v___x_1601_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0___boxed(
    mut v_00_u03b2_1602_: *mut crate::leanh::LeanObject,
    mut v_x_1603_: *mut crate::leanh::LeanObject,
    mut v_x_1604_: *mut crate::leanh::LeanObject,
    mut v_x_1605_: *mut crate::leanh::LeanObject,
    mut v_x_1606_: *mut crate::leanh::LeanObject,
    mut v_x_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_8555__boxed_1608_: usize = 0;
    let mut v_x_8556__boxed_1609_: usize = 0;
    let mut v_res_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_8555__boxed_1608_ = crate::leanh::lean_unbox_usize(v_x_1604_);
    crate::leanh::lean_dec(v_x_1604_);
    v_x_8556__boxed_1609_ = crate::leanh::lean_unbox_usize(v_x_1605_);
    crate::leanh::lean_dec(v_x_1605_);
    v_res_1610_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0(v_00_u03b2_1602_, v_x_1603_, v_x_8555__boxed_1608_, v_x_8556__boxed_1609_, v_x_1606_, v_x_1607_);
    return v_res_1610_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1611_: *mut crate::leanh::LeanObject,
    mut v_n_1612_: *mut crate::leanh::LeanObject,
    mut v_k_1613_: *mut crate::leanh::LeanObject,
    mut v_v_1614_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1615_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1___redArg(v_n_1612_, v_k_1613_, v_v_1614_);
    return v___x_1615_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1616_: *mut crate::leanh::LeanObject,
    mut v_depth_1617_: usize,
    mut v_keys_1618_: *mut crate::leanh::LeanObject,
    mut v_vals_1619_: *mut crate::leanh::LeanObject,
    mut v_heq_1620_: *mut crate::leanh::LeanObject,
    mut v_i_1621_: *mut crate::leanh::LeanObject,
    mut v_entries_1622_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1623_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___redArg(v_depth_1617_, v_keys_1618_, v_vals_1619_, v_i_1621_, v_entries_1622_);
    return v___x_1623_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1624_: *mut crate::leanh::LeanObject,
    mut v_depth_1625_: *mut crate::leanh::LeanObject,
    mut v_keys_1626_: *mut crate::leanh::LeanObject,
    mut v_vals_1627_: *mut crate::leanh::LeanObject,
    mut v_heq_1628_: *mut crate::leanh::LeanObject,
    mut v_i_1629_: *mut crate::leanh::LeanObject,
    mut v_entries_1630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1631_: usize = 0;
    let mut v_res_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1631_ = crate::leanh::lean_unbox_usize(v_depth_1625_);
    crate::leanh::lean_dec(v_depth_1625_);
    v_res_1632_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__2(v_00_u03b2_1624_, v_depth_boxed_1631_, v_keys_1626_, v_vals_1627_, v_heq_1628_, v_i_1629_, v_entries_1630_);
    crate::leanh::lean_dec_ref(v_vals_1627_);
    crate::leanh::lean_dec_ref(v_keys_1626_);
    return v_res_1632_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1633_: *mut crate::leanh::LeanObject,
    mut v_x_1634_: *mut crate::leanh::LeanObject,
    mut v_x_1635_: *mut crate::leanh::LeanObject,
    mut v_x_1636_: *mut crate::leanh::LeanObject,
    mut v_x_1637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1638_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1634_, v_x_1635_, v_x_1636_, v_x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(
    mut v_e_1639_: *mut crate::leanh::LeanObject,
    mut v___y_1640_: *mut crate::leanh::LeanObject,
    mut v___y_1641_: *mut crate::leanh::LeanObject,
    mut v___y_1642_: *mut crate::leanh::LeanObject,
    mut v___y_1643_: *mut crate::leanh::LeanObject,
    mut v___y_1644_: *mut crate::leanh::LeanObject,
    mut v___y_1645_: *mut crate::leanh::LeanObject,
    mut v___y_1646_: *mut crate::leanh::LeanObject,
    mut v___y_1647_: *mut crate::leanh::LeanObject,
    mut v___y_1648_: *mut crate::leanh::LeanObject,
    mut v___y_1649_: *mut crate::leanh::LeanObject,
    mut v___y_1650_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1652_ = l_Lean_Meta_Grind_Arith_CommRing_setTermNonCommRingId___redArg(
        v_e_1639_,
        v___y_1640_,
        v___y_1641_,
        v___y_1645_,
        v___y_1646_,
        v___y_1647_,
        v___y_1648_,
        v___y_1649_,
        v___y_1650_,
    );
    return v___x_1652_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0___boxed(
    mut v_e_1653_: *mut crate::leanh::LeanObject,
    mut v___y_1654_: *mut crate::leanh::LeanObject,
    mut v___y_1655_: *mut crate::leanh::LeanObject,
    mut v___y_1656_: *mut crate::leanh::LeanObject,
    mut v___y_1657_: *mut crate::leanh::LeanObject,
    mut v___y_1658_: *mut crate::leanh::LeanObject,
    mut v___y_1659_: *mut crate::leanh::LeanObject,
    mut v___y_1660_: *mut crate::leanh::LeanObject,
    mut v___y_1661_: *mut crate::leanh::LeanObject,
    mut v___y_1662_: *mut crate::leanh::LeanObject,
    mut v___y_1663_: *mut crate::leanh::LeanObject,
    mut v___y_1664_: *mut crate::leanh::LeanObject,
    mut v___y_1665_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1666_ = l_Lean_Meta_Grind_Arith_CommRing_instMonadSetTermIdNonCommRingM___lam__0(
        v_e_1653_,
        v___y_1654_,
        v___y_1655_,
        v___y_1656_,
        v___y_1657_,
        v___y_1658_,
        v___y_1659_,
        v___y_1660_,
        v___y_1661_,
        v___y_1662_,
        v___y_1663_,
        v___y_1664_,
    );
    crate::leanh::lean_dec(v___y_1664_);
    crate::leanh::lean_dec_ref(v___y_1663_);
    crate::leanh::lean_dec(v___y_1662_);
    crate::leanh::lean_dec_ref(v___y_1661_);
    crate::leanh::lean_dec(v___y_1660_);
    crate::leanh::lean_dec_ref(v___y_1659_);
    crate::leanh::lean_dec(v___y_1658_);
    crate::leanh::lean_dec_ref(v___y_1657_);
    crate::leanh::lean_dec(v___y_1656_);
    crate::leanh::lean_dec(v___y_1655_);
    crate::leanh::lean_dec(v___y_1654_);
    return v_res_1666_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM =
        _init_l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM();
    crate::leanh::lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instMonadRingNonCommRingM);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_NonCommRingM(builtin);
}

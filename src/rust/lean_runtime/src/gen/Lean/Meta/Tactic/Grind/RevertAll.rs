// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.RevertAll
// Imports: Lean.Meta.Tactic.Revert Init.Data.Range.Polymorphic.Iterators
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::{l_Lean_Name_hasMacroScopes, l_Lean_Name_str___override};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_mvarId_x21, l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalContext_getAt_x3f, l_Lean_LocalContext_getFVarIds, l_Lean_LocalContext_setUserName,
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isAuxDecl, l_Lean_LocalDecl_isImplementationDetail,
    l_Lean_LocalDecl_userName, lean_local_ctx_num_indices,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_FVarId_getDecl___redArg,
    l_Lean_MVarId_getDecl, l_Lean_MVarId_setKind___redArg, l_Lean_Meta_mkFreshExprMVarAt,
};
use crate::r#gen::Lean::Meta::Tactic::Revert::{
    initialize_Lean_Meta_Tactic_Revert, l_Lean_MVarId_revert,
    runtime_initialize_Lean_Meta_Tactic_Revert,
};
use crate::r#gen::Lean::Meta::Tactic::Util::l_Lean_MVarId_checkNotAssigned;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_lt, lean_nat_sub, lean_string_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
pub static l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value: crate::leanh::LeanStringObject<13> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [95, 95, 103, 114, 105, 110, 100, 95, 109, 97, 114, 107, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static mut l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_revertAll___lam__0___closed__0_value: crate::leanh::LeanArrayObject<0> =
    crate::leanh::LeanArrayObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<usize>() * 2
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 246,
        },
        m_size: 0,
        m_capacity: 0,
        m_data: [],
    };
static mut l_Lean_MVarId_revertAll___lam__0___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revertAll___lam__0___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_revertAll___closed__0_value: crate::leanh::LeanStringObject<10> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 10,
        m_capacity: 10,
        m_length: 9,
        m_data: [114, 101, 118, 101, 114, 116, 65, 108, 108, 0],
    };
static mut l_Lean_MVarId_revertAll___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revertAll___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_revertAll___closed__1_value: crate::leanh::LeanCtorObject<3> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 8) as u16,
            other: 2,
            tag: 1,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_MVarId_revertAll___closed__0_value)
                as *mut crate::leanh::LeanObject,
            16211803557940772528 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_revertAll___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_revertAll___closed__1_value) as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_getOriginalName_x3f(
    mut v_name_613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_name_613_) == 1 {
        let mut v_pre_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_str_615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_617_: u8 = 0;
        v_pre_614_ = crate::leanh::lean_ctor_get(v_name_613_, 0);
        v_str_615_ = crate::leanh::lean_ctor_get(v_name_613_, 1);
        v___x_616_ =
            l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0;
        v___x_617_ = lean_string_dec_eq(v_str_615_, v___x_616_);
        if v___x_617_ == 0 {
            let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_618_ = crate::leanh::lean_box(0);
            return v___x_618_;
        } else {
            let mut v___x_619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_inc(v_pre_614_);
            v___x_619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_619_, 0, v_pre_614_);
            return v___x_619_;
        }
    } else {
        let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_620_ = crate::leanh::lean_box(0);
        return v___x_620_;
    }
}
pub unsafe fn l_Lean_Meta_Grind_getOriginalName_x3f___boxed(
    mut v_name_621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_622_ = l_Lean_Meta_Grind_getOriginalName_x3f(v_name_621_);
    crate::leanh::lean_dec(v_name_621_);
    return v_res_622_;
}
pub unsafe fn l_Lean_Meta_Grind_markGrindName(
    mut v_userName_623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_624_ =
        l___private_Lean_Meta_Tactic_Grind_RevertAll_0__Lean_Meta_Grind_grindMark___closed__0;
    v___x_625_ = l_Lean_Name_str___override(v_userName_623_, v___x_624_);
    return v___x_625_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(
    mut v_mvarId_626_: *mut crate::leanh::LeanObject,
    mut v_x_627_: *mut crate::leanh::LeanObject,
    mut v___y_628_: *mut crate::leanh::LeanObject,
    mut v___y_629_: *mut crate::leanh::LeanObject,
    mut v___y_630_: *mut crate::leanh::LeanObject,
    mut v___y_631_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_637_: u8 = 0;
    let mut v___x_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_641_: u8 = 0;
    let mut v_a_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_645_: u8 = 0;
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_649_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_633_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_626_,
                    v_x_627_,
                    v___y_628_,
                    v___y_629_,
                    v___y_630_,
                    v___y_631_,
                );
                if crate::leanh::lean_obj_tag(v___x_633_) == 0 {
                    v_a_634_ = crate::leanh::lean_ctor_get(v___x_633_, 0);
                    v_isSharedCheck_641_ = (!crate::leanh::lean_is_exclusive(v___x_633_)) as u8;
                    if v_isSharedCheck_641_ == 0 {
                        v___x_636_ = v___x_633_;
                        v_isShared_637_ = v_isSharedCheck_641_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_634_);
                        crate::leanh::lean_dec(v___x_633_);
                        v___x_636_ = crate::leanh::lean_box(0);
                        v_isShared_637_ = v_isSharedCheck_641_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_642_ = crate::leanh::lean_ctor_get(v___x_633_, 0);
                    v_isSharedCheck_649_ = (!crate::leanh::lean_is_exclusive(v___x_633_)) as u8;
                    if v_isSharedCheck_649_ == 0 {
                        v___x_644_ = v___x_633_;
                        v_isShared_645_ = v_isSharedCheck_649_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_642_);
                        crate::leanh::lean_dec(v___x_633_);
                        v___x_644_ = crate::leanh::lean_box(0);
                        v_isShared_645_ = v_isSharedCheck_649_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_637_ == 0 {
                    v___x_639_ = v___x_636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_640_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_640_, 0, v_a_634_);
                    v___x_639_ = v_reuseFailAlloc_640_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_639_;
            }
            3 => {
                if v_isShared_645_ == 0 {
                    v___x_647_ = v___x_644_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_648_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_648_, 0, v_a_642_);
                    v___x_647_ = v_reuseFailAlloc_648_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_647_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg___boxed(
    mut v_mvarId_650_: *mut crate::leanh::LeanObject,
    mut v_x_651_: *mut crate::leanh::LeanObject,
    mut v___y_652_: *mut crate::leanh::LeanObject,
    mut v___y_653_: *mut crate::leanh::LeanObject,
    mut v___y_654_: *mut crate::leanh::LeanObject,
    mut v___y_655_: *mut crate::leanh::LeanObject,
    mut v___y_656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_657_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(
        v_mvarId_650_,
        v_x_651_,
        v___y_652_,
        v___y_653_,
        v___y_654_,
        v___y_655_,
    );
    crate::leanh::lean_dec(v___y_655_);
    crate::leanh::lean_dec_ref(v___y_654_);
    crate::leanh::lean_dec(v___y_653_);
    crate::leanh::lean_dec_ref(v___y_652_);
    return v_res_657_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(
    mut v_00_u03b1_658_: *mut crate::leanh::LeanObject,
    mut v_mvarId_659_: *mut crate::leanh::LeanObject,
    mut v_x_660_: *mut crate::leanh::LeanObject,
    mut v___y_661_: *mut crate::leanh::LeanObject,
    mut v___y_662_: *mut crate::leanh::LeanObject,
    mut v___y_663_: *mut crate::leanh::LeanObject,
    mut v___y_664_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_666_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(
        v_mvarId_659_,
        v_x_660_,
        v___y_661_,
        v___y_662_,
        v___y_663_,
        v___y_664_,
    );
    return v___x_666_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___boxed(
    mut v_00_u03b1_667_: *mut crate::leanh::LeanObject,
    mut v_mvarId_668_: *mut crate::leanh::LeanObject,
    mut v_x_669_: *mut crate::leanh::LeanObject,
    mut v___y_670_: *mut crate::leanh::LeanObject,
    mut v___y_671_: *mut crate::leanh::LeanObject,
    mut v___y_672_: *mut crate::leanh::LeanObject,
    mut v___y_673_: *mut crate::leanh::LeanObject,
    mut v___y_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_675_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2(
        v_00_u03b1_667_,
        v_mvarId_668_,
        v_x_669_,
        v___y_670_,
        v___y_671_,
        v___y_672_,
        v___y_673_,
    );
    crate::leanh::lean_dec(v___y_673_);
    crate::leanh::lean_dec_ref(v___y_672_);
    crate::leanh::lean_dec(v___y_671_);
    crate::leanh::lean_dec_ref(v___y_670_);
    return v_res_675_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(
    mut v_x_676_: *mut crate::leanh::LeanObject,
    mut v_x_677_: *mut crate::leanh::LeanObject,
    mut v_x_678_: *mut crate::leanh::LeanObject,
    mut v_x_679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_684_: u8 = 0;
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: u8 = 0;
    let mut v___x_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: u8 = 0;
    let mut v___x_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_705_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_680_ = crate::leanh::lean_ctor_get(v_x_676_, 0);
                v_vs_681_ = crate::leanh::lean_ctor_get(v_x_676_, 1);
                v_isSharedCheck_705_ = (!crate::leanh::lean_is_exclusive(v_x_676_)) as u8;
                if v_isSharedCheck_705_ == 0 {
                    v___x_683_ = v_x_676_;
                    v_isShared_684_ = v_isSharedCheck_705_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_681_);
                    crate::leanh::lean_inc(v_ks_680_);
                    crate::leanh::lean_dec(v_x_676_);
                    v___x_683_ = crate::leanh::lean_box(0);
                    v_isShared_684_ = v_isSharedCheck_705_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_685_ = lean_array_get_size(v_ks_680_);
                v___x_686_ = lean_nat_dec_lt(v_x_677_, v___x_685_);
                if v___x_686_ == 0 {
                    crate::leanh::lean_dec(v_x_677_);
                    v___x_687_ = lean_array_push(v_ks_680_, v_x_678_);
                    v___x_688_ = lean_array_push(v_vs_681_, v_x_679_);
                    if v_isShared_684_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_683_, 1, v___x_688_);
                        crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_687_);
                        v___x_690_ = v___x_683_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_691_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_687_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_691_, 1, v___x_688_);
                        v___x_690_ = v_reuseFailAlloc_691_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_692_ = lean_array_fget_borrowed(v_ks_680_, v_x_677_);
                    v___x_693_ = l_Lean_instBEqMVarId_beq(v_x_678_, v_k_x27_692_);
                    if v___x_693_ == 0 {
                        if v_isShared_684_ == 0 {
                            v___x_695_ = v___x_683_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_699_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_699_, 0, v_ks_680_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_699_, 1, v_vs_681_);
                            v___x_695_ = v_reuseFailAlloc_699_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_700_ = lean_array_fset(v_ks_680_, v_x_677_, v_x_678_);
                        v___x_701_ = lean_array_fset(v_vs_681_, v_x_677_, v_x_679_);
                        crate::leanh::lean_dec(v_x_677_);
                        if v_isShared_684_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_683_, 1, v___x_701_);
                            crate::leanh::lean_ctor_set(v___x_683_, 0, v___x_700_);
                            v___x_703_ = v___x_683_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_704_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_700_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_704_, 1, v___x_701_);
                            v___x_703_ = v_reuseFailAlloc_704_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_690_;
            }
            3 => {
                v___x_696_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_697_ = lean_nat_add(v_x_677_, v___x_696_);
                crate::leanh::lean_dec(v_x_677_);
                v_x_676_ = v___x_695_;
                v_x_677_ = v___x_697_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_703_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_n_706_: *mut crate::leanh::LeanObject,
    mut v_k_707_: *mut crate::leanh::LeanObject,
    mut v_v_708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_709_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_710_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_706_, v___x_709_, v_k_707_, v_v_708_);
    return v___x_710_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_711_: usize = 0;
    let mut v___x_712_: usize = 0;
    let mut v___x_713_: usize = 0;
    v___x_711_ = 5usize;
    v___x_712_ = 1usize;
    v___x_713_ = lean_usize_shift_left(v___x_712_, v___x_711_);
    return v___x_713_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_714_: usize = 0;
    let mut v___x_715_: usize = 0;
    let mut v___x_716_: usize = 0;
    v___x_714_ = 1usize;
    v___x_715_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_716_ = lean_usize_sub(v___x_715_, v___x_714_);
    return v___x_716_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_717_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_717_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(
    mut v_x_718_: *mut crate::leanh::LeanObject,
    mut v_x_719_: usize,
    mut v_x_720_: usize,
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v_x_722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_724_: usize = 0;
    let mut v___x_725_: usize = 0;
    let mut v___x_726_: usize = 0;
    let mut v___x_727_: usize = 0;
    let mut v_j_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: u8 = 0;
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_733_: u8 = 0;
    let mut v_v_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_747_: u8 = 0;
    let mut v___x_748_: u8 = 0;
    let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_754_: u8 = 0;
    let mut v_node_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_758_: u8 = 0;
    let mut v___x_759_: usize = 0;
    let mut v___x_760_: usize = 0;
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_765_: u8 = 0;
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_767_: u8 = 0;
    let mut v_unused_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_773_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_778_: u8 = 0;
    let mut v_ks_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: usize = 0;
    let mut v___x_785_: u8 = 0;
    let mut v___x_786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: u8 = 0;
    let mut v_reuseFailAlloc_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_718_) == 0 {
                    v_es_723_ = crate::leanh::lean_ctor_get(v_x_718_, 0);
                    v___x_724_ = 5usize;
                    v___x_725_ = 1usize;
                    v___x_726_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_727_ = lean_usize_land(v_x_719_, v___x_726_);
                    v_j_728_ = lean_usize_to_nat(v___x_727_);
                    v___x_729_ = lean_array_get_size(v_es_723_);
                    v___x_730_ = lean_nat_dec_lt(v_j_728_, v___x_729_);
                    if v___x_730_ == 0 {
                        crate::leanh::lean_dec(v_j_728_);
                        crate::leanh::lean_dec(v_x_722_);
                        crate::leanh::lean_dec(v_x_721_);
                        return v_x_718_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_723_);
                        v_isSharedCheck_767_ = (!crate::leanh::lean_is_exclusive(v_x_718_)) as u8;
                        if v_isSharedCheck_767_ == 0 {
                            v_unused_768_ = crate::leanh::lean_ctor_get(v_x_718_, 0);
                            crate::leanh::lean_dec(v_unused_768_);
                            v___x_732_ = v_x_718_;
                            v_isShared_733_ = v_isSharedCheck_767_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_718_);
                            v___x_732_ = crate::leanh::lean_box(0);
                            v_isShared_733_ = v_isSharedCheck_767_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_769_ = crate::leanh::lean_ctor_get(v_x_718_, 0);
                    v_vs_770_ = crate::leanh::lean_ctor_get(v_x_718_, 1);
                    v_isSharedCheck_790_ = (!crate::leanh::lean_is_exclusive(v_x_718_)) as u8;
                    if v_isSharedCheck_790_ == 0 {
                        v___x_772_ = v_x_718_;
                        v_isShared_773_ = v_isSharedCheck_790_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_770_);
                        crate::leanh::lean_inc(v_ks_769_);
                        crate::leanh::lean_dec(v_x_718_);
                        v___x_772_ = crate::leanh::lean_box(0);
                        v_isShared_773_ = v_isSharedCheck_790_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_734_ = lean_array_fget(v_es_723_, v_j_728_);
                v___x_735_ = crate::leanh::lean_box(0);
                v_xs_x27_736_ = lean_array_fset(v_es_723_, v_j_728_, v___x_735_);
                match crate::leanh::lean_obj_tag(v_v_734_) {
                    0 => {
                        v_key_743_ = crate::leanh::lean_ctor_get(v_v_734_, 0);
                        v_val_744_ = crate::leanh::lean_ctor_get(v_v_734_, 1);
                        v_isSharedCheck_754_ = (!crate::leanh::lean_is_exclusive(v_v_734_)) as u8;
                        if v_isSharedCheck_754_ == 0 {
                            v___x_746_ = v_v_734_;
                            v_isShared_747_ = v_isSharedCheck_754_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_744_);
                            crate::leanh::lean_inc(v_key_743_);
                            crate::leanh::lean_dec(v_v_734_);
                            v___x_746_ = crate::leanh::lean_box(0);
                            v_isShared_747_ = v_isSharedCheck_754_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_755_ = crate::leanh::lean_ctor_get(v_v_734_, 0);
                        v_isSharedCheck_765_ = (!crate::leanh::lean_is_exclusive(v_v_734_)) as u8;
                        if v_isSharedCheck_765_ == 0 {
                            v___x_757_ = v_v_734_;
                            v_isShared_758_ = v_isSharedCheck_765_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_755_);
                            crate::leanh::lean_dec(v_v_734_);
                            v___x_757_ = crate::leanh::lean_box(0);
                            v_isShared_758_ = v_isSharedCheck_765_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_766_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_766_, 0, v_x_721_);
                        crate::leanh::lean_ctor_set(v___x_766_, 1, v_x_722_);
                        v___y_738_ = v___x_766_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_739_ = lean_array_fset(v_xs_x27_736_, v_j_728_, v___y_738_);
                crate::leanh::lean_dec(v_j_728_);
                if v_isShared_733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_732_, 0, v___x_739_);
                    v___x_741_ = v___x_732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_742_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 0, v___x_739_);
                    v___x_741_ = v_reuseFailAlloc_742_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_741_;
            }
            4 => {
                v___x_748_ = l_Lean_instBEqMVarId_beq(v_x_721_, v_key_743_);
                if v___x_748_ == 0 {
                    crate::leanh::lean_del_object(v___x_746_);
                    v___x_749_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_743_, v_val_744_, v_x_721_, v_x_722_,
                    );
                    v___x_750_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_750_, 0, v___x_749_);
                    v___y_738_ = v___x_750_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_744_);
                    crate::leanh::lean_dec(v_key_743_);
                    if v_isShared_747_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_746_, 1, v_x_722_);
                        crate::leanh::lean_ctor_set(v___x_746_, 0, v_x_721_);
                        v___x_752_ = v___x_746_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_753_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_753_, 0, v_x_721_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_753_, 1, v_x_722_);
                        v___x_752_ = v_reuseFailAlloc_753_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_738_ = v___x_752_;
                state = 2;
                continue;
            }
            6 => {
                v___x_759_ = lean_usize_shift_right(v_x_719_, v___x_724_);
                v___x_760_ = lean_usize_add(v_x_720_, v___x_725_);
                v___x_761_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_node_755_, v___x_759_, v___x_760_, v_x_721_, v_x_722_);
                if v_isShared_758_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_761_);
                    v___x_763_ = v___x_757_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_764_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_764_, 0, v___x_761_);
                    v___x_763_ = v_reuseFailAlloc_764_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_738_ = v___x_763_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_773_ == 0 {
                    v___x_775_ = v___x_772_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v_ks_769_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 1, v_vs_770_);
                    v___x_775_ = v_reuseFailAlloc_789_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_776_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v___x_775_, v_x_721_, v_x_722_);
                v___x_784_ = 7usize;
                v___x_785_ = lean_usize_dec_le(v___x_784_, v_x_720_);
                if v___x_785_ == 0 {
                    v___x_786_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_776_);
                    v___x_787_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_788_ = lean_nat_dec_lt(v___x_786_, v___x_787_);
                    crate::leanh::lean_dec(v___x_786_);
                    v___y_778_ = v___x_788_;
                    state = 10;
                    continue;
                } else {
                    v___y_778_ = v___x_785_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_778_ == 0 {
                    v_ks_779_ = crate::leanh::lean_ctor_get(v_newNode_776_, 0);
                    crate::leanh::lean_inc_ref(v_ks_779_);
                    v_vs_780_ = crate::leanh::lean_ctor_get(v_newNode_776_, 1);
                    crate::leanh::lean_inc_ref(v_vs_780_);
                    crate::leanh::lean_dec_ref(v_newNode_776_);
                    v___x_781_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_782_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_783_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_x_720_, v_ks_779_, v_vs_780_, v___x_781_, v___x_782_);
                    crate::leanh::lean_dec_ref(v_vs_780_);
                    crate::leanh::lean_dec_ref(v_ks_779_);
                    return v___x_783_;
                } else {
                    return v_newNode_776_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_depth_791_: usize,
    mut v_keys_792_: *mut crate::leanh::LeanObject,
    mut v_vals_793_: *mut crate::leanh::LeanObject,
    mut v_i_794_: *mut crate::leanh::LeanObject,
    mut v_entries_795_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: u8 = 0;
    let mut v_k_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_800_: u64 = 0;
    let mut v_h_801_: usize = 0;
    let mut v___x_802_: usize = 0;
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: usize = 0;
    let mut v___x_805_: usize = 0;
    let mut v___x_806_: usize = 0;
    let mut v_h_807_: usize = 0;
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_796_ = lean_array_get_size(v_keys_792_);
                v___x_797_ = lean_nat_dec_lt(v_i_794_, v___x_796_);
                if v___x_797_ == 0 {
                    crate::leanh::lean_dec(v_i_794_);
                    return v_entries_795_;
                } else {
                    v_k_798_ = lean_array_fget_borrowed(v_keys_792_, v_i_794_);
                    v_v_799_ = lean_array_fget_borrowed(v_vals_793_, v_i_794_);
                    v___x_800_ = l_Lean_instHashableMVarId_hash(v_k_798_);
                    v_h_801_ = lean_uint64_to_usize(v___x_800_);
                    v___x_802_ = 5usize;
                    v___x_803_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_804_ = 1usize;
                    v___x_805_ = lean_usize_sub(v_depth_791_, v___x_804_);
                    v___x_806_ = lean_usize_mul(v___x_802_, v___x_805_);
                    v_h_807_ = lean_usize_shift_right(v_h_801_, v___x_806_);
                    v___x_808_ = lean_nat_add(v_i_794_, v___x_803_);
                    crate::leanh::lean_dec(v_i_794_);
                    crate::leanh::lean_inc(v_v_799_);
                    crate::leanh::lean_inc(v_k_798_);
                    v___x_809_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_entries_795_, v_h_807_, v_depth_791_, v_k_798_, v_v_799_);
                    v_i_794_ = v___x_808_;
                    v_entries_795_ = v___x_809_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_depth_811_: *mut crate::leanh::LeanObject,
    mut v_keys_812_: *mut crate::leanh::LeanObject,
    mut v_vals_813_: *mut crate::leanh::LeanObject,
    mut v_i_814_: *mut crate::leanh::LeanObject,
    mut v_entries_815_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_816_: usize = 0;
    let mut v_res_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_816_ = crate::leanh::lean_unbox_usize(v_depth_811_);
    crate::leanh::lean_dec(v_depth_811_);
    v_res_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_816_, v_keys_812_, v_vals_813_, v_i_814_, v_entries_815_);
    crate::leanh::lean_dec_ref(v_vals_813_);
    crate::leanh::lean_dec_ref(v_keys_812_);
    return v_res_817_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_818_: *mut crate::leanh::LeanObject,
    mut v_x_819_: *mut crate::leanh::LeanObject,
    mut v_x_820_: *mut crate::leanh::LeanObject,
    mut v_x_821_: *mut crate::leanh::LeanObject,
    mut v_x_822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_2956__boxed_823_: usize = 0;
    let mut v_x_2957__boxed_824_: usize = 0;
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_2956__boxed_823_ = crate::leanh::lean_unbox_usize(v_x_819_);
    crate::leanh::lean_dec(v_x_819_);
    v_x_2957__boxed_824_ = crate::leanh::lean_unbox_usize(v_x_820_);
    crate::leanh::lean_dec(v_x_820_);
    v_res_825_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_818_, v_x_2956__boxed_823_, v_x_2957__boxed_824_, v_x_821_, v_x_822_);
    return v_res_825_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(
    mut v_x_826_: *mut crate::leanh::LeanObject,
    mut v_x_827_: *mut crate::leanh::LeanObject,
    mut v_x_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: u64 = 0;
    let mut v___x_830_: usize = 0;
    let mut v___x_831_: usize = 0;
    let mut v___x_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_829_ = l_Lean_instHashableMVarId_hash(v_x_827_);
    v___x_830_ = lean_uint64_to_usize(v___x_829_);
    v___x_831_ = 1usize;
    v___x_832_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_826_, v___x_830_, v___x_831_, v_x_827_, v_x_828_);
    return v___x_832_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(
    mut v_mvarId_833_: *mut crate::leanh::LeanObject,
    mut v_val_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_845_: u8 = 0;
    let mut v_depth_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_858_: u8 = 0;
    let mut v___x_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_869_: u8 = 0;
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_837_ = lean_st_ref_take(v___y_835_);
                v_mctx_838_ = crate::leanh::lean_ctor_get(v___x_837_, 0);
                v_cache_839_ = crate::leanh::lean_ctor_get(v___x_837_, 1);
                v_zetaDeltaFVarIds_840_ = crate::leanh::lean_ctor_get(v___x_837_, 2);
                v_postponed_841_ = crate::leanh::lean_ctor_get(v___x_837_, 3);
                v_diag_842_ = crate::leanh::lean_ctor_get(v___x_837_, 4);
                v_isSharedCheck_870_ = (!crate::leanh::lean_is_exclusive(v___x_837_)) as u8;
                if v_isSharedCheck_870_ == 0 {
                    v___x_844_ = v___x_837_;
                    v_isShared_845_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_842_);
                    crate::leanh::lean_inc(v_postponed_841_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_840_);
                    crate::leanh::lean_inc(v_cache_839_);
                    crate::leanh::lean_inc(v_mctx_838_);
                    crate::leanh::lean_dec(v___x_837_);
                    v___x_844_ = crate::leanh::lean_box(0);
                    v_isShared_845_ = v_isSharedCheck_870_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_846_ = crate::leanh::lean_ctor_get(v_mctx_838_, 0);
                v_levelAssignDepth_847_ = crate::leanh::lean_ctor_get(v_mctx_838_, 1);
                v_lmvarCounter_848_ = crate::leanh::lean_ctor_get(v_mctx_838_, 2);
                v_mvarCounter_849_ = crate::leanh::lean_ctor_get(v_mctx_838_, 3);
                v_lDecls_850_ = crate::leanh::lean_ctor_get(v_mctx_838_, 4);
                v_decls_851_ = crate::leanh::lean_ctor_get(v_mctx_838_, 5);
                v_userNames_852_ = crate::leanh::lean_ctor_get(v_mctx_838_, 6);
                v_lAssignment_853_ = crate::leanh::lean_ctor_get(v_mctx_838_, 7);
                v_eAssignment_854_ = crate::leanh::lean_ctor_get(v_mctx_838_, 8);
                v_dAssignment_855_ = crate::leanh::lean_ctor_get(v_mctx_838_, 9);
                v_isSharedCheck_869_ = (!crate::leanh::lean_is_exclusive(v_mctx_838_)) as u8;
                if v_isSharedCheck_869_ == 0 {
                    v___x_857_ = v_mctx_838_;
                    v_isShared_858_ = v_isSharedCheck_869_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_855_);
                    crate::leanh::lean_inc(v_eAssignment_854_);
                    crate::leanh::lean_inc(v_lAssignment_853_);
                    crate::leanh::lean_inc(v_userNames_852_);
                    crate::leanh::lean_inc(v_decls_851_);
                    crate::leanh::lean_inc(v_lDecls_850_);
                    crate::leanh::lean_inc(v_mvarCounter_849_);
                    crate::leanh::lean_inc(v_lmvarCounter_848_);
                    crate::leanh::lean_inc(v_levelAssignDepth_847_);
                    crate::leanh::lean_inc(v_depth_846_);
                    crate::leanh::lean_dec(v_mctx_838_);
                    v___x_857_ = crate::leanh::lean_box(0);
                    v_isShared_858_ = v_isSharedCheck_869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_859_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_eAssignment_854_, v_mvarId_833_, v_val_834_);
                if v_isShared_858_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_857_, 8, v___x_859_);
                    v___x_861_ = v___x_857_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_868_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 0, v_depth_846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 1, v_levelAssignDepth_847_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 2, v_lmvarCounter_848_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 3, v_mvarCounter_849_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 4, v_lDecls_850_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 5, v_decls_851_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 6, v_userNames_852_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 7, v_lAssignment_853_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 8, v___x_859_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_868_, 9, v_dAssignment_855_);
                    v___x_861_ = v_reuseFailAlloc_868_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_845_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_844_, 0, v___x_861_);
                    v___x_863_ = v___x_844_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_867_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_861_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_867_, 1, v_cache_839_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_867_, 2, v_zetaDeltaFVarIds_840_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_867_, 3, v_postponed_841_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_867_, 4, v_diag_842_);
                    v___x_863_ = v_reuseFailAlloc_867_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_864_ = lean_st_ref_set(v___y_835_, v___x_863_);
                v___x_865_ = crate::leanh::lean_box(0);
                v___x_866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_866_, 0, v___x_865_);
                return v___x_866_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg___boxed(
    mut v_mvarId_871_: *mut crate::leanh::LeanObject,
    mut v_val_872_: *mut crate::leanh::LeanObject,
    mut v___y_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_875_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(
        v_mvarId_871_,
        v_val_872_,
        v___y_873_,
    );
    crate::leanh::lean_dec(v___y_873_);
    return v_res_875_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(
    mut v_upperBound_876_: *mut crate::leanh::LeanObject,
    mut v___x_877_: *mut crate::leanh::LeanObject,
    mut v_a_878_: *mut crate::leanh::LeanObject,
    mut v_b_879_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: u8 = 0;
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_893_: u8 = 0;
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_886_ = lean_nat_dec_lt(v_a_878_, v_upperBound_876_);
                if v___x_886_ == 0 {
                    crate::leanh::lean_dec(v_a_878_);
                    v___x_887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_887_, 0, v_b_879_);
                    return v___x_887_;
                } else {
                    v___x_888_ = lean_nat_sub(v___x_877_, v_a_878_);
                    v___x_889_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_890_ = lean_nat_sub(v___x_888_, v___x_889_);
                    crate::leanh::lean_dec(v___x_888_);
                    v___x_891_ = l_Lean_LocalContext_getAt_x3f(v_b_879_, v___x_890_);
                    crate::leanh::lean_dec(v___x_890_);
                    if crate::leanh::lean_obj_tag(v___x_891_) == 0 {
                        v_a_882_ = v_b_879_;
                        state = 1;
                        continue;
                    } else {
                        v_val_892_ = crate::leanh::lean_ctor_get(v___x_891_, 0);
                        crate::leanh::lean_inc(v_val_892_);
                        crate::leanh::lean_dec_ref_known(v___x_891_, 1);
                        v___x_893_ = l_Lean_LocalDecl_isImplementationDetail(v_val_892_);
                        if v___x_893_ == 0 {
                            v___x_894_ = l_Lean_LocalDecl_userName(v_val_892_);
                            v___x_895_ = l_Lean_Name_hasMacroScopes(v___x_894_);
                            if v___x_895_ == 0 {
                                v___x_896_ = l_Lean_Meta_Grind_markGrindName(v___x_894_);
                                v___x_897_ = l_Lean_LocalDecl_fvarId(v_val_892_);
                                crate::leanh::lean_dec(v_val_892_);
                                v___x_898_ = l_Lean_LocalContext_setUserName(
                                    v_b_879_, v___x_897_, v___x_896_,
                                );
                                v_a_882_ = v___x_898_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_894_);
                                crate::leanh::lean_dec(v_val_892_);
                                v_a_882_ = v_b_879_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_892_);
                            v_a_882_ = v_b_879_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_883_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_884_ = lean_nat_add(v_a_878_, v___x_883_);
                crate::leanh::lean_dec(v_a_878_);
                v_a_878_ = v___x_884_;
                v_b_879_ = v_a_882_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg___boxed(
    mut v_upperBound_899_: *mut crate::leanh::LeanObject,
    mut v___x_900_: *mut crate::leanh::LeanObject,
    mut v_a_901_: *mut crate::leanh::LeanObject,
    mut v_b_902_: *mut crate::leanh::LeanObject,
    mut v___y_903_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_904_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(
        v_upperBound_899_,
        v___x_900_,
        v_a_901_,
        v_b_902_,
    );
    crate::leanh::lean_dec(v___x_900_);
    crate::leanh::lean_dec(v_upperBound_899_);
    return v_res_904_;
}
pub unsafe fn l_Lean_MVarId_markAccessible___lam__0(
    mut v_mvarId_905_: *mut crate::leanh::LeanObject,
    mut v___y_906_: *mut crate::leanh::LeanObject,
    mut v___y_907_: *mut crate::leanh::LeanObject,
    mut v___y_908_: *mut crate::leanh::LeanObject,
    mut v___y_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userName_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_927_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_932_: u8 = 0;
    let mut v_unused_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_941_: u8 = 0;
    let mut v_a_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_945_: u8 = 0;
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_949_: u8 = 0;
    let mut v_a_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_905_);
                v___x_911_ = l_Lean_MVarId_getDecl(
                    v_mvarId_905_,
                    v___y_906_,
                    v___y_907_,
                    v___y_908_,
                    v___y_909_,
                );
                if crate::leanh::lean_obj_tag(v___x_911_) == 0 {
                    v_a_912_ = crate::leanh::lean_ctor_get(v___x_911_, 0);
                    crate::leanh::lean_inc(v_a_912_);
                    crate::leanh::lean_dec_ref_known(v___x_911_, 1);
                    v_userName_913_ = crate::leanh::lean_ctor_get(v_a_912_, 0);
                    crate::leanh::lean_inc(v_userName_913_);
                    v_lctx_914_ = crate::leanh::lean_ctor_get(v_a_912_, 1);
                    crate::leanh::lean_inc_ref_n(v_lctx_914_, 2);
                    v_type_915_ = crate::leanh::lean_ctor_get(v_a_912_, 2);
                    crate::leanh::lean_inc_ref(v_type_915_);
                    v_localInstances_916_ = crate::leanh::lean_ctor_get(v_a_912_, 4);
                    crate::leanh::lean_inc_ref(v_localInstances_916_);
                    crate::leanh::lean_dec(v_a_912_);
                    v___x_917_ = lean_local_ctx_num_indices(v_lctx_914_);
                    v___x_918_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_919_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(v___x_917_, v___x_917_, v___x_918_, v_lctx_914_);
                    crate::leanh::lean_dec(v___x_917_);
                    if crate::leanh::lean_obj_tag(v___x_919_) == 0 {
                        v_a_920_ = crate::leanh::lean_ctor_get(v___x_919_, 0);
                        crate::leanh::lean_inc(v_a_920_);
                        crate::leanh::lean_dec_ref_known(v___x_919_, 1);
                        v___x_921_ = 2;
                        v___x_922_ = l_Lean_Meta_mkFreshExprMVarAt(
                            v_a_920_,
                            v_localInstances_916_,
                            v_type_915_,
                            v___x_921_,
                            v_userName_913_,
                            v___x_918_,
                            v___y_906_,
                            v___y_907_,
                            v___y_908_,
                            v___y_909_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_922_) == 0 {
                            v_a_923_ = crate::leanh::lean_ctor_get(v___x_922_, 0);
                            crate::leanh::lean_inc_n(v_a_923_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_922_, 1);
                            v___x_924_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(v_mvarId_905_, v_a_923_, v___y_907_);
                            v_isSharedCheck_932_ =
                                (!crate::leanh::lean_is_exclusive(v___x_924_)) as u8;
                            if v_isSharedCheck_932_ == 0 {
                                v_unused_933_ = crate::leanh::lean_ctor_get(v___x_924_, 0);
                                crate::leanh::lean_dec(v_unused_933_);
                                v___x_926_ = v___x_924_;
                                v_isShared_927_ = v_isSharedCheck_932_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_924_);
                                v___x_926_ = crate::leanh::lean_box(0);
                                v_isShared_927_ = v_isSharedCheck_932_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_905_);
                            v_a_934_ = crate::leanh::lean_ctor_get(v___x_922_, 0);
                            v_isSharedCheck_941_ =
                                (!crate::leanh::lean_is_exclusive(v___x_922_)) as u8;
                            if v_isSharedCheck_941_ == 0 {
                                v___x_936_ = v___x_922_;
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_934_);
                                crate::leanh::lean_dec(v___x_922_);
                                v___x_936_ = crate::leanh::lean_box(0);
                                v_isShared_937_ = v_isSharedCheck_941_;
                                state = 3;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_localInstances_916_);
                        crate::leanh::lean_dec_ref(v_type_915_);
                        crate::leanh::lean_dec(v_userName_913_);
                        crate::leanh::lean_dec(v_mvarId_905_);
                        v_a_942_ = crate::leanh::lean_ctor_get(v___x_919_, 0);
                        v_isSharedCheck_949_ = (!crate::leanh::lean_is_exclusive(v___x_919_)) as u8;
                        if v_isSharedCheck_949_ == 0 {
                            v___x_944_ = v___x_919_;
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_942_);
                            crate::leanh::lean_dec(v___x_919_);
                            v___x_944_ = crate::leanh::lean_box(0);
                            v_isShared_945_ = v_isSharedCheck_949_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_905_);
                    v_a_950_ = crate::leanh::lean_ctor_get(v___x_911_, 0);
                    v_isSharedCheck_957_ = (!crate::leanh::lean_is_exclusive(v___x_911_)) as u8;
                    if v_isSharedCheck_957_ == 0 {
                        v___x_952_ = v___x_911_;
                        v_isShared_953_ = v_isSharedCheck_957_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_950_);
                        crate::leanh::lean_dec(v___x_911_);
                        v___x_952_ = crate::leanh::lean_box(0);
                        v_isShared_953_ = v_isSharedCheck_957_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_928_ = l_Lean_Expr_mvarId_x21(v_a_923_);
                crate::leanh::lean_dec(v_a_923_);
                if v_isShared_927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_926_, 0, v___x_928_);
                    v___x_930_ = v___x_926_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_931_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
                    v___x_930_ = v_reuseFailAlloc_931_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_930_;
            }
            3 => {
                if v_isShared_937_ == 0 {
                    v___x_939_ = v___x_936_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_940_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_940_, 0, v_a_934_);
                    v___x_939_ = v_reuseFailAlloc_940_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_939_;
            }
            5 => {
                if v_isShared_945_ == 0 {
                    v___x_947_ = v___x_944_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_948_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_948_, 0, v_a_942_);
                    v___x_947_ = v_reuseFailAlloc_948_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_947_;
            }
            7 => {
                if v_isShared_953_ == 0 {
                    v___x_955_ = v___x_952_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_a_950_);
                    v___x_955_ = v_reuseFailAlloc_956_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_markAccessible___lam__0___boxed(
    mut v_mvarId_958_: *mut crate::leanh::LeanObject,
    mut v___y_959_: *mut crate::leanh::LeanObject,
    mut v___y_960_: *mut crate::leanh::LeanObject,
    mut v___y_961_: *mut crate::leanh::LeanObject,
    mut v___y_962_: *mut crate::leanh::LeanObject,
    mut v___y_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_964_ = l_Lean_MVarId_markAccessible___lam__0(
        v_mvarId_958_,
        v___y_959_,
        v___y_960_,
        v___y_961_,
        v___y_962_,
    );
    crate::leanh::lean_dec(v___y_962_);
    crate::leanh::lean_dec_ref(v___y_961_);
    crate::leanh::lean_dec(v___y_960_);
    crate::leanh::lean_dec_ref(v___y_959_);
    return v_res_964_;
}
pub unsafe fn l_Lean_MVarId_markAccessible(
    mut v_mvarId_965_: *mut crate::leanh::LeanObject,
    mut v_a_966_: *mut crate::leanh::LeanObject,
    mut v_a_967_: *mut crate::leanh::LeanObject,
    mut v_a_968_: *mut crate::leanh::LeanObject,
    mut v_a_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_mvarId_965_);
    v___f_971_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_markAccessible___lam__0___boxed as *mut core::ffi::c_void,
        6,
        1,
    );
    crate::leanh::lean_closure_set(v___f_971_, 0, v_mvarId_965_);
    v___x_972_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(
        v_mvarId_965_,
        v___f_971_,
        v_a_966_,
        v_a_967_,
        v_a_968_,
        v_a_969_,
    );
    return v___x_972_;
}
pub unsafe fn l_Lean_MVarId_markAccessible___boxed(
    mut v_mvarId_973_: *mut crate::leanh::LeanObject,
    mut v_a_974_: *mut crate::leanh::LeanObject,
    mut v_a_975_: *mut crate::leanh::LeanObject,
    mut v_a_976_: *mut crate::leanh::LeanObject,
    mut v_a_977_: *mut crate::leanh::LeanObject,
    mut v_a_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_979_ =
        l_Lean_MVarId_markAccessible(v_mvarId_973_, v_a_974_, v_a_975_, v_a_976_, v_a_977_);
    crate::leanh::lean_dec(v_a_977_);
    crate::leanh::lean_dec_ref(v_a_976_);
    crate::leanh::lean_dec(v_a_975_);
    crate::leanh::lean_dec_ref(v_a_974_);
    return v_res_979_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(
    mut v_mvarId_980_: *mut crate::leanh::LeanObject,
    mut v_val_981_: *mut crate::leanh::LeanObject,
    mut v___y_982_: *mut crate::leanh::LeanObject,
    mut v___y_983_: *mut crate::leanh::LeanObject,
    mut v___y_984_: *mut crate::leanh::LeanObject,
    mut v___y_985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_987_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___redArg(
        v_mvarId_980_,
        v_val_981_,
        v___y_983_,
    );
    return v___x_987_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0___boxed(
    mut v_mvarId_988_: *mut crate::leanh::LeanObject,
    mut v_val_989_: *mut crate::leanh::LeanObject,
    mut v___y_990_: *mut crate::leanh::LeanObject,
    mut v___y_991_: *mut crate::leanh::LeanObject,
    mut v___y_992_: *mut crate::leanh::LeanObject,
    mut v___y_993_: *mut crate::leanh::LeanObject,
    mut v___y_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l_Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0(
        v_mvarId_988_,
        v_val_989_,
        v___y_990_,
        v___y_991_,
        v___y_992_,
        v___y_993_,
    );
    crate::leanh::lean_dec(v___y_993_);
    crate::leanh::lean_dec_ref(v___y_992_);
    crate::leanh::lean_dec(v___y_991_);
    crate::leanh::lean_dec_ref(v___y_990_);
    return v_res_995_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(
    mut v_upperBound_996_: *mut crate::leanh::LeanObject,
    mut v___x_997_: *mut crate::leanh::LeanObject,
    mut v_inst_998_: *mut crate::leanh::LeanObject,
    mut v_R_999_: *mut crate::leanh::LeanObject,
    mut v_a_1000_: *mut crate::leanh::LeanObject,
    mut v_b_1001_: *mut crate::leanh::LeanObject,
    mut v_c_1002_: *mut crate::leanh::LeanObject,
    mut v___y_1003_: *mut crate::leanh::LeanObject,
    mut v___y_1004_: *mut crate::leanh::LeanObject,
    mut v___y_1005_: *mut crate::leanh::LeanObject,
    mut v___y_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1008_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___redArg(
            v_upperBound_996_,
            v___x_997_,
            v_a_1000_,
            v_b_1001_,
        );
    return v___x_1008_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1___boxed(
    mut v_upperBound_1009_: *mut crate::leanh::LeanObject,
    mut v___x_1010_: *mut crate::leanh::LeanObject,
    mut v_inst_1011_: *mut crate::leanh::LeanObject,
    mut v_R_1012_: *mut crate::leanh::LeanObject,
    mut v_a_1013_: *mut crate::leanh::LeanObject,
    mut v_b_1014_: *mut crate::leanh::LeanObject,
    mut v_c_1015_: *mut crate::leanh::LeanObject,
    mut v___y_1016_: *mut crate::leanh::LeanObject,
    mut v___y_1017_: *mut crate::leanh::LeanObject,
    mut v___y_1018_: *mut crate::leanh::LeanObject,
    mut v___y_1019_: *mut crate::leanh::LeanObject,
    mut v___y_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1021_ = l_WellFounded_opaqueFix_u2083___at___00Lean_MVarId_markAccessible_spec__1(
        v_upperBound_1009_,
        v___x_1010_,
        v_inst_1011_,
        v_R_1012_,
        v_a_1013_,
        v_b_1014_,
        v_c_1015_,
        v___y_1016_,
        v___y_1017_,
        v___y_1018_,
        v___y_1019_,
    );
    crate::leanh::lean_dec(v___y_1019_);
    crate::leanh::lean_dec_ref(v___y_1018_);
    crate::leanh::lean_dec(v___y_1017_);
    crate::leanh::lean_dec_ref(v___y_1016_);
    crate::leanh::lean_dec(v___x_1010_);
    crate::leanh::lean_dec(v_upperBound_1009_);
    return v_res_1021_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0(
    mut v_00_u03b2_1022_: *mut crate::leanh::LeanObject,
    mut v_x_1023_: *mut crate::leanh::LeanObject,
    mut v_x_1024_: *mut crate::leanh::LeanObject,
    mut v_x_1025_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1026_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0___redArg(v_x_1023_, v_x_1024_, v_x_1025_);
    return v___x_1026_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1027_: *mut crate::leanh::LeanObject,
    mut v_x_1028_: *mut crate::leanh::LeanObject,
    mut v_x_1029_: usize,
    mut v_x_1030_: usize,
    mut v_x_1031_: *mut crate::leanh::LeanObject,
    mut v_x_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___redArg(v_x_1028_, v_x_1029_, v_x_1030_, v_x_1031_, v_x_1032_);
    return v___x_1033_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1034_: *mut crate::leanh::LeanObject,
    mut v_x_1035_: *mut crate::leanh::LeanObject,
    mut v_x_1036_: *mut crate::leanh::LeanObject,
    mut v_x_1037_: *mut crate::leanh::LeanObject,
    mut v_x_1038_: *mut crate::leanh::LeanObject,
    mut v_x_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_3382__boxed_1040_: usize = 0;
    let mut v_x_3383__boxed_1041_: usize = 0;
    let mut v_res_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_3382__boxed_1040_ = crate::leanh::lean_unbox_usize(v_x_1036_);
    crate::leanh::lean_dec(v_x_1036_);
    v_x_3383__boxed_1041_ = crate::leanh::lean_unbox_usize(v_x_1037_);
    crate::leanh::lean_dec(v_x_1037_);
    v_res_1042_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2(v_00_u03b2_1034_, v_x_1035_, v_x_3382__boxed_1040_, v_x_3383__boxed_1041_, v_x_1038_, v_x_1039_);
    return v_res_1042_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1043_: *mut crate::leanh::LeanObject,
    mut v_n_1044_: *mut crate::leanh::LeanObject,
    mut v_k_1045_: *mut crate::leanh::LeanObject,
    mut v_v_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1047_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1044_, v_k_1045_, v_v_1046_);
    return v___x_1047_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_1048_: *mut crate::leanh::LeanObject,
    mut v_depth_1049_: usize,
    mut v_keys_1050_: *mut crate::leanh::LeanObject,
    mut v_vals_1051_: *mut crate::leanh::LeanObject,
    mut v_heq_1052_: *mut crate::leanh::LeanObject,
    mut v_i_1053_: *mut crate::leanh::LeanObject,
    mut v_entries_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1055_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1049_, v_keys_1050_, v_vals_1051_, v_i_1053_, v_entries_1054_);
    return v___x_1055_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_1056_: *mut crate::leanh::LeanObject,
    mut v_depth_1057_: *mut crate::leanh::LeanObject,
    mut v_keys_1058_: *mut crate::leanh::LeanObject,
    mut v_vals_1059_: *mut crate::leanh::LeanObject,
    mut v_heq_1060_: *mut crate::leanh::LeanObject,
    mut v_i_1061_: *mut crate::leanh::LeanObject,
    mut v_entries_1062_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1063_: usize = 0;
    let mut v_res_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1063_ = crate::leanh::lean_unbox_usize(v_depth_1057_);
    crate::leanh::lean_dec(v_depth_1057_);
    v_res_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1056_, v_depth_boxed_1063_, v_keys_1058_, v_vals_1059_, v_heq_1060_, v_i_1061_, v_entries_1062_);
    crate::leanh::lean_dec_ref(v_vals_1059_);
    crate::leanh::lean_dec_ref(v_keys_1058_);
    return v_res_1064_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1065_: *mut crate::leanh::LeanObject,
    mut v_x_1066_: *mut crate::leanh::LeanObject,
    mut v_x_1067_: *mut crate::leanh::LeanObject,
    mut v_x_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_markAccessible_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1066_, v_x_1067_, v_x_1068_, v_x_1069_);
    return v___x_1070_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(
    mut v_as_1071_: *mut crate::leanh::LeanObject,
    mut v_sz_1072_: usize,
    mut v_i_1073_: usize,
    mut v_b_1074_: *mut crate::leanh::LeanObject,
    mut v___y_1075_: *mut crate::leanh::LeanObject,
    mut v___y_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: usize = 0;
    let mut v___x_1087_: usize = 0;
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1098_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1079_ = lean_usize_dec_lt(v_i_1073_, v_sz_1072_);
                if v___x_1079_ == 0 {
                    v___x_1080_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1080_, 0, v_b_1074_);
                    return v___x_1080_;
                } else {
                    v_a_1081_ = lean_array_uget_borrowed(v_as_1071_, v_i_1073_);
                    crate::leanh::lean_inc(v_a_1081_);
                    v___x_1082_ = l_Lean_FVarId_getDecl___redArg(
                        v_a_1081_,
                        v___y_1075_,
                        v___y_1076_,
                        v___y_1077_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1082_) == 0 {
                        v_a_1083_ = crate::leanh::lean_ctor_get(v___x_1082_, 0);
                        crate::leanh::lean_inc(v_a_1083_);
                        crate::leanh::lean_dec_ref_known(v___x_1082_, 1);
                        v___x_1089_ = l_Lean_LocalDecl_isAuxDecl(v_a_1083_);
                        crate::leanh::lean_dec(v_a_1083_);
                        if v___x_1089_ == 0 {
                            crate::leanh::lean_inc(v_a_1081_);
                            v___x_1090_ = lean_array_push(v_b_1074_, v_a_1081_);
                            v_a_1085_ = v___x_1090_;
                            state = 1;
                            continue;
                        } else {
                            v_a_1085_ = v_b_1074_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_b_1074_);
                        v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1082_, 0);
                        v_isSharedCheck_1098_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1082_)) as u8;
                        if v_isSharedCheck_1098_ == 0 {
                            v___x_1093_ = v___x_1082_;
                            v_isShared_1094_ = v_isSharedCheck_1098_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1091_);
                            crate::leanh::lean_dec(v___x_1082_);
                            v___x_1093_ = crate::leanh::lean_box(0);
                            v_isShared_1094_ = v_isSharedCheck_1098_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1086_ = 1usize;
                v___x_1087_ = lean_usize_add(v_i_1073_, v___x_1086_);
                v_i_1073_ = v___x_1087_;
                v_b_1074_ = v_a_1085_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1094_ == 0 {
                    v___x_1096_ = v___x_1093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1097_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1097_, 0, v_a_1091_);
                    v___x_1096_ = v_reuseFailAlloc_1097_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1096_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg___boxed(
    mut v_as_1099_: *mut crate::leanh::LeanObject,
    mut v_sz_1100_: *mut crate::leanh::LeanObject,
    mut v_i_1101_: *mut crate::leanh::LeanObject,
    mut v_b_1102_: *mut crate::leanh::LeanObject,
    mut v___y_1103_: *mut crate::leanh::LeanObject,
    mut v___y_1104_: *mut crate::leanh::LeanObject,
    mut v___y_1105_: *mut crate::leanh::LeanObject,
    mut v___y_1106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1107_: usize = 0;
    let mut v_i_boxed_1108_: usize = 0;
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1107_ = crate::leanh::lean_unbox_usize(v_sz_1100_);
    crate::leanh::lean_dec(v_sz_1100_);
    v_i_boxed_1108_ = crate::leanh::lean_unbox_usize(v_i_1101_);
    crate::leanh::lean_dec(v_i_1101_);
    v_res_1109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_1099_, v_sz_boxed_1107_, v_i_boxed_1108_, v_b_1102_, v___y_1103_, v___y_1104_, v___y_1105_);
    crate::leanh::lean_dec(v___y_1105_);
    crate::leanh::lean_dec_ref(v___y_1104_);
    crate::leanh::lean_dec_ref(v___y_1103_);
    crate::leanh::lean_dec_ref(v_as_1099_);
    return v_res_1109_;
}
pub unsafe fn l_Lean_MVarId_revertAll___lam__0(
    mut v_mvarId_1112_: *mut crate::leanh::LeanObject,
    mut v___x_1113_: *mut crate::leanh::LeanObject,
    mut v___y_1114_: *mut crate::leanh::LeanObject,
    mut v___y_1115_: *mut crate::leanh::LeanObject,
    mut v___y_1116_: *mut crate::leanh::LeanObject,
    mut v___y_1117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1123_: usize = 0;
    let mut v___x_1124_: usize = 0;
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: u8 = 0;
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1134_: u8 = 0;
    let mut v_snd_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1139_: u8 = 0;
    let mut v_a_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1143_: u8 = 0;
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1147_: u8 = 0;
    let mut v_a_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1151_: u8 = 0;
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1155_: u8 = 0;
    let mut v_a_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1159_: u8 = 0;
    let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1163_: u8 = 0;
    let mut v_a_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1167_: u8 = 0;
    let mut v___x_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1171_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1112_);
                v___x_1119_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1112_,
                    v___x_1113_,
                    v___y_1114_,
                    v___y_1115_,
                    v___y_1116_,
                    v___y_1117_,
                );
                if crate::leanh::lean_obj_tag(v___x_1119_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1119_, 1);
                    v_lctx_1120_ = crate::leanh::lean_ctor_get(v___y_1114_, 2);
                    v___x_1121_ = l_Lean_MVarId_revertAll___lam__0___closed__0;
                    v___x_1122_ = l_Lean_LocalContext_getFVarIds(v_lctx_1120_);
                    v_sz_1123_ = lean_array_size(v___x_1122_);
                    v___x_1124_ = 0usize;
                    v___x_1125_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v___x_1122_, v_sz_1123_, v___x_1124_, v___x_1121_, v___y_1114_, v___y_1116_, v___y_1117_);
                    crate::leanh::lean_dec_ref(v___x_1122_);
                    if crate::leanh::lean_obj_tag(v___x_1125_) == 0 {
                        v_a_1126_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                        crate::leanh::lean_inc(v_a_1126_);
                        crate::leanh::lean_dec_ref_known(v___x_1125_, 1);
                        v___x_1127_ = 0;
                        crate::leanh::lean_inc(v_mvarId_1112_);
                        v___x_1128_ = l_Lean_MVarId_setKind___redArg(
                            v_mvarId_1112_,
                            v___x_1127_,
                            v___y_1115_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1128_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1128_, 1);
                            v___x_1129_ = 1;
                            v___x_1130_ = l_Lean_MVarId_revert(
                                v_mvarId_1112_,
                                v_a_1126_,
                                v___x_1129_,
                                v___x_1129_,
                                v___y_1114_,
                                v___y_1115_,
                                v___y_1116_,
                                v___y_1117_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_1130_) == 0 {
                                v_a_1131_ = crate::leanh::lean_ctor_get(v___x_1130_, 0);
                                v_isSharedCheck_1139_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1130_)) as u8;
                                if v_isSharedCheck_1139_ == 0 {
                                    v___x_1133_ = v___x_1130_;
                                    v_isShared_1134_ = v_isSharedCheck_1139_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1131_);
                                    crate::leanh::lean_dec(v___x_1130_);
                                    v___x_1133_ = crate::leanh::lean_box(0);
                                    v_isShared_1134_ = v_isSharedCheck_1139_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                v_a_1140_ = crate::leanh::lean_ctor_get(v___x_1130_, 0);
                                v_isSharedCheck_1147_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1130_)) as u8;
                                if v_isSharedCheck_1147_ == 0 {
                                    v___x_1142_ = v___x_1130_;
                                    v_isShared_1143_ = v_isSharedCheck_1147_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1140_);
                                    crate::leanh::lean_dec(v___x_1130_);
                                    v___x_1142_ = crate::leanh::lean_box(0);
                                    v_isShared_1143_ = v_isSharedCheck_1147_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1126_);
                            crate::leanh::lean_dec(v_mvarId_1112_);
                            v_a_1148_ = crate::leanh::lean_ctor_get(v___x_1128_, 0);
                            v_isSharedCheck_1155_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1128_)) as u8;
                            if v_isSharedCheck_1155_ == 0 {
                                v___x_1150_ = v___x_1128_;
                                v_isShared_1151_ = v_isSharedCheck_1155_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1148_);
                                crate::leanh::lean_dec(v___x_1128_);
                                v___x_1150_ = crate::leanh::lean_box(0);
                                v_isShared_1151_ = v_isSharedCheck_1155_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_1112_);
                        v_a_1156_ = crate::leanh::lean_ctor_get(v___x_1125_, 0);
                        v_isSharedCheck_1163_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1125_)) as u8;
                        if v_isSharedCheck_1163_ == 0 {
                            v___x_1158_ = v___x_1125_;
                            v_isShared_1159_ = v_isSharedCheck_1163_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1156_);
                            crate::leanh::lean_dec(v___x_1125_);
                            v___x_1158_ = crate::leanh::lean_box(0);
                            v_isShared_1159_ = v_isSharedCheck_1163_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1112_);
                    v_a_1164_ = crate::leanh::lean_ctor_get(v___x_1119_, 0);
                    v_isSharedCheck_1171_ = (!crate::leanh::lean_is_exclusive(v___x_1119_)) as u8;
                    if v_isSharedCheck_1171_ == 0 {
                        v___x_1166_ = v___x_1119_;
                        v_isShared_1167_ = v_isSharedCheck_1171_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1164_);
                        crate::leanh::lean_dec(v___x_1119_);
                        v___x_1166_ = crate::leanh::lean_box(0);
                        v_isShared_1167_ = v_isSharedCheck_1171_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_snd_1135_ = crate::leanh::lean_ctor_get(v_a_1131_, 1);
                crate::leanh::lean_inc(v_snd_1135_);
                crate::leanh::lean_dec(v_a_1131_);
                if v_isShared_1134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1133_, 0, v_snd_1135_);
                    v___x_1137_ = v___x_1133_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1138_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1138_, 0, v_snd_1135_);
                    v___x_1137_ = v_reuseFailAlloc_1138_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1137_;
            }
            3 => {
                if v_isShared_1143_ == 0 {
                    v___x_1145_ = v___x_1142_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_a_1140_);
                    v___x_1145_ = v_reuseFailAlloc_1146_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1145_;
            }
            5 => {
                if v_isShared_1151_ == 0 {
                    v___x_1153_ = v___x_1150_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_a_1148_);
                    v___x_1153_ = v_reuseFailAlloc_1154_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1153_;
            }
            7 => {
                if v_isShared_1159_ == 0 {
                    v___x_1161_ = v___x_1158_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1162_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1162_, 0, v_a_1156_);
                    v___x_1161_ = v_reuseFailAlloc_1162_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1161_;
            }
            9 => {
                if v_isShared_1167_ == 0 {
                    v___x_1169_ = v___x_1166_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1170_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_a_1164_);
                    v___x_1169_ = v_reuseFailAlloc_1170_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1169_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_revertAll___lam__0___boxed(
    mut v_mvarId_1172_: *mut crate::leanh::LeanObject,
    mut v___x_1173_: *mut crate::leanh::LeanObject,
    mut v___y_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1179_ = l_Lean_MVarId_revertAll___lam__0(
        v_mvarId_1172_,
        v___x_1173_,
        v___y_1174_,
        v___y_1175_,
        v___y_1176_,
        v___y_1177_,
    );
    crate::leanh::lean_dec(v___y_1177_);
    crate::leanh::lean_dec_ref(v___y_1176_);
    crate::leanh::lean_dec(v___y_1175_);
    crate::leanh::lean_dec_ref(v___y_1174_);
    return v_res_1179_;
}
pub unsafe fn l_Lean_MVarId_revertAll(
    mut v_mvarId_1183_: *mut crate::leanh::LeanObject,
    mut v_a_1184_: *mut crate::leanh::LeanObject,
    mut v_a_1185_: *mut crate::leanh::LeanObject,
    mut v_a_1186_: *mut crate::leanh::LeanObject,
    mut v_a_1187_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1189_ = l_Lean_MVarId_revertAll___closed__1;
    crate::leanh::lean_inc(v_mvarId_1183_);
    v___f_1190_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_revertAll___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1190_, 0, v_mvarId_1183_);
    crate::leanh::lean_closure_set(v___f_1190_, 1, v___x_1189_);
    v___x_1191_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_markAccessible_spec__2___redArg(
        v_mvarId_1183_,
        v___f_1190_,
        v_a_1184_,
        v_a_1185_,
        v_a_1186_,
        v_a_1187_,
    );
    return v___x_1191_;
}
pub unsafe fn l_Lean_MVarId_revertAll___boxed(
    mut v_mvarId_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
    mut v_a_1194_: *mut crate::leanh::LeanObject,
    mut v_a_1195_: *mut crate::leanh::LeanObject,
    mut v_a_1196_: *mut crate::leanh::LeanObject,
    mut v_a_1197_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1198_ =
        l_Lean_MVarId_revertAll(v_mvarId_1192_, v_a_1193_, v_a_1194_, v_a_1195_, v_a_1196_);
    crate::leanh::lean_dec(v_a_1196_);
    crate::leanh::lean_dec_ref(v_a_1195_);
    crate::leanh::lean_dec(v_a_1194_);
    crate::leanh::lean_dec_ref(v_a_1193_);
    return v_res_1198_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(
    mut v_as_1199_: *mut crate::leanh::LeanObject,
    mut v_sz_1200_: usize,
    mut v_i_1201_: usize,
    mut v_b_1202_: *mut crate::leanh::LeanObject,
    mut v___y_1203_: *mut crate::leanh::LeanObject,
    mut v___y_1204_: *mut crate::leanh::LeanObject,
    mut v___y_1205_: *mut crate::leanh::LeanObject,
    mut v___y_1206_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1208_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___redArg(v_as_1199_, v_sz_1200_, v_i_1201_, v_b_1202_, v___y_1203_, v___y_1205_, v___y_1206_);
    return v___x_1208_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0___boxed(
    mut v_as_1209_: *mut crate::leanh::LeanObject,
    mut v_sz_1210_: *mut crate::leanh::LeanObject,
    mut v_i_1211_: *mut crate::leanh::LeanObject,
    mut v_b_1212_: *mut crate::leanh::LeanObject,
    mut v___y_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1218_: usize = 0;
    let mut v_i_boxed_1219_: usize = 0;
    let mut v_res_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1218_ = crate::leanh::lean_unbox_usize(v_sz_1210_);
    crate::leanh::lean_dec(v_sz_1210_);
    v_i_boxed_1219_ = crate::leanh::lean_unbox_usize(v_i_1211_);
    crate::leanh::lean_dec(v_i_1211_);
    v_res_1220_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_MVarId_revertAll_spec__0(v_as_1209_, v_sz_boxed_1218_, v_i_boxed_1219_, v_b_1212_, v___y_1213_, v___y_1214_, v___y_1215_, v___y_1216_);
    crate::leanh::lean_dec(v___y_1216_);
    crate::leanh::lean_dec_ref(v___y_1215_);
    crate::leanh::lean_dec(v___y_1214_);
    crate::leanh::lean_dec_ref(v___y_1213_);
    crate::leanh::lean_dec_ref(v_as_1209_);
    return v_res_1220_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_RevertAll(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_RevertAll(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Revert(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_RevertAll(builtin);
}

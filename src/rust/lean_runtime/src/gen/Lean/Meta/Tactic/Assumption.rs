// Lean compiler output
// Module: Lean.Meta.Tactic.Assumption
// Imports: Lean.Meta.Tactic.Util
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::LocalContext::{
    l_Lean_LocalDecl_fvarId, l_Lean_LocalDecl_isImplementationDetail, l_Lean_LocalDecl_type,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::Tactic::Util::{
    initialize_Lean_Meta_Tactic_Util, l_Lean_MVarId_checkNotAssigned, l_Lean_MVarId_getType,
    l_Lean_Meta_throwTacticEx___redArg, runtime_initialize_Lean_Meta_Tactic_Util,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub,
};
use crate::lean_imports_rs::Init::System::ST::{lean_st_ref_set, lean_st_ref_take};
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_MVarId_assumptionCore___closed__0_value: crate::leanh::LeanStringObject<11> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [97, 115, 115, 117, 109, 112, 116, 105, 111, 110, 0],
    };
static mut l_Lean_MVarId_assumptionCore___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assumptionCore___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_MVarId_assumptionCore___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_MVarId_assumptionCore___closed__0_value)
                as *mut crate::leanh::LeanObject,
            11851244492489364017 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_MVarId_assumptionCore___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_MVarId_assumptionCore___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_type_633_: *mut crate::leanh::LeanObject,
    mut v_as_634_: *mut crate::leanh::LeanObject,
    mut v_i_635_: *mut crate::leanh::LeanObject,
    mut v___y_636_: *mut crate::leanh::LeanObject,
    mut v___y_637_: *mut crate::leanh::LeanObject,
    mut v___y_638_: *mut crate::leanh::LeanObject,
    mut v___y_639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_642_: u8 = 0;
    let mut v___x_643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_652_: u8 = 0;
    let mut v___x_653_: u8 = 0;
    let mut v___x_654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_659_: u8 = 0;
    let mut v___x_660_: u8 = 0;
    let mut v___x_662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_669_: u8 = 0;
    let mut v_a_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_673_: u8 = 0;
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_677_: u8 = 0;
    let mut v_isSharedCheck_679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_641_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_642_ = lean_nat_dec_eq(v_i_635_, v_zero_641_);
                if v_isZero_642_ == 1 {
                    crate::leanh::lean_dec(v_i_635_);
                    crate::leanh::lean_dec_ref(v_type_633_);
                    v___x_643_ = crate::leanh::lean_box(0);
                    v___x_644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_644_, 0, v___x_643_);
                    return v___x_644_;
                } else {
                    v_one_645_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_646_ = lean_nat_sub(v_i_635_, v_one_645_);
                    crate::leanh::lean_dec(v_i_635_);
                    v___x_647_ = lean_array_fget(v_as_634_, v_n_646_);
                    if crate::leanh::lean_obj_tag(v___x_647_) == 0 {
                        v_i_635_ = v_n_646_;
                        state = 0;
                        continue;
                    } else {
                        v_val_649_ = crate::leanh::lean_ctor_get(v___x_647_, 0);
                        v_isSharedCheck_679_ = (!crate::leanh::lean_is_exclusive(v___x_647_)) as u8;
                        if v_isSharedCheck_679_ == 0 {
                            v___x_651_ = v___x_647_;
                            v_isShared_652_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_649_);
                            crate::leanh::lean_dec(v___x_647_);
                            v___x_651_ = crate::leanh::lean_box(0);
                            v_isShared_652_ = v_isSharedCheck_679_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_653_ = l_Lean_LocalDecl_isImplementationDetail(v_val_649_);
                if v___x_653_ == 0 {
                    v___x_654_ = l_Lean_LocalDecl_type(v_val_649_);
                    crate::leanh::lean_inc_ref(v_type_633_);
                    v___x_655_ = l_Lean_Meta_isExprDefEq(
                        v_type_633_,
                        v___x_654_,
                        v___y_636_,
                        v___y_637_,
                        v___y_638_,
                        v___y_639_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_655_) == 0 {
                        v_a_656_ = crate::leanh::lean_ctor_get(v___x_655_, 0);
                        v_isSharedCheck_669_ = (!crate::leanh::lean_is_exclusive(v___x_655_)) as u8;
                        if v_isSharedCheck_669_ == 0 {
                            v___x_658_ = v___x_655_;
                            v_isShared_659_ = v_isSharedCheck_669_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_656_);
                            crate::leanh::lean_dec(v___x_655_);
                            v___x_658_ = crate::leanh::lean_box(0);
                            v_isShared_659_ = v_isSharedCheck_669_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_651_);
                        crate::leanh::lean_dec(v_val_649_);
                        crate::leanh::lean_dec(v_n_646_);
                        crate::leanh::lean_dec_ref(v_type_633_);
                        v_a_670_ = crate::leanh::lean_ctor_get(v___x_655_, 0);
                        v_isSharedCheck_677_ = (!crate::leanh::lean_is_exclusive(v___x_655_)) as u8;
                        if v_isSharedCheck_677_ == 0 {
                            v___x_672_ = v___x_655_;
                            v_isShared_673_ = v_isSharedCheck_677_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_670_);
                            crate::leanh::lean_dec(v___x_655_);
                            v___x_672_ = crate::leanh::lean_box(0);
                            v_isShared_673_ = v_isSharedCheck_677_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_651_);
                    crate::leanh::lean_dec(v_val_649_);
                    v_i_635_ = v_n_646_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                v___x_660_ = (crate::leanh::lean_unbox(v_a_656_) as u8);
                crate::leanh::lean_dec(v_a_656_);
                if v___x_660_ == 0 {
                    crate::leanh::lean_del_object(v___x_658_);
                    crate::leanh::lean_del_object(v___x_651_);
                    crate::leanh::lean_dec(v_val_649_);
                    v_i_635_ = v_n_646_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_n_646_);
                    crate::leanh::lean_dec_ref(v_type_633_);
                    v___x_662_ = l_Lean_LocalDecl_fvarId(v_val_649_);
                    crate::leanh::lean_dec(v_val_649_);
                    if v_isShared_652_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_651_, 0, v___x_662_);
                        v___x_664_ = v___x_651_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_668_, 0, v___x_662_);
                        v___x_664_ = v_reuseFailAlloc_668_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_659_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_658_, 0, v___x_664_);
                    v___x_666_ = v___x_658_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_664_);
                    v___x_666_ = v_reuseFailAlloc_667_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_666_;
            }
            5 => {
                if v_isShared_673_ == 0 {
                    v___x_675_ = v___x_672_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_676_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_676_, 0, v_a_670_);
                    v___x_675_ = v_reuseFailAlloc_676_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_675_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_type_680_: *mut crate::leanh::LeanObject,
    mut v_as_681_: *mut crate::leanh::LeanObject,
    mut v_i_682_: *mut crate::leanh::LeanObject,
    mut v___y_683_: *mut crate::leanh::LeanObject,
    mut v___y_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_688_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_680_, v_as_681_, v_i_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_);
    crate::leanh::lean_dec(v___y_686_);
    crate::leanh::lean_dec_ref(v___y_685_);
    crate::leanh::lean_dec(v___y_684_);
    crate::leanh::lean_dec_ref(v___y_683_);
    crate::leanh::lean_dec_ref(v_as_681_);
    return v_res_688_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_type_689_: *mut crate::leanh::LeanObject,
    mut v_as_690_: *mut crate::leanh::LeanObject,
    mut v_i_691_: *mut crate::leanh::LeanObject,
    mut v___y_692_: *mut crate::leanh::LeanObject,
    mut v___y_693_: *mut crate::leanh::LeanObject,
    mut v___y_694_: *mut crate::leanh::LeanObject,
    mut v___y_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_698_: u8 = 0;
    let mut v___x_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_697_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_698_ = lean_nat_dec_eq(v_i_691_, v_zero_697_);
                if v_isZero_698_ == 1 {
                    crate::leanh::lean_dec(v_i_691_);
                    crate::leanh::lean_dec_ref(v_type_689_);
                    v___x_699_ = crate::leanh::lean_box(0);
                    v___x_700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_700_, 0, v___x_699_);
                    return v___x_700_;
                } else {
                    v_one_701_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_702_ = lean_nat_sub(v_i_691_, v_one_701_);
                    crate::leanh::lean_dec(v_i_691_);
                    v___x_703_ = lean_array_fget_borrowed(v_as_690_, v_n_702_);
                    crate::leanh::lean_inc_ref(v_type_689_);
                    v___x_704_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_689_, v___x_703_, v___y_692_, v___y_693_, v___y_694_, v___y_695_);
                    if crate::leanh::lean_obj_tag(v___x_704_) == 0 {
                        v_a_705_ = crate::leanh::lean_ctor_get(v___x_704_, 0);
                        crate::leanh::lean_inc(v_a_705_);
                        if crate::leanh::lean_obj_tag(v_a_705_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_704_, 1);
                            v_i_691_ = v_n_702_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v_a_705_, 1);
                            crate::leanh::lean_dec(v_n_702_);
                            crate::leanh::lean_dec_ref(v_type_689_);
                            return v___x_704_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_n_702_);
                        crate::leanh::lean_dec_ref(v_type_689_);
                        return v___x_704_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(
    mut v_type_707_: *mut crate::leanh::LeanObject,
    mut v_x_708_: *mut crate::leanh::LeanObject,
    mut v___y_709_: *mut crate::leanh::LeanObject,
    mut v___y_710_: *mut crate::leanh::LeanObject,
    mut v___y_711_: *mut crate::leanh::LeanObject,
    mut v___y_712_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_708_) == 0 {
        let mut v_cs_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_cs_714_ = crate::leanh::lean_ctor_get(v_x_708_, 0);
        v___x_715_ = lean_array_get_size(v_cs_714_);
        v___x_716_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_707_, v_cs_714_, v___x_715_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
        return v___x_716_;
    } else {
        let mut v_vs_717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_717_ = crate::leanh::lean_ctor_get(v_x_708_, 0);
        v___x_718_ = lean_array_get_size(v_vs_717_);
        v___x_719_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_707_, v_vs_717_, v___x_718_, v___y_709_, v___y_710_, v___y_711_, v___y_712_);
        return v___x_719_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2___boxed(
    mut v_type_720_: *mut crate::leanh::LeanObject,
    mut v_x_721_: *mut crate::leanh::LeanObject,
    mut v___y_722_: *mut crate::leanh::LeanObject,
    mut v___y_723_: *mut crate::leanh::LeanObject,
    mut v___y_724_: *mut crate::leanh::LeanObject,
    mut v___y_725_: *mut crate::leanh::LeanObject,
    mut v___y_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_727_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_720_, v_x_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
    crate::leanh::lean_dec(v___y_725_);
    crate::leanh::lean_dec_ref(v___y_724_);
    crate::leanh::lean_dec(v___y_723_);
    crate::leanh::lean_dec_ref(v___y_722_);
    crate::leanh::lean_dec_ref(v_x_721_);
    return v_res_727_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg___boxed(
    mut v_type_728_: *mut crate::leanh::LeanObject,
    mut v_as_729_: *mut crate::leanh::LeanObject,
    mut v_i_730_: *mut crate::leanh::LeanObject,
    mut v___y_731_: *mut crate::leanh::LeanObject,
    mut v___y_732_: *mut crate::leanh::LeanObject,
    mut v___y_733_: *mut crate::leanh::LeanObject,
    mut v___y_734_: *mut crate::leanh::LeanObject,
    mut v___y_735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_736_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_728_, v_as_729_, v_i_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_);
    crate::leanh::lean_dec(v___y_734_);
    crate::leanh::lean_dec_ref(v___y_733_);
    crate::leanh::lean_dec(v___y_732_);
    crate::leanh::lean_dec_ref(v___y_731_);
    crate::leanh::lean_dec_ref(v_as_729_);
    return v_res_736_;
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(
    mut v_type_737_: *mut crate::leanh::LeanObject,
    mut v_t_738_: *mut crate::leanh::LeanObject,
    mut v___y_739_: *mut crate::leanh::LeanObject,
    mut v___y_740_: *mut crate::leanh::LeanObject,
    mut v___y_741_: *mut crate::leanh::LeanObject,
    mut v___y_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_root_744_ = crate::leanh::lean_ctor_get(v_t_738_, 0);
    v_tail_745_ = crate::leanh::lean_ctor_get(v_t_738_, 1);
    v___x_746_ = lean_array_get_size(v_tail_745_);
    crate::leanh::lean_inc_ref(v_type_737_);
    v___x_747_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_737_, v_tail_745_, v___x_746_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
    if crate::leanh::lean_obj_tag(v___x_747_) == 0 {
        let mut v_a_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_a_748_ = crate::leanh::lean_ctor_get(v___x_747_, 0);
        crate::leanh::lean_inc(v_a_748_);
        if crate::leanh::lean_obj_tag(v_a_748_) == 0 {
            let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_747_, 1);
            v___x_749_ = l_Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2(v_type_737_, v_root_744_, v___y_739_, v___y_740_, v___y_741_, v___y_742_);
            return v___x_749_;
        } else {
            crate::leanh::lean_dec_ref_known(v_a_748_, 1);
            crate::leanh::lean_dec_ref(v_type_737_);
            return v___x_747_;
        }
    } else {
        crate::leanh::lean_dec_ref(v_type_737_);
        return v___x_747_;
    }
}
pub unsafe fn l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0___boxed(
    mut v_type_750_: *mut crate::leanh::LeanObject,
    mut v_t_751_: *mut crate::leanh::LeanObject,
    mut v___y_752_: *mut crate::leanh::LeanObject,
    mut v___y_753_: *mut crate::leanh::LeanObject,
    mut v___y_754_: *mut crate::leanh::LeanObject,
    mut v___y_755_: *mut crate::leanh::LeanObject,
    mut v___y_756_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_757_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_750_, v_t_751_, v___y_752_, v___y_753_, v___y_754_, v___y_755_);
    crate::leanh::lean_dec(v___y_755_);
    crate::leanh::lean_dec_ref(v___y_754_);
    crate::leanh::lean_dec(v___y_753_);
    crate::leanh::lean_dec_ref(v___y_752_);
    crate::leanh::lean_dec_ref(v_t_751_);
    return v_res_757_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(
    mut v_type_758_: *mut crate::leanh::LeanObject,
    mut v_lctx_759_: *mut crate::leanh::LeanObject,
    mut v___y_760_: *mut crate::leanh::LeanObject,
    mut v___y_761_: *mut crate::leanh::LeanObject,
    mut v___y_762_: *mut crate::leanh::LeanObject,
    mut v___y_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decls_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_decls_765_ = crate::leanh::lean_ctor_get(v_lctx_759_, 1);
    v___x_766_ = l_Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0(v_type_758_, v_decls_765_, v___y_760_, v___y_761_, v___y_762_, v___y_763_);
    return v___x_766_;
}
pub unsafe fn l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0___boxed(
    mut v_type_767_: *mut crate::leanh::LeanObject,
    mut v_lctx_768_: *mut crate::leanh::LeanObject,
    mut v___y_769_: *mut crate::leanh::LeanObject,
    mut v___y_770_: *mut crate::leanh::LeanObject,
    mut v___y_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
    mut v___y_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ =
        l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(
            v_type_767_,
            v_lctx_768_,
            v___y_769_,
            v___y_770_,
            v___y_771_,
            v___y_772_,
        );
    crate::leanh::lean_dec(v___y_772_);
    crate::leanh::lean_dec_ref(v___y_771_);
    crate::leanh::lean_dec(v___y_770_);
    crate::leanh::lean_dec_ref(v___y_769_);
    crate::leanh::lean_dec_ref(v_lctx_768_);
    return v_res_774_;
}
pub unsafe fn l_Lean_Meta_findLocalDeclWithType_x3f(
    mut v_type_775_: *mut crate::leanh::LeanObject,
    mut v_a_776_: *mut crate::leanh::LeanObject,
    mut v_a_777_: *mut crate::leanh::LeanObject,
    mut v_a_778_: *mut crate::leanh::LeanObject,
    mut v_a_779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lctx_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lctx_781_ = crate::leanh::lean_ctor_get(v_a_776_, 2);
    v___x_782_ =
        l_Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0(
            v_type_775_,
            v_lctx_781_,
            v_a_776_,
            v_a_777_,
            v_a_778_,
            v_a_779_,
        );
    return v___x_782_;
}
pub unsafe fn l_Lean_Meta_findLocalDeclWithType_x3f___boxed(
    mut v_type_783_: *mut crate::leanh::LeanObject,
    mut v_a_784_: *mut crate::leanh::LeanObject,
    mut v_a_785_: *mut crate::leanh::LeanObject,
    mut v_a_786_: *mut crate::leanh::LeanObject,
    mut v_a_787_: *mut crate::leanh::LeanObject,
    mut v_a_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_789_ =
        l_Lean_Meta_findLocalDeclWithType_x3f(v_type_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_);
    crate::leanh::lean_dec(v_a_787_);
    crate::leanh::lean_dec_ref(v_a_786_);
    crate::leanh::lean_dec(v_a_785_);
    crate::leanh::lean_dec_ref(v_a_784_);
    return v_res_789_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(
    mut v_type_790_: *mut crate::leanh::LeanObject,
    mut v_as_791_: *mut crate::leanh::LeanObject,
    mut v_i_792_: *mut crate::leanh::LeanObject,
    mut v_a_793_: *mut crate::leanh::LeanObject,
    mut v___y_794_: *mut crate::leanh::LeanObject,
    mut v___y_795_: *mut crate::leanh::LeanObject,
    mut v___y_796_: *mut crate::leanh::LeanObject,
    mut v___y_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_799_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___redArg(v_type_790_, v_as_791_, v_i_792_, v___y_794_, v___y_795_, v___y_796_, v___y_797_);
    return v___x_799_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_type_800_: *mut crate::leanh::LeanObject,
    mut v_as_801_: *mut crate::leanh::LeanObject,
    mut v_i_802_: *mut crate::leanh::LeanObject,
    mut v_a_803_: *mut crate::leanh::LeanObject,
    mut v___y_804_: *mut crate::leanh::LeanObject,
    mut v___y_805_: *mut crate::leanh::LeanObject,
    mut v___y_806_: *mut crate::leanh::LeanObject,
    mut v___y_807_: *mut crate::leanh::LeanObject,
    mut v___y_808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_809_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__1(v_type_800_, v_as_801_, v_i_802_, v_a_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
    crate::leanh::lean_dec(v___y_807_);
    crate::leanh::lean_dec_ref(v___y_806_);
    crate::leanh::lean_dec(v___y_805_);
    crate::leanh::lean_dec_ref(v___y_804_);
    crate::leanh::lean_dec_ref(v_as_801_);
    return v_res_809_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(
    mut v_type_810_: *mut crate::leanh::LeanObject,
    mut v_as_811_: *mut crate::leanh::LeanObject,
    mut v_i_812_: *mut crate::leanh::LeanObject,
    mut v_a_813_: *mut crate::leanh::LeanObject,
    mut v___y_814_: *mut crate::leanh::LeanObject,
    mut v___y_815_: *mut crate::leanh::LeanObject,
    mut v___y_816_: *mut crate::leanh::LeanObject,
    mut v___y_817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___redArg(v_type_810_, v_as_811_, v_i_812_, v___y_814_, v___y_815_, v___y_816_, v___y_817_);
    return v___x_819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_type_820_: *mut crate::leanh::LeanObject,
    mut v_as_821_: *mut crate::leanh::LeanObject,
    mut v_i_822_: *mut crate::leanh::LeanObject,
    mut v_a_823_: *mut crate::leanh::LeanObject,
    mut v___y_824_: *mut crate::leanh::LeanObject,
    mut v___y_825_: *mut crate::leanh::LeanObject,
    mut v___y_826_: *mut crate::leanh::LeanObject,
    mut v___y_827_: *mut crate::leanh::LeanObject,
    mut v___y_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_829_ = l___private_Init_Data_Array_Basic_0__Array_findSomeRevM_x3f_find___at___00Lean_PersistentArray_findSomeRevMAux___at___00Lean_PersistentArray_findSomeRevM_x3f___at___00Lean_LocalContext_findDeclRevM_x3f___at___00Lean_Meta_findLocalDeclWithType_x3f_spec__0_spec__0_spec__2_spec__3(v_type_820_, v_as_821_, v_i_822_, v_a_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_);
    crate::leanh::lean_dec(v___y_827_);
    crate::leanh::lean_dec_ref(v___y_826_);
    crate::leanh::lean_dec(v___y_825_);
    crate::leanh::lean_dec_ref(v___y_824_);
    crate::leanh::lean_dec_ref(v_as_821_);
    return v_res_829_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(
    mut v_mvarId_830_: *mut crate::leanh::LeanObject,
    mut v_x_831_: *mut crate::leanh::LeanObject,
    mut v___y_832_: *mut crate::leanh::LeanObject,
    mut v___y_833_: *mut crate::leanh::LeanObject,
    mut v___y_834_: *mut crate::leanh::LeanObject,
    mut v___y_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_841_: u8 = 0;
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_845_: u8 = 0;
    let mut v_a_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_849_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    crate::leanh::lean_box(0),
                    v_mvarId_830_,
                    v_x_831_,
                    v___y_832_,
                    v___y_833_,
                    v___y_834_,
                    v___y_835_,
                );
                if crate::leanh::lean_obj_tag(v___x_837_) == 0 {
                    v_a_838_ = crate::leanh::lean_ctor_get(v___x_837_, 0);
                    v_isSharedCheck_845_ = (!crate::leanh::lean_is_exclusive(v___x_837_)) as u8;
                    if v_isSharedCheck_845_ == 0 {
                        v___x_840_ = v___x_837_;
                        v_isShared_841_ = v_isSharedCheck_845_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_838_);
                        crate::leanh::lean_dec(v___x_837_);
                        v___x_840_ = crate::leanh::lean_box(0);
                        v_isShared_841_ = v_isSharedCheck_845_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_846_ = crate::leanh::lean_ctor_get(v___x_837_, 0);
                    v_isSharedCheck_853_ = (!crate::leanh::lean_is_exclusive(v___x_837_)) as u8;
                    if v_isSharedCheck_853_ == 0 {
                        v___x_848_ = v___x_837_;
                        v_isShared_849_ = v_isSharedCheck_853_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_846_);
                        crate::leanh::lean_dec(v___x_837_);
                        v___x_848_ = crate::leanh::lean_box(0);
                        v_isShared_849_ = v_isSharedCheck_853_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_841_ == 0 {
                    v___x_843_ = v___x_840_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_844_, 0, v_a_838_);
                    v___x_843_ = v_reuseFailAlloc_844_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_843_;
            }
            3 => {
                if v_isShared_849_ == 0 {
                    v___x_851_ = v___x_848_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_852_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_852_, 0, v_a_846_);
                    v___x_851_ = v_reuseFailAlloc_852_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg___boxed(
    mut v_mvarId_854_: *mut crate::leanh::LeanObject,
    mut v_x_855_: *mut crate::leanh::LeanObject,
    mut v___y_856_: *mut crate::leanh::LeanObject,
    mut v___y_857_: *mut crate::leanh::LeanObject,
    mut v___y_858_: *mut crate::leanh::LeanObject,
    mut v___y_859_: *mut crate::leanh::LeanObject,
    mut v___y_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(
        v_mvarId_854_,
        v_x_855_,
        v___y_856_,
        v___y_857_,
        v___y_858_,
        v___y_859_,
    );
    crate::leanh::lean_dec(v___y_859_);
    crate::leanh::lean_dec_ref(v___y_858_);
    crate::leanh::lean_dec(v___y_857_);
    crate::leanh::lean_dec_ref(v___y_856_);
    return v_res_861_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(
    mut v_00_u03b1_862_: *mut crate::leanh::LeanObject,
    mut v_mvarId_863_: *mut crate::leanh::LeanObject,
    mut v_x_864_: *mut crate::leanh::LeanObject,
    mut v___y_865_: *mut crate::leanh::LeanObject,
    mut v___y_866_: *mut crate::leanh::LeanObject,
    mut v___y_867_: *mut crate::leanh::LeanObject,
    mut v___y_868_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_870_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(
        v_mvarId_863_,
        v_x_864_,
        v___y_865_,
        v___y_866_,
        v___y_867_,
        v___y_868_,
    );
    return v___x_870_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___boxed(
    mut v_00_u03b1_871_: *mut crate::leanh::LeanObject,
    mut v_mvarId_872_: *mut crate::leanh::LeanObject,
    mut v_x_873_: *mut crate::leanh::LeanObject,
    mut v___y_874_: *mut crate::leanh::LeanObject,
    mut v___y_875_: *mut crate::leanh::LeanObject,
    mut v___y_876_: *mut crate::leanh::LeanObject,
    mut v___y_877_: *mut crate::leanh::LeanObject,
    mut v___y_878_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_879_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1(
        v_00_u03b1_871_,
        v_mvarId_872_,
        v_x_873_,
        v___y_874_,
        v___y_875_,
        v___y_876_,
        v___y_877_,
    );
    crate::leanh::lean_dec(v___y_877_);
    crate::leanh::lean_dec_ref(v___y_876_);
    crate::leanh::lean_dec(v___y_875_);
    crate::leanh::lean_dec_ref(v___y_874_);
    return v_res_879_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(
    mut v_x_880_: *mut crate::leanh::LeanObject,
    mut v_x_881_: *mut crate::leanh::LeanObject,
    mut v_x_882_: *mut crate::leanh::LeanObject,
    mut v_x_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_890_: u8 = 0;
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_909_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_884_ = crate::leanh::lean_ctor_get(v_x_880_, 0);
                v_vs_885_ = crate::leanh::lean_ctor_get(v_x_880_, 1);
                v_isSharedCheck_909_ = (!crate::leanh::lean_is_exclusive(v_x_880_)) as u8;
                if v_isSharedCheck_909_ == 0 {
                    v___x_887_ = v_x_880_;
                    v_isShared_888_ = v_isSharedCheck_909_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_885_);
                    crate::leanh::lean_inc(v_ks_884_);
                    crate::leanh::lean_dec(v_x_880_);
                    v___x_887_ = crate::leanh::lean_box(0);
                    v_isShared_888_ = v_isSharedCheck_909_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_889_ = lean_array_get_size(v_ks_884_);
                v___x_890_ = lean_nat_dec_lt(v_x_881_, v___x_889_);
                if v___x_890_ == 0 {
                    crate::leanh::lean_dec(v_x_881_);
                    v___x_891_ = lean_array_push(v_ks_884_, v_x_882_);
                    v___x_892_ = lean_array_push(v_vs_885_, v_x_883_);
                    if v_isShared_888_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_887_, 1, v___x_892_);
                        crate::leanh::lean_ctor_set(v___x_887_, 0, v___x_891_);
                        v___x_894_ = v___x_887_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_895_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_895_, 0, v___x_891_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_895_, 1, v___x_892_);
                        v___x_894_ = v_reuseFailAlloc_895_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_896_ = lean_array_fget_borrowed(v_ks_884_, v_x_881_);
                    v___x_897_ = l_Lean_instBEqMVarId_beq(v_x_882_, v_k_x27_896_);
                    if v___x_897_ == 0 {
                        if v_isShared_888_ == 0 {
                            v___x_899_ = v___x_887_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_903_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 0, v_ks_884_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_903_, 1, v_vs_885_);
                            v___x_899_ = v_reuseFailAlloc_903_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_904_ = lean_array_fset(v_ks_884_, v_x_881_, v_x_882_);
                        v___x_905_ = lean_array_fset(v_vs_885_, v_x_881_, v_x_883_);
                        crate::leanh::lean_dec(v_x_881_);
                        if v_isShared_888_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_887_, 1, v___x_905_);
                            crate::leanh::lean_ctor_set(v___x_887_, 0, v___x_904_);
                            v___x_907_ = v___x_887_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_908_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v___x_904_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_908_, 1, v___x_905_);
                            v___x_907_ = v_reuseFailAlloc_908_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_894_;
            }
            3 => {
                v___x_900_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_901_ = lean_nat_add(v_x_881_, v___x_900_);
                crate::leanh::lean_dec(v_x_881_);
                v_x_880_ = v___x_899_;
                v_x_881_ = v___x_901_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_907_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(
    mut v_n_910_: *mut crate::leanh::LeanObject,
    mut v_k_911_: *mut crate::leanh::LeanObject,
    mut v_v_912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_913_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_914_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_n_910_, v___x_913_, v_k_911_, v_v_912_);
    return v___x_914_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_915_: usize = 0;
    let mut v___x_916_: usize = 0;
    let mut v___x_917_: usize = 0;
    v___x_915_ = 5usize;
    v___x_916_ = 1usize;
    v___x_917_ = lean_usize_shift_left(v___x_916_, v___x_915_);
    return v___x_917_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_918_: usize = 0;
    let mut v___x_919_: usize = 0;
    let mut v___x_920_: usize = 0;
    v___x_918_ = 1usize;
    v___x_919_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_920_ = lean_usize_sub(v___x_919_, v___x_918_);
    return v___x_920_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_921_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_921_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(
    mut v_x_922_: *mut crate::leanh::LeanObject,
    mut v_x_923_: usize,
    mut v_x_924_: usize,
    mut v_x_925_: *mut crate::leanh::LeanObject,
    mut v_x_926_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_928_: usize = 0;
    let mut v___x_929_: usize = 0;
    let mut v___x_930_: usize = 0;
    let mut v___x_931_: usize = 0;
    let mut v_j_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: u8 = 0;
    let mut v___x_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_937_: u8 = 0;
    let mut v_v_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_951_: u8 = 0;
    let mut v___x_952_: u8 = 0;
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_958_: u8 = 0;
    let mut v_node_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_962_: u8 = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: usize = 0;
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_969_: u8 = 0;
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut v_unused_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_977_: u8 = 0;
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_982_: u8 = 0;
    let mut v_ks_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: usize = 0;
    let mut v___x_989_: u8 = 0;
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v_reuseFailAlloc_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_922_) == 0 {
                    v_es_927_ = crate::leanh::lean_ctor_get(v_x_922_, 0);
                    v___x_928_ = 5usize;
                    v___x_929_ = 1usize;
                    v___x_930_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_931_ = lean_usize_land(v_x_923_, v___x_930_);
                    v_j_932_ = lean_usize_to_nat(v___x_931_);
                    v___x_933_ = lean_array_get_size(v_es_927_);
                    v___x_934_ = lean_nat_dec_lt(v_j_932_, v___x_933_);
                    if v___x_934_ == 0 {
                        crate::leanh::lean_dec(v_j_932_);
                        crate::leanh::lean_dec(v_x_926_);
                        crate::leanh::lean_dec(v_x_925_);
                        return v_x_922_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_927_);
                        v_isSharedCheck_971_ = (!crate::leanh::lean_is_exclusive(v_x_922_)) as u8;
                        if v_isSharedCheck_971_ == 0 {
                            v_unused_972_ = crate::leanh::lean_ctor_get(v_x_922_, 0);
                            crate::leanh::lean_dec(v_unused_972_);
                            v___x_936_ = v_x_922_;
                            v_isShared_937_ = v_isSharedCheck_971_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_922_);
                            v___x_936_ = crate::leanh::lean_box(0);
                            v_isShared_937_ = v_isSharedCheck_971_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_973_ = crate::leanh::lean_ctor_get(v_x_922_, 0);
                    v_vs_974_ = crate::leanh::lean_ctor_get(v_x_922_, 1);
                    v_isSharedCheck_994_ = (!crate::leanh::lean_is_exclusive(v_x_922_)) as u8;
                    if v_isSharedCheck_994_ == 0 {
                        v___x_976_ = v_x_922_;
                        v_isShared_977_ = v_isSharedCheck_994_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_974_);
                        crate::leanh::lean_inc(v_ks_973_);
                        crate::leanh::lean_dec(v_x_922_);
                        v___x_976_ = crate::leanh::lean_box(0);
                        v_isShared_977_ = v_isSharedCheck_994_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_938_ = lean_array_fget(v_es_927_, v_j_932_);
                v___x_939_ = crate::leanh::lean_box(0);
                v_xs_x27_940_ = lean_array_fset(v_es_927_, v_j_932_, v___x_939_);
                match crate::leanh::lean_obj_tag(v_v_938_) {
                    0 => {
                        v_key_947_ = crate::leanh::lean_ctor_get(v_v_938_, 0);
                        v_val_948_ = crate::leanh::lean_ctor_get(v_v_938_, 1);
                        v_isSharedCheck_958_ = (!crate::leanh::lean_is_exclusive(v_v_938_)) as u8;
                        if v_isSharedCheck_958_ == 0 {
                            v___x_950_ = v_v_938_;
                            v_isShared_951_ = v_isSharedCheck_958_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_948_);
                            crate::leanh::lean_inc(v_key_947_);
                            crate::leanh::lean_dec(v_v_938_);
                            v___x_950_ = crate::leanh::lean_box(0);
                            v_isShared_951_ = v_isSharedCheck_958_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_959_ = crate::leanh::lean_ctor_get(v_v_938_, 0);
                        v_isSharedCheck_969_ = (!crate::leanh::lean_is_exclusive(v_v_938_)) as u8;
                        if v_isSharedCheck_969_ == 0 {
                            v___x_961_ = v_v_938_;
                            v_isShared_962_ = v_isSharedCheck_969_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_959_);
                            crate::leanh::lean_dec(v_v_938_);
                            v___x_961_ = crate::leanh::lean_box(0);
                            v_isShared_962_ = v_isSharedCheck_969_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_970_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_970_, 0, v_x_925_);
                        crate::leanh::lean_ctor_set(v___x_970_, 1, v_x_926_);
                        v___y_942_ = v___x_970_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_943_ = lean_array_fset(v_xs_x27_940_, v_j_932_, v___y_942_);
                crate::leanh::lean_dec(v_j_932_);
                if v_isShared_937_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_936_, 0, v___x_943_);
                    v___x_945_ = v___x_936_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_946_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_943_);
                    v___x_945_ = v_reuseFailAlloc_946_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_945_;
            }
            4 => {
                v___x_952_ = l_Lean_instBEqMVarId_beq(v_x_925_, v_key_947_);
                if v___x_952_ == 0 {
                    crate::leanh::lean_del_object(v___x_950_);
                    v___x_953_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_947_, v_val_948_, v_x_925_, v_x_926_,
                    );
                    v___x_954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_954_, 0, v___x_953_);
                    v___y_942_ = v___x_954_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_948_);
                    crate::leanh::lean_dec(v_key_947_);
                    if v_isShared_951_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_950_, 1, v_x_926_);
                        crate::leanh::lean_ctor_set(v___x_950_, 0, v_x_925_);
                        v___x_956_ = v___x_950_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_957_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_957_, 0, v_x_925_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_957_, 1, v_x_926_);
                        v___x_956_ = v_reuseFailAlloc_957_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_942_ = v___x_956_;
                state = 2;
                continue;
            }
            6 => {
                v___x_963_ = lean_usize_shift_right(v_x_923_, v___x_928_);
                v___x_964_ = lean_usize_add(v_x_924_, v___x_929_);
                v___x_965_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_node_959_, v___x_963_, v___x_964_, v_x_925_, v_x_926_);
                if v_isShared_962_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_961_, 0, v___x_965_);
                    v___x_967_ = v___x_961_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_968_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_968_, 0, v___x_965_);
                    v___x_967_ = v_reuseFailAlloc_968_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_942_ = v___x_967_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_977_ == 0 {
                    v___x_979_ = v___x_976_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_993_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_993_, 0, v_ks_973_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_993_, 1, v_vs_974_);
                    v___x_979_ = v_reuseFailAlloc_993_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_980_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v___x_979_, v_x_925_, v_x_926_);
                v___x_988_ = 7usize;
                v___x_989_ = lean_usize_dec_le(v___x_988_, v_x_924_);
                if v___x_989_ == 0 {
                    v___x_990_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_980_);
                    v___x_991_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_992_ = lean_nat_dec_lt(v___x_990_, v___x_991_);
                    crate::leanh::lean_dec(v___x_990_);
                    v___y_982_ = v___x_992_;
                    state = 10;
                    continue;
                } else {
                    v___y_982_ = v___x_989_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_982_ == 0 {
                    v_ks_983_ = crate::leanh::lean_ctor_get(v_newNode_980_, 0);
                    crate::leanh::lean_inc_ref(v_ks_983_);
                    v_vs_984_ = crate::leanh::lean_ctor_get(v_newNode_980_, 1);
                    crate::leanh::lean_inc_ref(v_vs_984_);
                    crate::leanh::lean_dec_ref(v_newNode_980_);
                    v___x_985_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_986_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_987_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_x_924_, v_ks_983_, v_vs_984_, v___x_985_, v___x_986_);
                    crate::leanh::lean_dec_ref(v_vs_984_);
                    crate::leanh::lean_dec_ref(v_ks_983_);
                    return v___x_987_;
                } else {
                    return v_newNode_980_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_depth_995_: usize,
    mut v_keys_996_: *mut crate::leanh::LeanObject,
    mut v_vals_997_: *mut crate::leanh::LeanObject,
    mut v_i_998_: *mut crate::leanh::LeanObject,
    mut v_entries_999_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    let mut v_k_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: u64 = 0;
    let mut v_h_1005_: usize = 0;
    let mut v___x_1006_: usize = 0;
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: usize = 0;
    let mut v___x_1010_: usize = 0;
    let mut v_h_1011_: usize = 0;
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1000_ = lean_array_get_size(v_keys_996_);
                v___x_1001_ = lean_nat_dec_lt(v_i_998_, v___x_1000_);
                if v___x_1001_ == 0 {
                    crate::leanh::lean_dec(v_i_998_);
                    return v_entries_999_;
                } else {
                    v_k_1002_ = lean_array_fget_borrowed(v_keys_996_, v_i_998_);
                    v_v_1003_ = lean_array_fget_borrowed(v_vals_997_, v_i_998_);
                    v___x_1004_ = l_Lean_instHashableMVarId_hash(v_k_1002_);
                    v_h_1005_ = lean_uint64_to_usize(v___x_1004_);
                    v___x_1006_ = 5usize;
                    v___x_1007_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1008_ = 1usize;
                    v___x_1009_ = lean_usize_sub(v_depth_995_, v___x_1008_);
                    v___x_1010_ = lean_usize_mul(v___x_1006_, v___x_1009_);
                    v_h_1011_ = lean_usize_shift_right(v_h_1005_, v___x_1010_);
                    v___x_1012_ = lean_nat_add(v_i_998_, v___x_1007_);
                    crate::leanh::lean_dec(v_i_998_);
                    crate::leanh::lean_inc(v_v_1003_);
                    crate::leanh::lean_inc(v_k_1002_);
                    v___x_1013_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_entries_999_, v_h_1011_, v_depth_995_, v_k_1002_, v_v_1003_);
                    v_i_998_ = v___x_1012_;
                    v_entries_999_ = v___x_1013_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg___boxed(
    mut v_depth_1015_: *mut crate::leanh::LeanObject,
    mut v_keys_1016_: *mut crate::leanh::LeanObject,
    mut v_vals_1017_: *mut crate::leanh::LeanObject,
    mut v_i_1018_: *mut crate::leanh::LeanObject,
    mut v_entries_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1020_: usize = 0;
    let mut v_res_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1020_ = crate::leanh::lean_unbox_usize(v_depth_1015_);
    crate::leanh::lean_dec(v_depth_1015_);
    v_res_1021_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_boxed_1020_, v_keys_1016_, v_vals_1017_, v_i_1018_, v_entries_1019_);
    crate::leanh::lean_dec_ref(v_vals_1017_);
    crate::leanh::lean_dec_ref(v_keys_1016_);
    return v_res_1021_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_1022_: *mut crate::leanh::LeanObject,
    mut v_x_1023_: *mut crate::leanh::LeanObject,
    mut v_x_1024_: *mut crate::leanh::LeanObject,
    mut v_x_1025_: *mut crate::leanh::LeanObject,
    mut v_x_1026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1415__boxed_1027_: usize = 0;
    let mut v_x_1416__boxed_1028_: usize = 0;
    let mut v_res_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1415__boxed_1027_ = crate::leanh::lean_unbox_usize(v_x_1023_);
    crate::leanh::lean_dec(v_x_1023_);
    v_x_1416__boxed_1028_ = crate::leanh::lean_unbox_usize(v_x_1024_);
    crate::leanh::lean_dec(v_x_1024_);
    v_res_1029_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_1022_, v_x_1415__boxed_1027_, v_x_1416__boxed_1028_, v_x_1025_, v_x_1026_);
    return v_res_1029_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(
    mut v_x_1030_: *mut crate::leanh::LeanObject,
    mut v_x_1031_: *mut crate::leanh::LeanObject,
    mut v_x_1032_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1033_: u64 = 0;
    let mut v___x_1034_: usize = 0;
    let mut v___x_1035_: usize = 0;
    let mut v___x_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1033_ = l_Lean_instHashableMVarId_hash(v_x_1031_);
    v___x_1034_ = lean_uint64_to_usize(v___x_1033_);
    v___x_1035_ = 1usize;
    v___x_1036_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_1030_, v___x_1034_, v___x_1035_, v_x_1031_, v_x_1032_);
    return v___x_1036_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(
    mut v_mvarId_1037_: *mut crate::leanh::LeanObject,
    mut v_val_1038_: *mut crate::leanh::LeanObject,
    mut v___y_1039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1049_: u8 = 0;
    let mut v_depth_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1062_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1073_: u8 = 0;
    let mut v_isSharedCheck_1074_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1041_ = lean_st_ref_take(v___y_1039_);
                v_mctx_1042_ = crate::leanh::lean_ctor_get(v___x_1041_, 0);
                v_cache_1043_ = crate::leanh::lean_ctor_get(v___x_1041_, 1);
                v_zetaDeltaFVarIds_1044_ = crate::leanh::lean_ctor_get(v___x_1041_, 2);
                v_postponed_1045_ = crate::leanh::lean_ctor_get(v___x_1041_, 3);
                v_diag_1046_ = crate::leanh::lean_ctor_get(v___x_1041_, 4);
                v_isSharedCheck_1074_ = (!crate::leanh::lean_is_exclusive(v___x_1041_)) as u8;
                if v_isSharedCheck_1074_ == 0 {
                    v___x_1048_ = v___x_1041_;
                    v_isShared_1049_ = v_isSharedCheck_1074_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_diag_1046_);
                    crate::leanh::lean_inc(v_postponed_1045_);
                    crate::leanh::lean_inc(v_zetaDeltaFVarIds_1044_);
                    crate::leanh::lean_inc(v_cache_1043_);
                    crate::leanh::lean_inc(v_mctx_1042_);
                    crate::leanh::lean_dec(v___x_1041_);
                    v___x_1048_ = crate::leanh::lean_box(0);
                    v_isShared_1049_ = v_isSharedCheck_1074_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1050_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 0);
                v_levelAssignDepth_1051_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 1);
                v_lmvarCounter_1052_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 2);
                v_mvarCounter_1053_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 3);
                v_lDecls_1054_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 4);
                v_decls_1055_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 5);
                v_userNames_1056_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 6);
                v_lAssignment_1057_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 7);
                v_eAssignment_1058_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 8);
                v_dAssignment_1059_ = crate::leanh::lean_ctor_get(v_mctx_1042_, 9);
                v_isSharedCheck_1073_ = (!crate::leanh::lean_is_exclusive(v_mctx_1042_)) as u8;
                if v_isSharedCheck_1073_ == 0 {
                    v___x_1061_ = v_mctx_1042_;
                    v_isShared_1062_ = v_isSharedCheck_1073_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_dAssignment_1059_);
                    crate::leanh::lean_inc(v_eAssignment_1058_);
                    crate::leanh::lean_inc(v_lAssignment_1057_);
                    crate::leanh::lean_inc(v_userNames_1056_);
                    crate::leanh::lean_inc(v_decls_1055_);
                    crate::leanh::lean_inc(v_lDecls_1054_);
                    crate::leanh::lean_inc(v_mvarCounter_1053_);
                    crate::leanh::lean_inc(v_lmvarCounter_1052_);
                    crate::leanh::lean_inc(v_levelAssignDepth_1051_);
                    crate::leanh::lean_inc(v_depth_1050_);
                    crate::leanh::lean_dec(v_mctx_1042_);
                    v___x_1061_ = crate::leanh::lean_box(0);
                    v_isShared_1062_ = v_isSharedCheck_1073_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1063_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_eAssignment_1058_, v_mvarId_1037_, v_val_1038_);
                if v_isShared_1062_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1061_, 8, v___x_1063_);
                    v___x_1065_ = v___x_1061_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1072_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 0, v_depth_1050_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1072_,
                        1,
                        v_levelAssignDepth_1051_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 2, v_lmvarCounter_1052_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 3, v_mvarCounter_1053_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 4, v_lDecls_1054_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 5, v_decls_1055_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 6, v_userNames_1056_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 7, v_lAssignment_1057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 8, v___x_1063_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1072_, 9, v_dAssignment_1059_);
                    v___x_1065_ = v_reuseFailAlloc_1072_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1049_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1065_);
                    v___x_1067_ = v___x_1048_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1071_ = crate::leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1065_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_cache_1043_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_1071_,
                        2,
                        v_zetaDeltaFVarIds_1044_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 3, v_postponed_1045_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1071_, 4, v_diag_1046_);
                    v___x_1067_ = v_reuseFailAlloc_1071_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1068_ = lean_st_ref_set(v___y_1039_, v___x_1067_);
                v___x_1069_ = crate::leanh::lean_box(0);
                v___x_1070_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1069_);
                return v___x_1070_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg___boxed(
    mut v_mvarId_1075_: *mut crate::leanh::LeanObject,
    mut v_val_1076_: *mut crate::leanh::LeanObject,
    mut v___y_1077_: *mut crate::leanh::LeanObject,
    mut v___y_1078_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1079_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(
        v_mvarId_1075_,
        v_val_1076_,
        v___y_1077_,
    );
    crate::leanh::lean_dec(v___y_1077_);
    return v_res_1079_;
}
pub unsafe fn l_Lean_MVarId_assumptionCore___lam__0(
    mut v_mvarId_1080_: *mut crate::leanh::LeanObject,
    mut v___x_1081_: *mut crate::leanh::LeanObject,
    mut v___y_1082_: *mut crate::leanh::LeanObject,
    mut v___y_1083_: *mut crate::leanh::LeanObject,
    mut v___y_1084_: *mut crate::leanh::LeanObject,
    mut v___y_1085_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1094_: u8 = 0;
    let mut v___x_1095_: u8 = 0;
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1105_: u8 = 0;
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1111_: u8 = 0;
    let mut v_unused_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1113_: u8 = 0;
    let mut v_a_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1117_: u8 = 0;
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1121_: u8 = 0;
    let mut v_a_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1125_: u8 = 0;
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1129_: u8 = 0;
    let mut v_a_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1133_: u8 = 0;
    let mut v___x_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1137_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1080_);
                v___x_1087_ = l_Lean_MVarId_checkNotAssigned(
                    v_mvarId_1080_,
                    v___x_1081_,
                    v___y_1082_,
                    v___y_1083_,
                    v___y_1084_,
                    v___y_1085_,
                );
                if crate::leanh::lean_obj_tag(v___x_1087_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_1087_, 1);
                    crate::leanh::lean_inc(v_mvarId_1080_);
                    v___x_1088_ = l_Lean_MVarId_getType(
                        v_mvarId_1080_,
                        v___y_1082_,
                        v___y_1083_,
                        v___y_1084_,
                        v___y_1085_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1088_) == 0 {
                        v_a_1089_ = crate::leanh::lean_ctor_get(v___x_1088_, 0);
                        crate::leanh::lean_inc(v_a_1089_);
                        crate::leanh::lean_dec_ref_known(v___x_1088_, 1);
                        v___x_1090_ = l_Lean_Meta_findLocalDeclWithType_x3f(
                            v_a_1089_,
                            v___y_1082_,
                            v___y_1083_,
                            v___y_1084_,
                            v___y_1085_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1090_) == 0 {
                            v_a_1091_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                            v_isSharedCheck_1113_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                            if v_isSharedCheck_1113_ == 0 {
                                v___x_1093_ = v___x_1090_;
                                v_isShared_1094_ = v_isSharedCheck_1113_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1091_);
                                crate::leanh::lean_dec(v___x_1090_);
                                v___x_1093_ = crate::leanh::lean_box(0);
                                v_isShared_1094_ = v_isSharedCheck_1113_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_mvarId_1080_);
                            v_a_1114_ = crate::leanh::lean_ctor_get(v___x_1090_, 0);
                            v_isSharedCheck_1121_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1090_)) as u8;
                            if v_isSharedCheck_1121_ == 0 {
                                v___x_1116_ = v___x_1090_;
                                v_isShared_1117_ = v_isSharedCheck_1121_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1114_);
                                crate::leanh::lean_dec(v___x_1090_);
                                v___x_1116_ = crate::leanh::lean_box(0);
                                v_isShared_1117_ = v_isSharedCheck_1121_;
                                state = 5;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_mvarId_1080_);
                        v_a_1122_ = crate::leanh::lean_ctor_get(v___x_1088_, 0);
                        v_isSharedCheck_1129_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1088_)) as u8;
                        if v_isSharedCheck_1129_ == 0 {
                            v___x_1124_ = v___x_1088_;
                            v_isShared_1125_ = v_isSharedCheck_1129_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1122_);
                            crate::leanh::lean_dec(v___x_1088_);
                            v___x_1124_ = crate::leanh::lean_box(0);
                            v_isShared_1125_ = v_isSharedCheck_1129_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1080_);
                    v_a_1130_ = crate::leanh::lean_ctor_get(v___x_1087_, 0);
                    v_isSharedCheck_1137_ = (!crate::leanh::lean_is_exclusive(v___x_1087_)) as u8;
                    if v_isSharedCheck_1137_ == 0 {
                        v___x_1132_ = v___x_1087_;
                        v_isShared_1133_ = v_isSharedCheck_1137_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1130_);
                        crate::leanh::lean_dec(v___x_1087_);
                        v___x_1132_ = crate::leanh::lean_box(0);
                        v_isShared_1133_ = v_isSharedCheck_1137_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1091_) == 0 {
                    crate::leanh::lean_dec(v_mvarId_1080_);
                    v___x_1095_ = 0;
                    v___x_1096_ = crate::leanh::lean_box((v___x_1095_) as usize);
                    if v_isShared_1094_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1093_, 0, v___x_1096_);
                        v___x_1098_ = v___x_1093_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1099_, 0, v___x_1096_);
                        v___x_1098_ = v_reuseFailAlloc_1099_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1093_);
                    v_val_1100_ = crate::leanh::lean_ctor_get(v_a_1091_, 0);
                    crate::leanh::lean_inc(v_val_1100_);
                    crate::leanh::lean_dec_ref_known(v_a_1091_, 1);
                    v___x_1101_ = l_Lean_mkFVar(v_val_1100_);
                    v___x_1102_ =
                        l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(
                            v_mvarId_1080_,
                            v___x_1101_,
                            v___y_1083_,
                        );
                    v_isSharedCheck_1111_ = (!crate::leanh::lean_is_exclusive(v___x_1102_)) as u8;
                    if v_isSharedCheck_1111_ == 0 {
                        v_unused_1112_ = crate::leanh::lean_ctor_get(v___x_1102_, 0);
                        crate::leanh::lean_dec(v_unused_1112_);
                        v___x_1104_ = v___x_1102_;
                        v_isShared_1105_ = v_isSharedCheck_1111_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_1102_);
                        v___x_1104_ = crate::leanh::lean_box(0);
                        v_isShared_1105_ = v_isSharedCheck_1111_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1098_;
            }
            3 => {
                v___x_1106_ = 1;
                v___x_1107_ = crate::leanh::lean_box((v___x_1106_) as usize);
                if v_isShared_1105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1104_, 0, v___x_1107_);
                    v___x_1109_ = v___x_1104_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1110_, 0, v___x_1107_);
                    v___x_1109_ = v_reuseFailAlloc_1110_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1109_;
            }
            5 => {
                if v_isShared_1117_ == 0 {
                    v___x_1119_ = v___x_1116_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1120_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1120_, 0, v_a_1114_);
                    v___x_1119_ = v_reuseFailAlloc_1120_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1119_;
            }
            7 => {
                if v_isShared_1125_ == 0 {
                    v___x_1127_ = v___x_1124_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1128_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1128_, 0, v_a_1122_);
                    v___x_1127_ = v_reuseFailAlloc_1128_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1127_;
            }
            9 => {
                if v_isShared_1133_ == 0 {
                    v___x_1135_ = v___x_1132_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1136_, 0, v_a_1130_);
                    v___x_1135_ = v_reuseFailAlloc_1136_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1135_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assumptionCore___lam__0___boxed(
    mut v_mvarId_1138_: *mut crate::leanh::LeanObject,
    mut v___x_1139_: *mut crate::leanh::LeanObject,
    mut v___y_1140_: *mut crate::leanh::LeanObject,
    mut v___y_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v___y_1143_: *mut crate::leanh::LeanObject,
    mut v___y_1144_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1145_ = l_Lean_MVarId_assumptionCore___lam__0(
        v_mvarId_1138_,
        v___x_1139_,
        v___y_1140_,
        v___y_1141_,
        v___y_1142_,
        v___y_1143_,
    );
    crate::leanh::lean_dec(v___y_1143_);
    crate::leanh::lean_dec_ref(v___y_1142_);
    crate::leanh::lean_dec(v___y_1141_);
    crate::leanh::lean_dec_ref(v___y_1140_);
    return v_res_1145_;
}
pub unsafe fn l_Lean_MVarId_assumptionCore(
    mut v_mvarId_1149_: *mut crate::leanh::LeanObject,
    mut v_a_1150_: *mut crate::leanh::LeanObject,
    mut v_a_1151_: *mut crate::leanh::LeanObject,
    mut v_a_1152_: *mut crate::leanh::LeanObject,
    mut v_a_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1155_ = l_Lean_MVarId_assumptionCore___closed__1;
    crate::leanh::lean_inc(v_mvarId_1149_);
    v___f_1156_ = crate::leanh::lean_alloc_closure(
        l_Lean_MVarId_assumptionCore___lam__0___boxed as *mut core::ffi::c_void,
        7,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1156_, 0, v_mvarId_1149_);
    crate::leanh::lean_closure_set(v___f_1156_, 1, v___x_1155_);
    v___x_1157_ = l_Lean_MVarId_withContext___at___00Lean_MVarId_assumptionCore_spec__1___redArg(
        v_mvarId_1149_,
        v___f_1156_,
        v_a_1150_,
        v_a_1151_,
        v_a_1152_,
        v_a_1153_,
    );
    return v___x_1157_;
}
pub unsafe fn l_Lean_MVarId_assumptionCore___boxed(
    mut v_mvarId_1158_: *mut crate::leanh::LeanObject,
    mut v_a_1159_: *mut crate::leanh::LeanObject,
    mut v_a_1160_: *mut crate::leanh::LeanObject,
    mut v_a_1161_: *mut crate::leanh::LeanObject,
    mut v_a_1162_: *mut crate::leanh::LeanObject,
    mut v_a_1163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1164_ =
        l_Lean_MVarId_assumptionCore(v_mvarId_1158_, v_a_1159_, v_a_1160_, v_a_1161_, v_a_1162_);
    crate::leanh::lean_dec(v_a_1162_);
    crate::leanh::lean_dec_ref(v_a_1161_);
    crate::leanh::lean_dec(v_a_1160_);
    crate::leanh::lean_dec_ref(v_a_1159_);
    return v_res_1164_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(
    mut v_mvarId_1165_: *mut crate::leanh::LeanObject,
    mut v_val_1166_: *mut crate::leanh::LeanObject,
    mut v___y_1167_: *mut crate::leanh::LeanObject,
    mut v___y_1168_: *mut crate::leanh::LeanObject,
    mut v___y_1169_: *mut crate::leanh::LeanObject,
    mut v___y_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1172_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___redArg(
        v_mvarId_1165_,
        v_val_1166_,
        v___y_1168_,
    );
    return v___x_1172_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0___boxed(
    mut v_mvarId_1173_: *mut crate::leanh::LeanObject,
    mut v_val_1174_: *mut crate::leanh::LeanObject,
    mut v___y_1175_: *mut crate::leanh::LeanObject,
    mut v___y_1176_: *mut crate::leanh::LeanObject,
    mut v___y_1177_: *mut crate::leanh::LeanObject,
    mut v___y_1178_: *mut crate::leanh::LeanObject,
    mut v___y_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1180_ = l_Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0(
        v_mvarId_1173_,
        v_val_1174_,
        v___y_1175_,
        v___y_1176_,
        v___y_1177_,
        v___y_1178_,
    );
    crate::leanh::lean_dec(v___y_1178_);
    crate::leanh::lean_dec_ref(v___y_1177_);
    crate::leanh::lean_dec(v___y_1176_);
    crate::leanh::lean_dec_ref(v___y_1175_);
    return v_res_1180_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0(
    mut v_00_u03b2_1181_: *mut crate::leanh::LeanObject,
    mut v_x_1182_: *mut crate::leanh::LeanObject,
    mut v_x_1183_: *mut crate::leanh::LeanObject,
    mut v_x_1184_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1185_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0___redArg(v_x_1182_, v_x_1183_, v_x_1184_);
    return v___x_1185_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1186_: *mut crate::leanh::LeanObject,
    mut v_x_1187_: *mut crate::leanh::LeanObject,
    mut v_x_1188_: usize,
    mut v_x_1189_: usize,
    mut v_x_1190_: *mut crate::leanh::LeanObject,
    mut v_x_1191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1192_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___redArg(v_x_1187_, v_x_1188_, v_x_1189_, v_x_1190_, v_x_1191_);
    return v___x_1192_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1193_: *mut crate::leanh::LeanObject,
    mut v_x_1194_: *mut crate::leanh::LeanObject,
    mut v_x_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v_x_1197_: *mut crate::leanh::LeanObject,
    mut v_x_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_1801__boxed_1199_: usize = 0;
    let mut v_x_1802__boxed_1200_: usize = 0;
    let mut v_res_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_1801__boxed_1199_ = crate::leanh::lean_unbox_usize(v_x_1195_);
    crate::leanh::lean_dec(v_x_1195_);
    v_x_1802__boxed_1200_ = crate::leanh::lean_unbox_usize(v_x_1196_);
    crate::leanh::lean_dec(v_x_1196_);
    v_res_1201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2(v_00_u03b2_1193_, v_x_1194_, v_x_1801__boxed_1199_, v_x_1802__boxed_1200_, v_x_1197_, v_x_1198_);
    return v_res_1201_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3(
    mut v_00_u03b2_1202_: *mut crate::leanh::LeanObject,
    mut v_n_1203_: *mut crate::leanh::LeanObject,
    mut v_k_1204_: *mut crate::leanh::LeanObject,
    mut v_v_1205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1206_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3___redArg(v_n_1203_, v_k_1204_, v_v_1205_);
    return v___x_1206_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1207_: *mut crate::leanh::LeanObject,
    mut v_depth_1208_: usize,
    mut v_keys_1209_: *mut crate::leanh::LeanObject,
    mut v_vals_1210_: *mut crate::leanh::LeanObject,
    mut v_heq_1211_: *mut crate::leanh::LeanObject,
    mut v_i_1212_: *mut crate::leanh::LeanObject,
    mut v_entries_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___redArg(v_depth_1208_, v_keys_1209_, v_vals_1210_, v_i_1212_, v_entries_1213_);
    return v___x_1214_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_00_u03b2_1215_: *mut crate::leanh::LeanObject,
    mut v_depth_1216_: *mut crate::leanh::LeanObject,
    mut v_keys_1217_: *mut crate::leanh::LeanObject,
    mut v_vals_1218_: *mut crate::leanh::LeanObject,
    mut v_heq_1219_: *mut crate::leanh::LeanObject,
    mut v_i_1220_: *mut crate::leanh::LeanObject,
    mut v_entries_1221_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_1222_: usize = 0;
    let mut v_res_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1222_ = crate::leanh::lean_unbox_usize(v_depth_1216_);
    crate::leanh::lean_dec(v_depth_1216_);
    v_res_1223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__4(v_00_u03b2_1215_, v_depth_boxed_1222_, v_keys_1217_, v_vals_1218_, v_heq_1219_, v_i_1220_, v_entries_1221_);
    crate::leanh::lean_dec_ref(v_vals_1218_);
    crate::leanh::lean_dec_ref(v_keys_1217_);
    return v_res_1223_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4(
    mut v_00_u03b2_1224_: *mut crate::leanh::LeanObject,
    mut v_x_1225_: *mut crate::leanh::LeanObject,
    mut v_x_1226_: *mut crate::leanh::LeanObject,
    mut v_x_1227_: *mut crate::leanh::LeanObject,
    mut v_x_1228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1229_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_MVarId_assumptionCore_spec__0_spec__0_spec__2_spec__3_spec__4___redArg(v_x_1225_, v_x_1226_, v_x_1227_, v_x_1228_);
    return v___x_1229_;
}
pub unsafe fn l_Lean_MVarId_assumption(
    mut v_mvarId_1230_: *mut crate::leanh::LeanObject,
    mut v_a_1231_: *mut crate::leanh::LeanObject,
    mut v_a_1232_: *mut crate::leanh::LeanObject,
    mut v_a_1233_: *mut crate::leanh::LeanObject,
    mut v_a_1234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1240_: u8 = 0;
    let mut v___x_1241_: u8 = 0;
    let mut v___x_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1249_: u8 = 0;
    let mut v_a_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1253_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1257_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_mvarId_1230_);
                v___x_1236_ = l_Lean_MVarId_assumptionCore(
                    v_mvarId_1230_,
                    v_a_1231_,
                    v_a_1232_,
                    v_a_1233_,
                    v_a_1234_,
                );
                if crate::leanh::lean_obj_tag(v___x_1236_) == 0 {
                    v_a_1237_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                    v_isSharedCheck_1249_ = (!crate::leanh::lean_is_exclusive(v___x_1236_)) as u8;
                    if v_isSharedCheck_1249_ == 0 {
                        v___x_1239_ = v___x_1236_;
                        v_isShared_1240_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1237_);
                        crate::leanh::lean_dec(v___x_1236_);
                        v___x_1239_ = crate::leanh::lean_box(0);
                        v_isShared_1240_ = v_isSharedCheck_1249_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_mvarId_1230_);
                    v_a_1250_ = crate::leanh::lean_ctor_get(v___x_1236_, 0);
                    v_isSharedCheck_1257_ = (!crate::leanh::lean_is_exclusive(v___x_1236_)) as u8;
                    if v_isSharedCheck_1257_ == 0 {
                        v___x_1252_ = v___x_1236_;
                        v_isShared_1253_ = v_isSharedCheck_1257_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1250_);
                        crate::leanh::lean_dec(v___x_1236_);
                        v___x_1252_ = crate::leanh::lean_box(0);
                        v_isShared_1253_ = v_isSharedCheck_1257_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1241_ = (crate::leanh::lean_unbox(v_a_1237_) as u8);
                crate::leanh::lean_dec(v_a_1237_);
                if v___x_1241_ == 0 {
                    crate::leanh::lean_del_object(v___x_1239_);
                    v___x_1242_ = l_Lean_MVarId_assumptionCore___closed__1;
                    v___x_1243_ = crate::leanh::lean_box(0);
                    v___x_1244_ = l_Lean_Meta_throwTacticEx___redArg(
                        v___x_1242_,
                        v_mvarId_1230_,
                        v___x_1243_,
                        v_a_1231_,
                        v_a_1232_,
                        v_a_1233_,
                        v_a_1234_,
                    );
                    return v___x_1244_;
                } else {
                    crate::leanh::lean_dec(v_mvarId_1230_);
                    v___x_1245_ = crate::leanh::lean_box(0);
                    if v_isShared_1240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1239_, 0, v___x_1245_);
                        v___x_1247_ = v___x_1239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
                        v___x_1247_ = v_reuseFailAlloc_1248_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1247_;
            }
            3 => {
                if v_isShared_1253_ == 0 {
                    v___x_1255_ = v___x_1252_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1256_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
                    v___x_1255_ = v_reuseFailAlloc_1256_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1255_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assumption___boxed(
    mut v_mvarId_1258_: *mut crate::leanh::LeanObject,
    mut v_a_1259_: *mut crate::leanh::LeanObject,
    mut v_a_1260_: *mut crate::leanh::LeanObject,
    mut v_a_1261_: *mut crate::leanh::LeanObject,
    mut v_a_1262_: *mut crate::leanh::LeanObject,
    mut v_a_1263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1264_ =
        l_Lean_MVarId_assumption(v_mvarId_1258_, v_a_1259_, v_a_1260_, v_a_1261_, v_a_1262_);
    crate::leanh::lean_dec(v_a_1262_);
    crate::leanh::lean_dec_ref(v_a_1261_);
    crate::leanh::lean_dec(v_a_1260_);
    crate::leanh::lean_dec_ref(v_a_1259_);
    return v_res_1264_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Assumption(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Assumption(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Assumption(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Assumption(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Assumption(builtin);
}

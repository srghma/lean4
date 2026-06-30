// Lean compiler output
// Module: Lean.Meta.Sym.Apply
// Imports: Lean.Meta.Sym.Pattern Lean.Util.CollectFVars Init.Data.Range.Polymorphic.Iterators
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_to_list, lean_array_uget_borrowed, lean_array_uset, lean_expr_instantiate_rev,
    lean_expr_instantiate_rev_range, lean_mk_array, lean_mk_empty_array_with_capacity,
    lean_name_eq, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_st_ref_get,
    lean_st_ref_set, lean_st_ref_take, lean_uint64_to_usize, lean_usize_add, lean_usize_dec_le,
    lean_usize_dec_lt, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::Range::Polymorphic::Iterators::{
    initialize_Init_Data_Range_Polymorphic_Iterators,
    runtime_initialize_Init_Data_Range_Polymorphic_Iterators,
};
use crate::r#gen::Init::Prelude::l_Lean_Name_num___override;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_containsFVar, l_Lean_Expr_fvarId_x21, l_Lean_Expr_mvarId_x21,
    l_Lean_instBEqMVarId_beq, l_Lean_instHashableMVarId_hash, l_Lean_instInhabitedExpr,
    l_Lean_mkAppN, l_Lean_mkConst, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Level::l_Lean_mkLevelParam;
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp, l_Lean_MVarId_getDecl,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern, l_Lean_Meta_Sym_Pattern_unify_x3f,
    l_Lean_Meta_Sym_mkPatternFromDecl, l_Lean_Meta_Sym_mkPatternFromExpr,
    runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::r#gen::Lean::Util::CollectFVars::{
    initialize_Lean_Util_CollectFVars, l_Lean_collectFVars,
    runtime_initialize_Lean_Util_CollectFVars,
};
use crate::r#gen::Lean::Util::InstantiateLevelParams::l_Lean_Expr_instantiateLevelParams;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 115, 121, 109, 95, 112, 114, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__0_value) as *mut leanh::LeanObject,669235891876232411 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value
) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4_value
) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        114, 117, 108, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 112, 112, 108, 105, 99, 97,
        98, 108, 101, 32, 116, 111, 32, 103, 111, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value:
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
    m_data: [114, 117, 108, 101, 58, 0],
};
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(
    mut v_sz_985_: usize,
    mut v_i_986_: usize,
    mut v_bs_987_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_988_: u8 = 0;
    let mut v_v_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isInstance_990_: u8 = 0;
    let mut v___x_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_993_: usize = 0;
    let mut v___x_994_: usize = 0;
    let mut v___x_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_988_ = lean_usize_dec_lt(v_i_986_, v_sz_985_);
                if v___x_988_ == 0 {
                    return v_bs_987_;
                } else {
                    v_v_989_ = lean_array_uget_borrowed(v_bs_987_, v_i_986_);
                    v_isInstance_990_ = leanh::lean_ctor_get_uint8(v_v_989_, 1 as u32);
                    v___x_991_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_992_ = lean_array_uset(v_bs_987_, v_i_986_, v___x_991_);
                    v___x_993_ = 1usize;
                    v___x_994_ = lean_usize_add(v_i_986_, v___x_993_);
                    v___x_995_ = leanh::lean_box((v_isInstance_990_) as usize);
                    v___x_996_ = lean_array_uset(v_bs_x27_992_, v_i_986_, v___x_995_);
                    v_i_986_ = v___x_994_;
                    v_bs_987_ = v___x_996_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5___boxed(
    mut v_sz_998_: *mut leanh::LeanObject,
    mut v_i_999_: *mut leanh::LeanObject,
    mut v_bs_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1001_: usize = 0;
    let mut v_i_boxed_1002_: usize = 0;
    let mut v_res_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1001_ = leanh::lean_unbox_usize(v_sz_998_);
    leanh::lean_dec(v_sz_998_);
    v_i_boxed_1002_ = leanh::lean_unbox_usize(v_i_999_);
    leanh::lean_dec(v_i_999_);
    v_res_1003_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_boxed_1001_, v_i_boxed_1002_, v_bs_1000_);
    return v_res_1003_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(
    mut v_auxVars_1004_: *mut leanh::LeanObject,
    mut v_as_1005_: *mut leanh::LeanObject,
    mut v_i_1006_: *mut leanh::LeanObject,
    mut v_j_1007_: *mut leanh::LeanObject,
    mut v_bs_1008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1010_: u8 = 0;
    let mut v_one_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1009_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1010_ = lean_nat_dec_eq(v_i_1006_, v_zero_1009_);
                if v_isZero_1010_ == 1 {
                    leanh::lean_dec(v_j_1007_);
                    leanh::lean_dec(v_i_1006_);
                    return v_bs_1008_;
                } else {
                    v_one_1011_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1012_ = lean_nat_sub(v_i_1006_, v_one_1011_);
                    leanh::lean_dec(v_i_1006_);
                    v___x_1013_ = lean_array_fget_borrowed(v_as_1005_, v_j_1007_);
                    v___x_1014_ = lean_expr_instantiate_rev_range(
                        v___x_1013_,
                        v_zero_1009_,
                        v_j_1007_,
                        v_auxVars_1004_,
                    );
                    v___x_1015_ = lean_nat_add(v_j_1007_, v_one_1011_);
                    leanh::lean_dec(v_j_1007_);
                    v___x_1016_ = lean_array_push(v_bs_1008_, v___x_1014_);
                    v_i_1006_ = v_n_1012_;
                    v_j_1007_ = v___x_1015_;
                    v_bs_1008_ = v___x_1016_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg___boxed(
    mut v_auxVars_1018_: *mut leanh::LeanObject,
    mut v_as_1019_: *mut leanh::LeanObject,
    mut v_i_1020_: *mut leanh::LeanObject,
    mut v_j_1021_: *mut leanh::LeanObject,
    mut v_bs_1022_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1023_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_1018_, v_as_1019_, v_i_1020_, v_j_1021_, v_bs_1022_);
    leanh::lean_dec_ref(v_as_1019_);
    leanh::lean_dec_ref(v_auxVars_1018_);
    return v_res_1023_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(
    mut v_as_1027_: *mut leanh::LeanObject,
    mut v_sz_1028_: usize,
    mut v_i_1029_: usize,
    mut v_b_1030_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: usize = 0;
    let mut v___x_1034_: usize = 0;
    let mut v___x_1036_: u8 = 0;
    let mut v_a_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_i_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxPrefix_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1041_: u8 = 0;
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1036_ = lean_usize_dec_lt(v_i_1029_, v_sz_1028_);
                if v___x_1036_ == 0 {
                    return v_b_1030_;
                } else {
                    v_a_1037_ = lean_array_uget_borrowed(v_as_1027_, v_i_1029_);
                    if leanh::lean_obj_tag(v_a_1037_) == 2 {
                        v_pre_1038_ = leanh::lean_ctor_get(v_a_1037_, 0);
                        v_i_1039_ = leanh::lean_ctor_get(v_a_1037_, 1);
                        v_auxPrefix_1040_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1;
                        v___x_1041_ = lean_name_eq(v_pre_1038_, v_auxPrefix_1040_);
                        if v___x_1041_ == 0 {
                            v_a_1032_ = v_b_1030_;
                            state = 1;
                            continue;
                        } else {
                            v___x_1042_ = leanh::lean_box((v___x_1041_) as usize);
                            v___x_1043_ = lean_array_set(v_b_1030_, v_i_1039_, v___x_1042_);
                            v_a_1032_ = v___x_1043_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_1032_ = v_b_1030_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1033_ = 1usize;
                v___x_1034_ = lean_usize_add(v_i_1029_, v___x_1033_);
                v_i_1029_ = v___x_1034_;
                v_b_1030_ = v_a_1032_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___boxed(
    mut v_as_1044_: *mut leanh::LeanObject,
    mut v_sz_1045_: *mut leanh::LeanObject,
    mut v_i_1046_: *mut leanh::LeanObject,
    mut v_b_1047_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1048_: usize = 0;
    let mut v_i_boxed_1049_: usize = 0;
    let mut v_res_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1048_ = leanh::lean_unbox_usize(v_sz_1045_);
    leanh::lean_dec(v_sz_1045_);
    v_i_boxed_1049_ = leanh::lean_unbox_usize(v_i_1046_);
    leanh::lean_dec(v_i_1046_);
    v_res_1050_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_as_1044_, v_sz_boxed_1048_, v_i_boxed_1049_, v_b_1047_);
    leanh::lean_dec_ref(v_as_1044_);
    return v_res_1050_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(
    mut v_upperBound_1051_: *mut leanh::LeanObject,
    mut v___x_1052_: *mut leanh::LeanObject,
    mut v___x_1053_: *mut leanh::LeanObject,
    mut v___x_1054_: *mut leanh::LeanObject,
    mut v_a_1055_: *mut leanh::LeanObject,
    mut v_b_1056_: u8,
) -> u8 {
    let mut v_a_1058_: u8 = 0;
    let mut v___x_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: u8 = 0;
    let mut v___x_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: u8 = 0;
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1062_ = lean_nat_dec_lt(v_a_1055_, v_upperBound_1051_);
                if v___x_1062_ == 0 {
                    leanh::lean_dec(v_a_1055_);
                    return v_b_1056_;
                } else {
                    v___x_1063_ = 0;
                    v___x_1064_ = leanh::lean_box((v___x_1063_) as usize);
                    v___x_1065_ = lean_array_get(v___x_1064_, v___x_1052_, v_a_1055_);
                    leanh::lean_dec(v___x_1064_);
                    v___x_1066_ = (leanh::lean_unbox(v___x_1065_) as u8);
                    leanh::lean_dec(v___x_1065_);
                    if v___x_1066_ == 0 {
                        v___x_1067_ = l_Lean_instInhabitedExpr;
                        v___x_1068_ = lean_array_get_borrowed(v___x_1067_, v___x_1053_, v_a_1055_);
                        v___x_1069_ = l_Lean_Expr_fvarId_x21(v___x_1054_);
                        v___x_1070_ = l_Lean_Expr_containsFVar(v___x_1068_, v___x_1069_);
                        leanh::lean_dec(v___x_1069_);
                        if v___x_1070_ == 0 {
                            v_a_1058_ = v_b_1056_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_a_1055_);
                            return v___x_1070_;
                        }
                    } else {
                        v_a_1058_ = v_b_1056_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1059_ = leanh::lean_unsigned_to_nat(1);
                v___x_1060_ = lean_nat_add(v_a_1055_, v___x_1059_);
                leanh::lean_dec(v_a_1055_);
                v_a_1055_ = v___x_1060_;
                v_b_1056_ = v_a_1058_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg___boxed(
    mut v_upperBound_1071_: *mut leanh::LeanObject,
    mut v___x_1072_: *mut leanh::LeanObject,
    mut v___x_1073_: *mut leanh::LeanObject,
    mut v___x_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_b_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1077_: u8 = 0;
    let mut v_res_1078_: u8 = 0;
    let mut v_r_1079_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1077_ = (leanh::lean_unbox(v_b_1076_) as u8);
    v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_1071_, v___x_1072_, v___x_1073_, v___x_1074_, v_a_1075_, v_b_boxed_1077_);
    leanh::lean_dec_ref(v___x_1074_);
    leanh::lean_dec_ref(v___x_1073_);
    leanh::lean_dec_ref(v___x_1072_);
    leanh::lean_dec(v_upperBound_1071_);
    v_r_1079_ = leanh::lean_box((v_res_1078_) as usize);
    return v_r_1079_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(
    mut v_upperBound_1080_: *mut leanh::LeanObject,
    mut v___x_1081_: *mut leanh::LeanObject,
    mut v_numArgs_1082_: *mut leanh::LeanObject,
    mut v_auxVars_1083_: *mut leanh::LeanObject,
    mut v___x_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
    mut v_b_1086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: u8 = 0;
    let mut v_fst_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1101_: u8 = 0;
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1106_: u8 = 0;
    let mut v___x_1107_: u8 = 0;
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1119_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1092_ = lean_nat_dec_lt(v_a_1085_, v_upperBound_1080_);
                if v___x_1092_ == 0 {
                    leanh::lean_dec(v_a_1085_);
                    return v_b_1086_;
                } else {
                    v_fst_1093_ = leanh::lean_ctor_get(v_b_1086_, 0);
                    v_snd_1094_ = leanh::lean_ctor_get(v_b_1086_, 1);
                    v_isSharedCheck_1119_ = (!leanh::lean_is_exclusive(v_b_1086_)) as u8;
                    if v_isSharedCheck_1119_ == 0 {
                        v___x_1096_ = v_b_1086_;
                        v_isShared_1097_ = v_isSharedCheck_1119_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_1094_);
                        leanh::lean_inc(v_fst_1093_);
                        leanh::lean_dec(v_b_1086_);
                        v___x_1096_ = leanh::lean_box(0);
                        v_isShared_1097_ = v_isSharedCheck_1119_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1089_ = leanh::lean_unsigned_to_nat(1);
                v___x_1090_ = lean_nat_add(v_a_1085_, v___x_1089_);
                leanh::lean_dec(v_a_1085_);
                v_a_1085_ = v___x_1090_;
                v_b_1086_ = v_a_1088_;
                state = 0;
                continue;
            }
            2 => {
                v___x_1098_ = 0;
                v___x_1099_ = leanh::lean_box((v___x_1098_) as usize);
                v___x_1100_ = lean_array_get(v___x_1099_, v___x_1081_, v_a_1085_);
                leanh::lean_dec(v___x_1099_);
                v___x_1101_ = (leanh::lean_unbox(v___x_1100_) as u8);
                if v___x_1101_ == 0 {
                    v___x_1102_ = l_Lean_instInhabitedExpr;
                    v___x_1103_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1104_ = lean_nat_add(v_a_1085_, v___x_1103_);
                    v___x_1105_ = lean_array_get_borrowed(v___x_1102_, v_auxVars_1083_, v_a_1085_);
                    v___x_1106_ = (leanh::lean_unbox(v___x_1100_) as u8);
                    leanh::lean_dec(v___x_1100_);
                    v___x_1107_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_numArgs_1082_, v___x_1081_, v___x_1084_, v___x_1105_, v___x_1104_, v___x_1106_);
                    if v___x_1107_ == 0 {
                        leanh::lean_inc(v_a_1085_);
                        v___x_1108_ = lean_array_push(v_snd_1094_, v_a_1085_);
                        if v_isShared_1097_ == 0 {
                            leanh::lean_ctor_set(v___x_1096_, 1, v___x_1108_);
                            v___x_1110_ = v___x_1096_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1111_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 0, v_fst_1093_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1111_, 1, v___x_1108_);
                            v___x_1110_ = v_reuseFailAlloc_1111_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_inc(v_a_1085_);
                        v___x_1112_ = lean_array_push(v_fst_1093_, v_a_1085_);
                        if v_isShared_1097_ == 0 {
                            leanh::lean_ctor_set(v___x_1096_, 0, v___x_1112_);
                            v___x_1114_ = v___x_1096_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1115_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 0, v___x_1112_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_snd_1094_);
                            v___x_1114_ = v_reuseFailAlloc_1115_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v___x_1100_);
                    if v_isShared_1097_ == 0 {
                        v___x_1117_ = v___x_1096_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1118_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 0, v_fst_1093_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1118_, 1, v_snd_1094_);
                        v___x_1117_ = v_reuseFailAlloc_1118_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v_a_1088_ = v___x_1110_;
                state = 1;
                continue;
            }
            4 => {
                v_a_1088_ = v___x_1114_;
                state = 1;
                continue;
            }
            5 => {
                v_a_1088_ = v___x_1117_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg___boxed(
    mut v_upperBound_1120_: *mut leanh::LeanObject,
    mut v___x_1121_: *mut leanh::LeanObject,
    mut v_numArgs_1122_: *mut leanh::LeanObject,
    mut v_auxVars_1123_: *mut leanh::LeanObject,
    mut v___x_1124_: *mut leanh::LeanObject,
    mut v_a_1125_: *mut leanh::LeanObject,
    mut v_b_1126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1127_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_1120_, v___x_1121_, v_numArgs_1122_, v_auxVars_1123_, v___x_1124_, v_a_1125_, v_b_1126_);
    leanh::lean_dec_ref(v___x_1124_);
    leanh::lean_dec_ref(v_auxVars_1123_);
    leanh::lean_dec(v_numArgs_1122_);
    leanh::lean_dec_ref(v___x_1121_);
    leanh::lean_dec(v_upperBound_1120_);
    return v_res_1127_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(
    mut v_i_1128_: *mut leanh::LeanObject,
    mut v_j_1129_: *mut leanh::LeanObject,
    mut v_bs_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_zero_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_1132_: u8 = 0;
    let mut v_auxPrefix_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_one_1134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_1135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_1131_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_1132_ = lean_nat_dec_eq(v_i_1128_, v_zero_1131_);
                if v_isZero_1132_ == 1 {
                    leanh::lean_dec(v_j_1129_);
                    leanh::lean_dec(v_i_1128_);
                    return v_bs_1130_;
                } else {
                    v_auxPrefix_1133_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1___closed__1;
                    v_one_1134_ = leanh::lean_unsigned_to_nat(1);
                    v_n_1135_ = lean_nat_sub(v_i_1128_, v_one_1134_);
                    leanh::lean_dec(v_i_1128_);
                    leanh::lean_inc(v_j_1129_);
                    v___x_1136_ = l_Lean_Name_num___override(v_auxPrefix_1133_, v_j_1129_);
                    v___x_1137_ = l_Lean_mkFVar(v___x_1136_);
                    v___x_1138_ = lean_nat_add(v_j_1129_, v_one_1134_);
                    leanh::lean_dec(v_j_1129_);
                    v___x_1139_ = lean_array_push(v_bs_1130_, v___x_1137_);
                    v_i_1128_ = v_n_1135_;
                    v_j_1129_ = v___x_1138_;
                    v_bs_1130_ = v___x_1139_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1141_ = leanh::lean_box(0);
    v___x_1142_ = leanh::lean_unsigned_to_nat(16);
    v___x_1143_ = lean_mk_array(v___x_1142_, v___x_1141_);
    return v___x_1143_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1144_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0_once
        ),
        _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__0,
    );
    v___x_1145_ = leanh::lean_unsigned_to_nat(0);
    v___x_1146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1146_, 0, v___x_1145_);
    leanh::lean_ctor_set(v___x_1146_, 1, v___x_1144_);
    return v___x_1146_;
}
pub unsafe fn _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1149_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__2;
    v___x_1150_ = leanh::lean_box(1);
    v___x_1151_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1_once
        ),
        _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__1,
    );
    v___x_1152_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1152_, 0, v___x_1151_);
    leanh::lean_ctor_set(v___x_1152_, 1, v___x_1150_);
    leanh::lean_ctor_set(v___x_1152_, 2, v___x_1149_);
    return v___x_1152_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(
    mut v_pattern_1155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_varTypes_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varInfos_x3f_1157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numArgs_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxVars_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarIds_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1169_: usize = 0;
    let mut v___x_1170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1171_: usize = 0;
    let mut v___x_1172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_1175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_1180_: usize = 0;
    let mut v___x_1181_: usize = 0;
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_varTypes_1156_ = leanh::lean_ctor_get(v_pattern_1155_, 1);
                leanh::lean_inc_ref(v_varTypes_1156_);
                v_varInfos_x3f_1157_ = leanh::lean_ctor_get(v_pattern_1155_, 2);
                leanh::lean_inc(v_varInfos_x3f_1157_);
                v_pattern_1158_ = leanh::lean_ctor_get(v_pattern_1155_, 3);
                leanh::lean_inc_ref(v_pattern_1158_);
                leanh::lean_dec_ref(v_pattern_1155_);
                v_numArgs_1159_ = lean_array_get_size(v_varTypes_1156_);
                if leanh::lean_obj_tag(v_varInfos_x3f_1157_) == 1 {
                    v_val_1179_ = leanh::lean_ctor_get(v_varInfos_x3f_1157_, 0);
                    leanh::lean_inc(v_val_1179_);
                    leanh::lean_dec_ref_known(v_varInfos_x3f_1157_, 1);
                    v_sz_1180_ = lean_array_size(v_val_1179_);
                    v___x_1181_ = 0usize;
                    v___x_1182_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__5(v_sz_1180_, v___x_1181_, v_val_1179_);
                    v___y_1161_ = v___x_1182_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_varInfos_x3f_1157_);
                    v___x_1183_ = 0;
                    v___x_1184_ = leanh::lean_box((v___x_1183_) as usize);
                    v___x_1185_ = lean_mk_array(v_numArgs_1159_, v___x_1184_);
                    v___y_1161_ = v___x_1185_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1162_ = leanh::lean_unsigned_to_nat(0);
                v___x_1163_ = lean_mk_empty_array_with_capacity(v_numArgs_1159_);
                leanh::lean_inc_ref(v___x_1163_);
                v_auxVars_1164_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_numArgs_1159_, v___x_1162_, v___x_1163_);
                v___x_1165_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3_once), _init_l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__3);
                v___x_1166_ = lean_expr_instantiate_rev(v_pattern_1158_, v_auxVars_1164_);
                leanh::lean_dec_ref(v_pattern_1158_);
                v___x_1167_ = l_Lean_collectFVars(v___x_1165_, v___x_1166_);
                v_fvarIds_1168_ = leanh::lean_ctor_get(v___x_1167_, 2);
                leanh::lean_inc_ref(v_fvarIds_1168_);
                leanh::lean_dec_ref(v___x_1167_);
                v_sz_1169_ = lean_array_size(v_fvarIds_1168_);
                v___x_1170_ =
                    l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos___closed__4;
                v___x_1171_ = 0usize;
                v___x_1172_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__1(v_fvarIds_1168_, v_sz_1169_, v___x_1171_, v___y_1161_);
                leanh::lean_dec_ref(v_fvarIds_1168_);
                v___x_1173_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_1164_, v_varTypes_1156_, v_numArgs_1159_, v___x_1162_, v___x_1163_);
                leanh::lean_dec_ref(v_varTypes_1156_);
                v___x_1174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_numArgs_1159_, v___x_1172_, v_numArgs_1159_, v_auxVars_1164_, v___x_1173_, v___x_1162_, v___x_1170_);
                leanh::lean_dec_ref(v___x_1173_);
                leanh::lean_dec_ref(v_auxVars_1164_);
                leanh::lean_dec_ref(v___x_1172_);
                v_fst_1175_ = leanh::lean_ctor_get(v___x_1174_, 0);
                leanh::lean_inc(v_fst_1175_);
                v_snd_1176_ = leanh::lean_ctor_get(v___x_1174_, 1);
                leanh::lean_inc(v_snd_1176_);
                leanh::lean_dec_ref(v___x_1174_);
                v___x_1177_ = l_Array_append___redArg(v_snd_1176_, v_fst_1175_);
                leanh::lean_dec(v_fst_1175_);
                v___x_1178_ = lean_array_to_list(v___x_1177_);
                return v___x_1178_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(
    mut v_as_1186_: *mut leanh::LeanObject,
    mut v_i_1187_: *mut leanh::LeanObject,
    mut v_j_1188_: *mut leanh::LeanObject,
    mut v_inv_1189_: *mut leanh::LeanObject,
    mut v_bs_1190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1191_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1191_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___redArg(v_i_1187_, v_j_1188_, v_bs_1190_);
    return v___x_1191_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0___boxed(
    mut v_as_1192_: *mut leanh::LeanObject,
    mut v_i_1193_: *mut leanh::LeanObject,
    mut v_j_1194_: *mut leanh::LeanObject,
    mut v_inv_1195_: *mut leanh::LeanObject,
    mut v_bs_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1197_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__0(v_as_1192_, v_i_1193_, v_j_1194_, v_inv_1195_, v_bs_1196_);
    leanh::lean_dec_ref(v_as_1192_);
    return v_res_1197_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(
    mut v_auxVars_1198_: *mut leanh::LeanObject,
    mut v_as_1199_: *mut leanh::LeanObject,
    mut v_i_1200_: *mut leanh::LeanObject,
    mut v_j_1201_: *mut leanh::LeanObject,
    mut v_inv_1202_: *mut leanh::LeanObject,
    mut v_bs_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1204_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___redArg(v_auxVars_1198_, v_as_1199_, v_i_1200_, v_j_1201_, v_bs_1203_);
    return v___x_1204_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2___boxed(
    mut v_auxVars_1205_: *mut leanh::LeanObject,
    mut v_as_1206_: *mut leanh::LeanObject,
    mut v_i_1207_: *mut leanh::LeanObject,
    mut v_j_1208_: *mut leanh::LeanObject,
    mut v_inv_1209_: *mut leanh::LeanObject,
    mut v_bs_1210_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Array_mapFinIdxM_map___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__2(v_auxVars_1205_, v_as_1206_, v_i_1207_, v_j_1208_, v_inv_1209_, v_bs_1210_);
    leanh::lean_dec_ref(v_as_1206_);
    leanh::lean_dec_ref(v_auxVars_1205_);
    return v_res_1211_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(
    mut v_upperBound_1212_: *mut leanh::LeanObject,
    mut v___x_1213_: *mut leanh::LeanObject,
    mut v___x_1214_: *mut leanh::LeanObject,
    mut v___x_1215_: *mut leanh::LeanObject,
    mut v_inst_1216_: *mut leanh::LeanObject,
    mut v_R_1217_: *mut leanh::LeanObject,
    mut v_a_1218_: *mut leanh::LeanObject,
    mut v_b_1219_: u8,
    mut v_c_1220_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1221_: u8 = 0;
    v___x_1221_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___redArg(v_upperBound_1212_, v___x_1213_, v___x_1214_, v___x_1215_, v_a_1218_, v_b_1219_);
    return v___x_1221_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3___boxed(
    mut v_upperBound_1222_: *mut leanh::LeanObject,
    mut v___x_1223_: *mut leanh::LeanObject,
    mut v___x_1224_: *mut leanh::LeanObject,
    mut v___x_1225_: *mut leanh::LeanObject,
    mut v_inst_1226_: *mut leanh::LeanObject,
    mut v_R_1227_: *mut leanh::LeanObject,
    mut v_a_1228_: *mut leanh::LeanObject,
    mut v_b_1229_: *mut leanh::LeanObject,
    mut v_c_1230_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_b_boxed_1231_: u8 = 0;
    let mut v_res_1232_: u8 = 0;
    let mut v_r_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_b_boxed_1231_ = (leanh::lean_unbox(v_b_1229_) as u8);
    v_res_1232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__3(v_upperBound_1222_, v___x_1223_, v___x_1224_, v___x_1225_, v_inst_1226_, v_R_1227_, v_a_1228_, v_b_boxed_1231_, v_c_1230_);
    leanh::lean_dec_ref(v___x_1225_);
    leanh::lean_dec_ref(v___x_1224_);
    leanh::lean_dec_ref(v___x_1223_);
    leanh::lean_dec(v_upperBound_1222_);
    v_r_1233_ = leanh::lean_box((v_res_1232_) as usize);
    return v_r_1233_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(
    mut v_upperBound_1234_: *mut leanh::LeanObject,
    mut v___x_1235_: *mut leanh::LeanObject,
    mut v_numArgs_1236_: *mut leanh::LeanObject,
    mut v_auxVars_1237_: *mut leanh::LeanObject,
    mut v___x_1238_: *mut leanh::LeanObject,
    mut v_inst_1239_: *mut leanh::LeanObject,
    mut v_R_1240_: *mut leanh::LeanObject,
    mut v_a_1241_: *mut leanh::LeanObject,
    mut v_b_1242_: *mut leanh::LeanObject,
    mut v_c_1243_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1244_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___redArg(v_upperBound_1234_, v___x_1235_, v_numArgs_1236_, v_auxVars_1237_, v___x_1238_, v_a_1241_, v_b_1242_);
    return v___x_1244_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4___boxed(
    mut v_upperBound_1245_: *mut leanh::LeanObject,
    mut v___x_1246_: *mut leanh::LeanObject,
    mut v_numArgs_1247_: *mut leanh::LeanObject,
    mut v_auxVars_1248_: *mut leanh::LeanObject,
    mut v___x_1249_: *mut leanh::LeanObject,
    mut v_inst_1250_: *mut leanh::LeanObject,
    mut v_R_1251_: *mut leanh::LeanObject,
    mut v_a_1252_: *mut leanh::LeanObject,
    mut v_b_1253_: *mut leanh::LeanObject,
    mut v_c_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos_spec__4(v_upperBound_1245_, v___x_1246_, v_numArgs_1247_, v_auxVars_1248_, v___x_1249_, v_inst_1250_, v_R_1251_, v_a_1252_, v_b_1253_, v_c_1254_);
    leanh::lean_dec_ref(v___x_1249_);
    leanh::lean_dec_ref(v_auxVars_1248_);
    leanh::lean_dec(v_numArgs_1247_);
    leanh::lean_dec_ref(v___x_1246_);
    leanh::lean_dec(v_upperBound_1245_);
    return v_res_1255_;
}
pub unsafe fn l_Lean_Meta_Sym_mkBackwardRuleFromDecl(
    mut v_declName_1256_: *mut leanh::LeanObject,
    mut v_num_x3f_1257_: *mut leanh::LeanObject,
    mut v_a_1258_: *mut leanh::LeanObject,
    mut v_a_1259_: *mut leanh::LeanObject,
    mut v_a_1260_: *mut leanh::LeanObject,
    mut v_a_1261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1267_: u8 = 0;
    let mut v___x_1268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1275_: u8 = 0;
    let mut v_a_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1279_: u8 = 0;
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1283_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_1256_);
                v___x_1263_ = l_Lean_Meta_Sym_mkPatternFromDecl(
                    v_declName_1256_,
                    v_num_x3f_1257_,
                    v_a_1258_,
                    v_a_1259_,
                    v_a_1260_,
                    v_a_1261_,
                );
                if leanh::lean_obj_tag(v___x_1263_) == 0 {
                    v_a_1264_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1275_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1275_ == 0 {
                        v___x_1266_ = v___x_1263_;
                        v_isShared_1267_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1264_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1266_ = leanh::lean_box(0);
                        v_isShared_1267_ = v_isSharedCheck_1275_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_1256_);
                    v_a_1276_ = leanh::lean_ctor_get(v___x_1263_, 0);
                    v_isSharedCheck_1283_ = (!leanh::lean_is_exclusive(v___x_1263_)) as u8;
                    if v_isSharedCheck_1283_ == 0 {
                        v___x_1278_ = v___x_1263_;
                        v_isShared_1279_ = v_isSharedCheck_1283_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1276_);
                        leanh::lean_dec(v___x_1263_);
                        v___x_1278_ = leanh::lean_box(0);
                        v_isShared_1279_ = v_isSharedCheck_1283_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_a_1264_);
                v___x_1268_ =
                    l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_1264_);
                v___x_1269_ = leanh::lean_box(0);
                v___x_1270_ = l_Lean_mkConst(v_declName_1256_, v___x_1269_);
                v___x_1271_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1271_, 0, v___x_1270_);
                leanh::lean_ctor_set(v___x_1271_, 1, v_a_1264_);
                leanh::lean_ctor_set(v___x_1271_, 2, v___x_1268_);
                if v_isShared_1267_ == 0 {
                    leanh::lean_ctor_set(v___x_1266_, 0, v___x_1271_);
                    v___x_1273_ = v___x_1266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1274_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1274_, 0, v___x_1271_);
                    v___x_1273_ = v_reuseFailAlloc_1274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1273_;
            }
            3 => {
                if v_isShared_1279_ == 0 {
                    v___x_1281_ = v___x_1278_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1282_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1282_, 0, v_a_1276_);
                    v___x_1281_ = v_reuseFailAlloc_1282_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1281_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkBackwardRuleFromDecl___boxed(
    mut v_declName_1284_: *mut leanh::LeanObject,
    mut v_num_x3f_1285_: *mut leanh::LeanObject,
    mut v_a_1286_: *mut leanh::LeanObject,
    mut v_a_1287_: *mut leanh::LeanObject,
    mut v_a_1288_: *mut leanh::LeanObject,
    mut v_a_1289_: *mut leanh::LeanObject,
    mut v_a_1290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1291_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(
        v_declName_1284_,
        v_num_x3f_1285_,
        v_a_1286_,
        v_a_1287_,
        v_a_1288_,
        v_a_1289_,
    );
    leanh::lean_dec(v_a_1289_);
    leanh::lean_dec_ref(v_a_1288_);
    leanh::lean_dec(v_a_1287_);
    leanh::lean_dec_ref(v_a_1286_);
    leanh::lean_dec(v_num_x3f_1285_);
    return v_res_1291_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(
    mut v_a_1292_: *mut leanh::LeanObject,
    mut v_a_1293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1299_: u8 = 0;
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1305_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1292_) == 0 {
                    v___x_1294_ = l_List_reverse___redArg(v_a_1293_);
                    return v___x_1294_;
                } else {
                    v_head_1295_ = leanh::lean_ctor_get(v_a_1292_, 0);
                    v_tail_1296_ = leanh::lean_ctor_get(v_a_1292_, 1);
                    v_isSharedCheck_1305_ = (!leanh::lean_is_exclusive(v_a_1292_)) as u8;
                    if v_isSharedCheck_1305_ == 0 {
                        v___x_1298_ = v_a_1292_;
                        v_isShared_1299_ = v_isSharedCheck_1305_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1296_);
                        leanh::lean_inc(v_head_1295_);
                        leanh::lean_dec(v_a_1292_);
                        v___x_1298_ = leanh::lean_box(0);
                        v_isShared_1299_ = v_isSharedCheck_1305_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1300_ = l_Lean_mkLevelParam(v_head_1295_);
                if v_isShared_1299_ == 0 {
                    leanh::lean_ctor_set(v___x_1298_, 1, v_a_1293_);
                    leanh::lean_ctor_set(v___x_1298_, 0, v___x_1300_);
                    v___x_1302_ = v___x_1298_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1304_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1300_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1304_, 1, v_a_1293_);
                    v___x_1302_ = v_reuseFailAlloc_1304_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1292_ = v_tail_1296_;
                v_a_1293_ = v___x_1302_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkBackwardRuleFromExpr(
    mut v_e_1306_: *mut leanh::LeanObject,
    mut v_levelParams_1307_: *mut leanh::LeanObject,
    mut v_num_x3f_1308_: *mut leanh::LeanObject,
    mut v_a_1309_: *mut leanh::LeanObject,
    mut v_a_1310_: *mut leanh::LeanObject,
    mut v_a_1311_: *mut leanh::LeanObject,
    mut v_a_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1318_: u8 = 0;
    let mut v_levelParams_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1328_: u8 = 0;
    let mut v_a_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1332_: u8 = 0;
    let mut v___x_1334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1336_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_levelParams_1307_);
                leanh::lean_inc_ref(v_e_1306_);
                v___x_1314_ = l_Lean_Meta_Sym_mkPatternFromExpr(
                    v_e_1306_,
                    v_levelParams_1307_,
                    v_num_x3f_1308_,
                    v_a_1309_,
                    v_a_1310_,
                    v_a_1311_,
                    v_a_1312_,
                );
                if leanh::lean_obj_tag(v___x_1314_) == 0 {
                    v_a_1315_ = leanh::lean_ctor_get(v___x_1314_, 0);
                    v_isSharedCheck_1328_ = (!leanh::lean_is_exclusive(v___x_1314_)) as u8;
                    if v_isSharedCheck_1328_ == 0 {
                        v___x_1317_ = v___x_1314_;
                        v_isShared_1318_ = v_isSharedCheck_1328_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1315_);
                        leanh::lean_dec(v___x_1314_);
                        v___x_1317_ = leanh::lean_box(0);
                        v_isShared_1318_ = v_isSharedCheck_1328_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_levelParams_1307_);
                    leanh::lean_dec_ref(v_e_1306_);
                    v_a_1329_ = leanh::lean_ctor_get(v___x_1314_, 0);
                    v_isSharedCheck_1336_ = (!leanh::lean_is_exclusive(v___x_1314_)) as u8;
                    if v_isSharedCheck_1336_ == 0 {
                        v___x_1331_ = v___x_1314_;
                        v_isShared_1332_ = v_isSharedCheck_1336_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1329_);
                        leanh::lean_dec(v___x_1314_);
                        v___x_1331_ = leanh::lean_box(0);
                        v_isShared_1332_ = v_isSharedCheck_1336_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_levelParams_1319_ = leanh::lean_ctor_get(v_a_1315_, 0);
                leanh::lean_inc(v_a_1315_);
                v___x_1320_ =
                    l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkResultPos(v_a_1315_);
                v___x_1321_ = leanh::lean_box(0);
                leanh::lean_inc(v_levelParams_1319_);
                v___x_1322_ =
                    l_List_mapTR_loop___at___00Lean_Meta_Sym_mkBackwardRuleFromExpr_spec__0(
                        v_levelParams_1319_,
                        v___x_1321_,
                    );
                v___x_1323_ =
                    l_Lean_Expr_instantiateLevelParams(v_e_1306_, v_levelParams_1307_, v___x_1322_);
                leanh::lean_dec_ref(v_e_1306_);
                v___x_1324_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_1324_, 0, v___x_1323_);
                leanh::lean_ctor_set(v___x_1324_, 1, v_a_1315_);
                leanh::lean_ctor_set(v___x_1324_, 2, v___x_1320_);
                if v_isShared_1318_ == 0 {
                    leanh::lean_ctor_set(v___x_1317_, 0, v___x_1324_);
                    v___x_1326_ = v___x_1317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1327_, 0, v___x_1324_);
                    v___x_1326_ = v_reuseFailAlloc_1327_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1326_;
            }
            3 => {
                if v_isShared_1332_ == 0 {
                    v___x_1334_ = v___x_1331_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1335_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1335_, 0, v_a_1329_);
                    v___x_1334_ = v_reuseFailAlloc_1335_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1334_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_mkBackwardRuleFromExpr___boxed(
    mut v_e_1337_: *mut leanh::LeanObject,
    mut v_levelParams_1338_: *mut leanh::LeanObject,
    mut v_num_x3f_1339_: *mut leanh::LeanObject,
    mut v_a_1340_: *mut leanh::LeanObject,
    mut v_a_1341_: *mut leanh::LeanObject,
    mut v_a_1342_: *mut leanh::LeanObject,
    mut v_a_1343_: *mut leanh::LeanObject,
    mut v_a_1344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1345_ = l_Lean_Meta_Sym_mkBackwardRuleFromExpr(
        v_e_1337_,
        v_levelParams_1338_,
        v_num_x3f_1339_,
        v_a_1340_,
        v_a_1341_,
        v_a_1342_,
        v_a_1343_,
    );
    leanh::lean_dec(v_a_1343_);
    leanh::lean_dec_ref(v_a_1342_);
    leanh::lean_dec(v_a_1341_);
    leanh::lean_dec_ref(v_a_1340_);
    leanh::lean_dec(v_num_x3f_1339_);
    return v_res_1345_;
}
pub unsafe fn l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(
    mut v_expr_1346_: *mut leanh::LeanObject,
    mut v_pattern_1347_: *mut leanh::LeanObject,
    mut v_result_1348_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_levelParams_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_expr_1346_) == 4 {
                    v_us_1355_ = leanh::lean_ctor_get(v_expr_1346_, 1);
                    if leanh::lean_obj_tag(v_us_1355_) == 0 {
                        leanh::lean_dec_ref(v_pattern_1347_);
                        v_declName_1356_ = leanh::lean_ctor_get(v_expr_1346_, 0);
                        leanh::lean_inc(v_declName_1356_);
                        leanh::lean_dec_ref_known(v_expr_1346_, 2);
                        v_us_1357_ = leanh::lean_ctor_get(v_result_1348_, 0);
                        leanh::lean_inc(v_us_1357_);
                        v_args_1358_ = leanh::lean_ctor_get(v_result_1348_, 1);
                        leanh::lean_inc_ref(v_args_1358_);
                        leanh::lean_dec_ref(v_result_1348_);
                        v___x_1359_ = l_Lean_mkConst(v_declName_1356_, v_us_1357_);
                        v___x_1360_ = l_Lean_mkAppN(v___x_1359_, v_args_1358_);
                        leanh::lean_dec_ref(v_args_1358_);
                        return v___x_1360_;
                    } else {
                        state = 1;
                        continue;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_levelParams_1350_ = leanh::lean_ctor_get(v_pattern_1347_, 0);
                leanh::lean_inc(v_levelParams_1350_);
                leanh::lean_dec_ref(v_pattern_1347_);
                v_us_1351_ = leanh::lean_ctor_get(v_result_1348_, 0);
                leanh::lean_inc(v_us_1351_);
                v_args_1352_ = leanh::lean_ctor_get(v_result_1348_, 1);
                leanh::lean_inc_ref(v_args_1352_);
                leanh::lean_dec_ref(v_result_1348_);
                v___x_1353_ = l_Lean_Expr_instantiateLevelParams(
                    v_expr_1346_,
                    v_levelParams_1350_,
                    v_us_1351_,
                );
                leanh::lean_dec_ref(v_expr_1346_);
                v___x_1354_ = l_Lean_mkAppN(v___x_1353_, v_args_1352_);
                leanh::lean_dec_ref(v_args_1352_);
                return v___x_1354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_ctorIdx(
    mut v_x_1361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_1361_) == 0 {
        let mut v___x_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1362_ = leanh::lean_unsigned_to_nat(0);
        return v___x_1362_;
    } else {
        let mut v___x_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1363_ = leanh::lean_unsigned_to_nat(1);
        return v___x_1363_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_ctorIdx___boxed(
    mut v_x_1364_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1365_ = l_Lean_Meta_Sym_ApplyResult_ctorIdx(v_x_1364_);
    leanh::lean_dec(v_x_1364_);
    return v_res_1365_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(
    mut v_t_1366_: *mut leanh::LeanObject,
    mut v_k_1367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_t_1366_) == 0 {
        return v_k_1367_;
    } else {
        let mut v_mvarIds_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_mvarIds_1368_ = leanh::lean_ctor_get(v_t_1366_, 0);
        leanh::lean_inc(v_mvarIds_1368_);
        leanh::lean_dec_ref_known(v_t_1366_, 1);
        v___x_1369_ = leanh::lean_apply_1(v_k_1367_, v_mvarIds_1368_);
        return v___x_1369_;
    }
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_ctorElim(
    mut v_motive_1370_: *mut leanh::LeanObject,
    mut v_ctorIdx_1371_: *mut leanh::LeanObject,
    mut v_t_1372_: *mut leanh::LeanObject,
    mut v_h_1373_: *mut leanh::LeanObject,
    mut v_k_1374_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1375_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_1372_, v_k_1374_);
    return v___x_1375_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_ctorElim___boxed(
    mut v_motive_1376_: *mut leanh::LeanObject,
    mut v_ctorIdx_1377_: *mut leanh::LeanObject,
    mut v_t_1378_: *mut leanh::LeanObject,
    mut v_h_1379_: *mut leanh::LeanObject,
    mut v_k_1380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1381_ = l_Lean_Meta_Sym_ApplyResult_ctorElim(
        v_motive_1376_,
        v_ctorIdx_1377_,
        v_t_1378_,
        v_h_1379_,
        v_k_1380_,
    );
    leanh::lean_dec(v_ctorIdx_1377_);
    return v_res_1381_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_failed_elim___redArg(
    mut v_t_1382_: *mut leanh::LeanObject,
    mut v_failed_1383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1384_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_1382_, v_failed_1383_);
    return v___x_1384_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_failed_elim(
    mut v_motive_1385_: *mut leanh::LeanObject,
    mut v_t_1386_: *mut leanh::LeanObject,
    mut v_h_1387_: *mut leanh::LeanObject,
    mut v_failed_1388_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1389_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_1386_, v_failed_1388_);
    return v___x_1389_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_goals_elim___redArg(
    mut v_t_1390_: *mut leanh::LeanObject,
    mut v_goals_1391_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1392_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1392_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_1390_, v_goals_1391_);
    return v___x_1392_;
}
pub unsafe fn l_Lean_Meta_Sym_ApplyResult_goals_elim(
    mut v_motive_1393_: *mut leanh::LeanObject,
    mut v_t_1394_: *mut leanh::LeanObject,
    mut v_h_1395_: *mut leanh::LeanObject,
    mut v_goals_1396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1397_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1397_ = l_Lean_Meta_Sym_ApplyResult_ctorElim___redArg(v_t_1394_, v_goals_1396_);
    return v___x_1397_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(
    mut v_x_1398_: *mut leanh::LeanObject,
    mut v___y_1399_: *mut leanh::LeanObject,
    mut v___y_1400_: *mut leanh::LeanObject,
    mut v___y_1401_: *mut leanh::LeanObject,
    mut v___y_1402_: *mut leanh::LeanObject,
    mut v___y_1403_: *mut leanh::LeanObject,
    mut v___y_1404_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_1400_);
    leanh::lean_inc_ref(v___y_1399_);
    v___x_1406_ = leanh::lean_apply_7(
        v_x_1398_,
        v___y_1399_,
        v___y_1400_,
        v___y_1401_,
        v___y_1402_,
        v___y_1403_,
        v___y_1404_,
        leanh::lean_box(0),
    );
    return v___x_1406_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed(
    mut v_x_1407_: *mut leanh::LeanObject,
    mut v___y_1408_: *mut leanh::LeanObject,
    mut v___y_1409_: *mut leanh::LeanObject,
    mut v___y_1410_: *mut leanh::LeanObject,
    mut v___y_1411_: *mut leanh::LeanObject,
    mut v___y_1412_: *mut leanh::LeanObject,
    mut v___y_1413_: *mut leanh::LeanObject,
    mut v___y_1414_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1415_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0(v_x_1407_, v___y_1408_, v___y_1409_, v___y_1410_, v___y_1411_, v___y_1412_, v___y_1413_);
    leanh::lean_dec(v___y_1409_);
    leanh::lean_dec_ref(v___y_1408_);
    return v_res_1415_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(
    mut v_mvarId_1416_: *mut leanh::LeanObject,
    mut v_x_1417_: *mut leanh::LeanObject,
    mut v___y_1418_: *mut leanh::LeanObject,
    mut v___y_1419_: *mut leanh::LeanObject,
    mut v___y_1420_: *mut leanh::LeanObject,
    mut v___y_1421_: *mut leanh::LeanObject,
    mut v___y_1422_: *mut leanh::LeanObject,
    mut v___y_1423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1430_: u8 = 0;
    let mut v___x_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1434_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v___y_1419_);
                leanh::lean_inc_ref(v___y_1418_);
                v___f_1425_ = leanh::lean_alloc_closure(l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 3);
                leanh::lean_closure_set(v___f_1425_, 0, v_x_1417_);
                leanh::lean_closure_set(v___f_1425_, 1, v___y_1418_);
                leanh::lean_closure_set(v___f_1425_, 2, v___y_1419_);
                v___x_1426_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(
                    leanh::lean_box(0),
                    v_mvarId_1416_,
                    v___f_1425_,
                    v___y_1420_,
                    v___y_1421_,
                    v___y_1422_,
                    v___y_1423_,
                );
                if leanh::lean_obj_tag(v___x_1426_) == 0 {
                    return v___x_1426_;
                } else {
                    v_a_1427_ = leanh::lean_ctor_get(v___x_1426_, 0);
                    v_isSharedCheck_1434_ = (!leanh::lean_is_exclusive(v___x_1426_)) as u8;
                    if v_isSharedCheck_1434_ == 0 {
                        v___x_1429_ = v___x_1426_;
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1427_);
                        leanh::lean_dec(v___x_1426_);
                        v___x_1429_ = leanh::lean_box(0);
                        v_isShared_1430_ = v_isSharedCheck_1434_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_1430_ == 0 {
                    v___x_1432_ = v___x_1429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1433_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1433_, 0, v_a_1427_);
                    v___x_1432_ = v_reuseFailAlloc_1433_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1432_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg___boxed(
    mut v_mvarId_1435_: *mut leanh::LeanObject,
    mut v_x_1436_: *mut leanh::LeanObject,
    mut v___y_1437_: *mut leanh::LeanObject,
    mut v___y_1438_: *mut leanh::LeanObject,
    mut v___y_1439_: *mut leanh::LeanObject,
    mut v___y_1440_: *mut leanh::LeanObject,
    mut v___y_1441_: *mut leanh::LeanObject,
    mut v___y_1442_: *mut leanh::LeanObject,
    mut v___y_1443_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1444_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1444_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(
            v_mvarId_1435_,
            v_x_1436_,
            v___y_1437_,
            v___y_1438_,
            v___y_1439_,
            v___y_1440_,
            v___y_1441_,
            v___y_1442_,
        );
    leanh::lean_dec(v___y_1442_);
    leanh::lean_dec_ref(v___y_1441_);
    leanh::lean_dec(v___y_1440_);
    leanh::lean_dec_ref(v___y_1439_);
    leanh::lean_dec(v___y_1438_);
    leanh::lean_dec_ref(v___y_1437_);
    return v_res_1444_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(
    mut v_00_u03b1_1445_: *mut leanh::LeanObject,
    mut v_mvarId_1446_: *mut leanh::LeanObject,
    mut v_x_1447_: *mut leanh::LeanObject,
    mut v___y_1448_: *mut leanh::LeanObject,
    mut v___y_1449_: *mut leanh::LeanObject,
    mut v___y_1450_: *mut leanh::LeanObject,
    mut v___y_1451_: *mut leanh::LeanObject,
    mut v___y_1452_: *mut leanh::LeanObject,
    mut v___y_1453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1455_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(
            v_mvarId_1446_,
            v_x_1447_,
            v___y_1448_,
            v___y_1449_,
            v___y_1450_,
            v___y_1451_,
            v___y_1452_,
            v___y_1453_,
        );
    return v___x_1455_;
}
pub unsafe fn l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___boxed(
    mut v_00_u03b1_1456_: *mut leanh::LeanObject,
    mut v_mvarId_1457_: *mut leanh::LeanObject,
    mut v_x_1458_: *mut leanh::LeanObject,
    mut v___y_1459_: *mut leanh::LeanObject,
    mut v___y_1460_: *mut leanh::LeanObject,
    mut v___y_1461_: *mut leanh::LeanObject,
    mut v___y_1462_: *mut leanh::LeanObject,
    mut v___y_1463_: *mut leanh::LeanObject,
    mut v___y_1464_: *mut leanh::LeanObject,
    mut v___y_1465_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1466_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1466_ = l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2(
        v_00_u03b1_1456_,
        v_mvarId_1457_,
        v_x_1458_,
        v___y_1459_,
        v___y_1460_,
        v___y_1461_,
        v___y_1462_,
        v___y_1463_,
        v___y_1464_,
    );
    leanh::lean_dec(v___y_1464_);
    leanh::lean_dec_ref(v___y_1463_);
    leanh::lean_dec(v___y_1462_);
    leanh::lean_dec_ref(v___y_1461_);
    leanh::lean_dec(v___y_1460_);
    leanh::lean_dec_ref(v___y_1459_);
    return v_res_1466_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(
    mut v_val_1467_: *mut leanh::LeanObject,
    mut v_a_1468_: *mut leanh::LeanObject,
    mut v_a_1469_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1475_: u8 = 0;
    let mut v_args_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1484_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_1468_) == 0 {
                    v___x_1470_ = l_List_reverse___redArg(v_a_1469_);
                    return v___x_1470_;
                } else {
                    v_head_1471_ = leanh::lean_ctor_get(v_a_1468_, 0);
                    v_tail_1472_ = leanh::lean_ctor_get(v_a_1468_, 1);
                    v_isSharedCheck_1484_ = (!leanh::lean_is_exclusive(v_a_1468_)) as u8;
                    if v_isSharedCheck_1484_ == 0 {
                        v___x_1474_ = v_a_1468_;
                        v_isShared_1475_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_1472_);
                        leanh::lean_inc(v_head_1471_);
                        leanh::lean_dec(v_a_1468_);
                        v___x_1474_ = leanh::lean_box(0);
                        v_isShared_1475_ = v_isSharedCheck_1484_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_args_1476_ = leanh::lean_ctor_get(v_val_1467_, 1);
                v___x_1477_ = l_Lean_instInhabitedExpr;
                v___x_1478_ = lean_array_get_borrowed(v___x_1477_, v_args_1476_, v_head_1471_);
                leanh::lean_dec(v_head_1471_);
                v___x_1479_ = l_Lean_Expr_mvarId_x21(v___x_1478_);
                if v_isShared_1475_ == 0 {
                    leanh::lean_ctor_set(v___x_1474_, 1, v_a_1469_);
                    leanh::lean_ctor_set(v___x_1474_, 0, v___x_1479_);
                    v___x_1481_ = v___x_1474_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1483_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 0, v___x_1479_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1483_, 1, v_a_1469_);
                    v___x_1481_ = v_reuseFailAlloc_1483_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1468_ = v_tail_1472_;
                v_a_1469_ = v___x_1481_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1___boxed(
    mut v_val_1485_: *mut leanh::LeanObject,
    mut v_a_1486_: *mut leanh::LeanObject,
    mut v_a_1487_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1488_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(
        v_val_1485_,
        v_a_1486_,
        v_a_1487_,
    );
    leanh::lean_dec_ref(v_val_1485_);
    return v_res_1488_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(
    mut v_x_1489_: *mut leanh::LeanObject,
    mut v_x_1490_: *mut leanh::LeanObject,
    mut v_x_1491_: *mut leanh::LeanObject,
    mut v_x_1492_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_1493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1497_: u8 = 0;
    let mut v___x_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1499_: u8 = 0;
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: u8 = 0;
    let mut v___x_1508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1518_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_1493_ = leanh::lean_ctor_get(v_x_1489_, 0);
                v_vs_1494_ = leanh::lean_ctor_get(v_x_1489_, 1);
                v_isSharedCheck_1518_ = (!leanh::lean_is_exclusive(v_x_1489_)) as u8;
                if v_isSharedCheck_1518_ == 0 {
                    v___x_1496_ = v_x_1489_;
                    v_isShared_1497_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_1494_);
                    leanh::lean_inc(v_ks_1493_);
                    leanh::lean_dec(v_x_1489_);
                    v___x_1496_ = leanh::lean_box(0);
                    v_isShared_1497_ = v_isSharedCheck_1518_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1498_ = lean_array_get_size(v_ks_1493_);
                v___x_1499_ = lean_nat_dec_lt(v_x_1490_, v___x_1498_);
                if v___x_1499_ == 0 {
                    leanh::lean_dec(v_x_1490_);
                    v___x_1500_ = lean_array_push(v_ks_1493_, v_x_1491_);
                    v___x_1501_ = lean_array_push(v_vs_1494_, v_x_1492_);
                    if v_isShared_1497_ == 0 {
                        leanh::lean_ctor_set(v___x_1496_, 1, v___x_1501_);
                        leanh::lean_ctor_set(v___x_1496_, 0, v___x_1500_);
                        v___x_1503_ = v___x_1496_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1504_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 0, v___x_1500_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1504_, 1, v___x_1501_);
                        v___x_1503_ = v_reuseFailAlloc_1504_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_1505_ = lean_array_fget_borrowed(v_ks_1493_, v_x_1490_);
                    v___x_1506_ = l_Lean_instBEqMVarId_beq(v_x_1491_, v_k_x27_1505_);
                    if v___x_1506_ == 0 {
                        if v_isShared_1497_ == 0 {
                            v___x_1508_ = v___x_1496_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_1512_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_ks_1493_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1512_, 1, v_vs_1494_);
                            v___x_1508_ = v_reuseFailAlloc_1512_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_1513_ = lean_array_fset(v_ks_1493_, v_x_1490_, v_x_1491_);
                        v___x_1514_ = lean_array_fset(v_vs_1494_, v_x_1490_, v_x_1492_);
                        leanh::lean_dec(v_x_1490_);
                        if v_isShared_1497_ == 0 {
                            leanh::lean_ctor_set(v___x_1496_, 1, v___x_1514_);
                            leanh::lean_ctor_set(v___x_1496_, 0, v___x_1513_);
                            v___x_1516_ = v___x_1496_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_1517_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 0, v___x_1513_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_1517_, 1, v___x_1514_);
                            v___x_1516_ = v_reuseFailAlloc_1517_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1503_;
            }
            3 => {
                v___x_1509_ = leanh::lean_unsigned_to_nat(1);
                v___x_1510_ = lean_nat_add(v_x_1490_, v___x_1509_);
                leanh::lean_dec(v_x_1490_);
                v_x_1489_ = v___x_1508_;
                v_x_1490_ = v___x_1510_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_1516_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(
    mut v_n_1519_: *mut leanh::LeanObject,
    mut v_k_1520_: *mut leanh::LeanObject,
    mut v_v_1521_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1523_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1522_ = leanh::lean_unsigned_to_nat(0);
    v___x_1523_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_n_1519_, v___x_1522_, v_k_1520_, v_v_1521_);
    return v___x_1523_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0()
-> usize {
    let mut v___x_1524_: usize = 0;
    let mut v___x_1525_: usize = 0;
    let mut v___x_1526_: usize = 0;
    v___x_1524_ = 5usize;
    v___x_1525_ = 1usize;
    v___x_1526_ = lean_usize_shift_left(v___x_1525_, v___x_1524_);
    return v___x_1526_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1()
-> usize {
    let mut v___x_1527_: usize = 0;
    let mut v___x_1528_: usize = 0;
    let mut v___x_1529_: usize = 0;
    v___x_1527_ = 1usize;
    v___x_1528_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__0);
    v___x_1529_ = lean_usize_sub(v___x_1528_, v___x_1527_);
    return v___x_1529_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1530_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1530_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(
    mut v_x_1531_: *mut leanh::LeanObject,
    mut v_x_1532_: usize,
    mut v_x_1533_: usize,
    mut v_x_1534_: *mut leanh::LeanObject,
    mut v_x_1535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: usize = 0;
    let mut v___x_1538_: usize = 0;
    let mut v___x_1539_: usize = 0;
    let mut v___x_1540_: usize = 0;
    let mut v_j_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1543_: u8 = 0;
    let mut v___x_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1546_: u8 = 0;
    let mut v_v_1547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1560_: u8 = 0;
    let mut v___x_1561_: u8 = 0;
    let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1567_: u8 = 0;
    let mut v_node_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1571_: u8 = 0;
    let mut v___x_1572_: usize = 0;
    let mut v___x_1573_: usize = 0;
    let mut v___x_1574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1578_: u8 = 0;
    let mut v___x_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1580_: u8 = 0;
    let mut v_unused_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1586_: u8 = 0;
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_1591_: u8 = 0;
    let mut v_ks_1592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1597_: usize = 0;
    let mut v___x_1598_: u8 = 0;
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: u8 = 0;
    let mut v_reuseFailAlloc_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1603_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_1531_) == 0 {
                    v_es_1536_ = leanh::lean_ctor_get(v_x_1531_, 0);
                    v___x_1537_ = 5usize;
                    v___x_1538_ = 1usize;
                    v___x_1539_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__1);
                    v___x_1540_ = lean_usize_land(v_x_1532_, v___x_1539_);
                    v_j_1541_ = lean_usize_to_nat(v___x_1540_);
                    v___x_1542_ = lean_array_get_size(v_es_1536_);
                    v___x_1543_ = lean_nat_dec_lt(v_j_1541_, v___x_1542_);
                    if v___x_1543_ == 0 {
                        leanh::lean_dec(v_j_1541_);
                        leanh::lean_dec(v_x_1535_);
                        leanh::lean_dec(v_x_1534_);
                        return v_x_1531_;
                    } else {
                        leanh::lean_inc_ref(v_es_1536_);
                        v_isSharedCheck_1580_ = (!leanh::lean_is_exclusive(v_x_1531_)) as u8;
                        if v_isSharedCheck_1580_ == 0 {
                            v_unused_1581_ = leanh::lean_ctor_get(v_x_1531_, 0);
                            leanh::lean_dec(v_unused_1581_);
                            v___x_1545_ = v_x_1531_;
                            v_isShared_1546_ = v_isSharedCheck_1580_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_1531_);
                            v___x_1545_ = leanh::lean_box(0);
                            v_isShared_1546_ = v_isSharedCheck_1580_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_1582_ = leanh::lean_ctor_get(v_x_1531_, 0);
                    v_vs_1583_ = leanh::lean_ctor_get(v_x_1531_, 1);
                    v_isSharedCheck_1603_ = (!leanh::lean_is_exclusive(v_x_1531_)) as u8;
                    if v_isSharedCheck_1603_ == 0 {
                        v___x_1585_ = v_x_1531_;
                        v_isShared_1586_ = v_isSharedCheck_1603_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_1583_);
                        leanh::lean_inc(v_ks_1582_);
                        leanh::lean_dec(v_x_1531_);
                        v___x_1585_ = leanh::lean_box(0);
                        v_isShared_1586_ = v_isSharedCheck_1603_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_1547_ = lean_array_fget(v_es_1536_, v_j_1541_);
                v___x_1548_ = leanh::lean_box(0);
                v_xs_x27_1549_ = lean_array_fset(v_es_1536_, v_j_1541_, v___x_1548_);
                match leanh::lean_obj_tag(v_v_1547_) {
                    0 => {
                        v_key_1556_ = leanh::lean_ctor_get(v_v_1547_, 0);
                        v_val_1557_ = leanh::lean_ctor_get(v_v_1547_, 1);
                        v_isSharedCheck_1567_ = (!leanh::lean_is_exclusive(v_v_1547_)) as u8;
                        if v_isSharedCheck_1567_ == 0 {
                            v___x_1559_ = v_v_1547_;
                            v_isShared_1560_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_1557_);
                            leanh::lean_inc(v_key_1556_);
                            leanh::lean_dec(v_v_1547_);
                            v___x_1559_ = leanh::lean_box(0);
                            v_isShared_1560_ = v_isSharedCheck_1567_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1568_ = leanh::lean_ctor_get(v_v_1547_, 0);
                        v_isSharedCheck_1578_ = (!leanh::lean_is_exclusive(v_v_1547_)) as u8;
                        if v_isSharedCheck_1578_ == 0 {
                            v___x_1570_ = v_v_1547_;
                            v_isShared_1571_ = v_isSharedCheck_1578_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_1568_);
                            leanh::lean_dec(v_v_1547_);
                            v___x_1570_ = leanh::lean_box(0);
                            v_isShared_1571_ = v_isSharedCheck_1578_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1579_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1579_, 0, v_x_1534_);
                        leanh::lean_ctor_set(v___x_1579_, 1, v_x_1535_);
                        v___y_1551_ = v___x_1579_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1552_ = lean_array_fset(v_xs_x27_1549_, v_j_1541_, v___y_1551_);
                leanh::lean_dec(v_j_1541_);
                if v_isShared_1546_ == 0 {
                    leanh::lean_ctor_set(v___x_1545_, 0, v___x_1552_);
                    v___x_1554_ = v___x_1545_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1555_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1552_);
                    v___x_1554_ = v_reuseFailAlloc_1555_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1554_;
            }
            4 => {
                v___x_1561_ = l_Lean_instBEqMVarId_beq(v_x_1534_, v_key_1556_);
                if v___x_1561_ == 0 {
                    leanh::lean_del_object(v___x_1559_);
                    v___x_1562_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_1556_,
                        v_val_1557_,
                        v_x_1534_,
                        v_x_1535_,
                    );
                    v___x_1563_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1563_, 0, v___x_1562_);
                    v___y_1551_ = v___x_1563_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_1557_);
                    leanh::lean_dec(v_key_1556_);
                    if v_isShared_1560_ == 0 {
                        leanh::lean_ctor_set(v___x_1559_, 1, v_x_1535_);
                        leanh::lean_ctor_set(v___x_1559_, 0, v_x_1534_);
                        v___x_1565_ = v___x_1559_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_1566_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 0, v_x_1534_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1566_, 1, v_x_1535_);
                        v___x_1565_ = v_reuseFailAlloc_1566_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_1551_ = v___x_1565_;
                state = 2;
                continue;
            }
            6 => {
                v___x_1572_ = lean_usize_shift_right(v_x_1532_, v___x_1537_);
                v___x_1573_ = lean_usize_add(v_x_1533_, v___x_1538_);
                v___x_1574_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_node_1568_, v___x_1572_, v___x_1573_, v_x_1534_, v_x_1535_);
                if v_isShared_1571_ == 0 {
                    leanh::lean_ctor_set(v___x_1570_, 0, v___x_1574_);
                    v___x_1576_ = v___x_1570_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1577_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1577_, 0, v___x_1574_);
                    v___x_1576_ = v_reuseFailAlloc_1577_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_1551_ = v___x_1576_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_1586_ == 0 {
                    v___x_1588_ = v___x_1585_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1602_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_ks_1582_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1602_, 1, v_vs_1583_);
                    v___x_1588_ = v_reuseFailAlloc_1602_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_1589_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v___x_1588_, v_x_1534_, v_x_1535_);
                v___x_1597_ = 7usize;
                v___x_1598_ = lean_usize_dec_le(v___x_1597_, v_x_1533_);
                if v___x_1598_ == 0 {
                    v___x_1599_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1589_);
                    v___x_1600_ = leanh::lean_unsigned_to_nat(4);
                    v___x_1601_ = lean_nat_dec_lt(v___x_1599_, v___x_1600_);
                    leanh::lean_dec(v___x_1599_);
                    v___y_1591_ = v___x_1601_;
                    state = 10;
                    continue;
                } else {
                    v___y_1591_ = v___x_1598_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_1591_ == 0 {
                    v_ks_1592_ = leanh::lean_ctor_get(v_newNode_1589_, 0);
                    leanh::lean_inc_ref(v_ks_1592_);
                    v_vs_1593_ = leanh::lean_ctor_get(v_newNode_1589_, 1);
                    leanh::lean_inc_ref(v_vs_1593_);
                    leanh::lean_dec_ref(v_newNode_1589_);
                    v___x_1594_ = leanh::lean_unsigned_to_nat(0);
                    v___x_1595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___closed__2);
                    v___x_1596_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_x_1533_, v_ks_1592_, v_vs_1593_, v___x_1594_, v___x_1595_);
                    leanh::lean_dec_ref(v_vs_1593_);
                    leanh::lean_dec_ref(v_ks_1592_);
                    return v___x_1596_;
                } else {
                    return v_newNode_1589_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(
    mut v_depth_1604_: usize,
    mut v_keys_1605_: *mut leanh::LeanObject,
    mut v_vals_1606_: *mut leanh::LeanObject,
    mut v_i_1607_: *mut leanh::LeanObject,
    mut v_entries_1608_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1610_: u8 = 0;
    let mut v_k_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1613_: u64 = 0;
    let mut v_h_1614_: usize = 0;
    let mut v___x_1615_: usize = 0;
    let mut v___x_1616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: usize = 0;
    let mut v___x_1618_: usize = 0;
    let mut v___x_1619_: usize = 0;
    let mut v_h_1620_: usize = 0;
    let mut v___x_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1609_ = lean_array_get_size(v_keys_1605_);
                v___x_1610_ = lean_nat_dec_lt(v_i_1607_, v___x_1609_);
                if v___x_1610_ == 0 {
                    leanh::lean_dec(v_i_1607_);
                    return v_entries_1608_;
                } else {
                    v_k_1611_ = lean_array_fget_borrowed(v_keys_1605_, v_i_1607_);
                    v_v_1612_ = lean_array_fget_borrowed(v_vals_1606_, v_i_1607_);
                    v___x_1613_ = l_Lean_instHashableMVarId_hash(v_k_1611_);
                    v_h_1614_ = lean_uint64_to_usize(v___x_1613_);
                    v___x_1615_ = 5usize;
                    v___x_1616_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1617_ = 1usize;
                    v___x_1618_ = lean_usize_sub(v_depth_1604_, v___x_1617_);
                    v___x_1619_ = lean_usize_mul(v___x_1615_, v___x_1618_);
                    v_h_1620_ = lean_usize_shift_right(v_h_1614_, v___x_1619_);
                    v___x_1621_ = lean_nat_add(v_i_1607_, v___x_1616_);
                    leanh::lean_dec(v_i_1607_);
                    leanh::lean_inc(v_v_1612_);
                    leanh::lean_inc(v_k_1611_);
                    v___x_1622_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_entries_1608_, v_h_1620_, v_depth_1604_, v_k_1611_, v_v_1612_);
                    v_i_1607_ = v___x_1621_;
                    v_entries_1608_ = v___x_1622_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg___boxed(
    mut v_depth_1624_: *mut leanh::LeanObject,
    mut v_keys_1625_: *mut leanh::LeanObject,
    mut v_vals_1626_: *mut leanh::LeanObject,
    mut v_i_1627_: *mut leanh::LeanObject,
    mut v_entries_1628_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1629_: usize = 0;
    let mut v_res_1630_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1629_ = leanh::lean_unbox_usize(v_depth_1624_);
    leanh::lean_dec(v_depth_1624_);
    v_res_1630_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_boxed_1629_, v_keys_1625_, v_vals_1626_, v_i_1627_, v_entries_1628_);
    leanh::lean_dec_ref(v_vals_1626_);
    leanh::lean_dec_ref(v_keys_1625_);
    return v_res_1630_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_x_1631_: *mut leanh::LeanObject,
    mut v_x_1632_: *mut leanh::LeanObject,
    mut v_x_1633_: *mut leanh::LeanObject,
    mut v_x_1634_: *mut leanh::LeanObject,
    mut v_x_1635_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2825__boxed_1636_: usize = 0;
    let mut v_x_2826__boxed_1637_: usize = 0;
    let mut v_res_1638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2825__boxed_1636_ = leanh::lean_unbox_usize(v_x_1632_);
    leanh::lean_dec(v_x_1632_);
    v_x_2826__boxed_1637_ = leanh::lean_unbox_usize(v_x_1633_);
    leanh::lean_dec(v_x_1633_);
    v_res_1638_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_1631_, v_x_2825__boxed_1636_, v_x_2826__boxed_1637_, v_x_1634_, v_x_1635_);
    return v_res_1638_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(
    mut v_x_1639_: *mut leanh::LeanObject,
    mut v_x_1640_: *mut leanh::LeanObject,
    mut v_x_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1642_: u64 = 0;
    let mut v___x_1643_: usize = 0;
    let mut v___x_1644_: usize = 0;
    let mut v___x_1645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1642_ = l_Lean_instHashableMVarId_hash(v_x_1640_);
    v___x_1643_ = lean_uint64_to_usize(v___x_1642_);
    v___x_1644_ = 1usize;
    v___x_1645_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_1639_, v___x_1643_, v___x_1644_, v_x_1640_, v_x_1641_);
    return v___x_1645_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(
    mut v_mvarId_1646_: *mut leanh::LeanObject,
    mut v_val_1647_: *mut leanh::LeanObject,
    mut v___y_1648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_1652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_1653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_1654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_1655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1658_: u8 = 0;
    let mut v_depth_1659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelAssignDepth_1660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lmvarCounter_1661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mvarCounter_1662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lDecls_1663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_decls_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_userNames_1665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lAssignment_1666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eAssignment_1667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dAssignment_1668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1671_: u8 = 0;
    let mut v___x_1672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut v_isSharedCheck_1683_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1650_ = lean_st_ref_take(v___y_1648_);
                v_mctx_1651_ = leanh::lean_ctor_get(v___x_1650_, 0);
                v_cache_1652_ = leanh::lean_ctor_get(v___x_1650_, 1);
                v_zetaDeltaFVarIds_1653_ = leanh::lean_ctor_get(v___x_1650_, 2);
                v_postponed_1654_ = leanh::lean_ctor_get(v___x_1650_, 3);
                v_diag_1655_ = leanh::lean_ctor_get(v___x_1650_, 4);
                v_isSharedCheck_1683_ = (!leanh::lean_is_exclusive(v___x_1650_)) as u8;
                if v_isSharedCheck_1683_ == 0 {
                    v___x_1657_ = v___x_1650_;
                    v_isShared_1658_ = v_isSharedCheck_1683_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_1655_);
                    leanh::lean_inc(v_postponed_1654_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_1653_);
                    leanh::lean_inc(v_cache_1652_);
                    leanh::lean_inc(v_mctx_1651_);
                    leanh::lean_dec(v___x_1650_);
                    v___x_1657_ = leanh::lean_box(0);
                    v_isShared_1658_ = v_isSharedCheck_1683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_depth_1659_ = leanh::lean_ctor_get(v_mctx_1651_, 0);
                v_levelAssignDepth_1660_ = leanh::lean_ctor_get(v_mctx_1651_, 1);
                v_lmvarCounter_1661_ = leanh::lean_ctor_get(v_mctx_1651_, 2);
                v_mvarCounter_1662_ = leanh::lean_ctor_get(v_mctx_1651_, 3);
                v_lDecls_1663_ = leanh::lean_ctor_get(v_mctx_1651_, 4);
                v_decls_1664_ = leanh::lean_ctor_get(v_mctx_1651_, 5);
                v_userNames_1665_ = leanh::lean_ctor_get(v_mctx_1651_, 6);
                v_lAssignment_1666_ = leanh::lean_ctor_get(v_mctx_1651_, 7);
                v_eAssignment_1667_ = leanh::lean_ctor_get(v_mctx_1651_, 8);
                v_dAssignment_1668_ = leanh::lean_ctor_get(v_mctx_1651_, 9);
                v_isSharedCheck_1682_ = (!leanh::lean_is_exclusive(v_mctx_1651_)) as u8;
                if v_isSharedCheck_1682_ == 0 {
                    v___x_1670_ = v_mctx_1651_;
                    v_isShared_1671_ = v_isSharedCheck_1682_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_dAssignment_1668_);
                    leanh::lean_inc(v_eAssignment_1667_);
                    leanh::lean_inc(v_lAssignment_1666_);
                    leanh::lean_inc(v_userNames_1665_);
                    leanh::lean_inc(v_decls_1664_);
                    leanh::lean_inc(v_lDecls_1663_);
                    leanh::lean_inc(v_mvarCounter_1662_);
                    leanh::lean_inc(v_lmvarCounter_1661_);
                    leanh::lean_inc(v_levelAssignDepth_1660_);
                    leanh::lean_inc(v_depth_1659_);
                    leanh::lean_dec(v_mctx_1651_);
                    v___x_1670_ = leanh::lean_box(0);
                    v_isShared_1671_ = v_isSharedCheck_1682_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1672_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_eAssignment_1667_, v_mvarId_1646_, v_val_1647_);
                if v_isShared_1671_ == 0 {
                    leanh::lean_ctor_set(v___x_1670_, 8, v___x_1672_);
                    v___x_1674_ = v___x_1670_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_depth_1659_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1681_,
                        1,
                        v_levelAssignDepth_1660_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 2, v_lmvarCounter_1661_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 3, v_mvarCounter_1662_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 4, v_lDecls_1663_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 5, v_decls_1664_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 6, v_userNames_1665_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 7, v_lAssignment_1666_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 8, v___x_1672_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 9, v_dAssignment_1668_);
                    v___x_1674_ = v_reuseFailAlloc_1681_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_1658_ == 0 {
                    leanh::lean_ctor_set(v___x_1657_, 0, v___x_1674_);
                    v___x_1676_ = v___x_1657_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1680_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 0, v___x_1674_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 1, v_cache_1652_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_1680_,
                        2,
                        v_zetaDeltaFVarIds_1653_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 3, v_postponed_1654_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1680_, 4, v_diag_1655_);
                    v___x_1676_ = v_reuseFailAlloc_1680_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1677_ = lean_st_ref_set(v___y_1648_, v___x_1676_);
                v___x_1678_ = leanh::lean_box(0);
                v___x_1679_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1679_, 0, v___x_1678_);
                return v___x_1679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg___boxed(
    mut v_mvarId_1684_: *mut leanh::LeanObject,
    mut v_val_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(
        v_mvarId_1684_,
        v_val_1685_,
        v___y_1686_,
    );
    leanh::lean_dec(v___y_1686_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply___lam__0(
    mut v_mvarId_1689_: *mut leanh::LeanObject,
    mut v_rule_1690_: *mut leanh::LeanObject,
    mut v___y_1691_: *mut leanh::LeanObject,
    mut v___y_1692_: *mut leanh::LeanObject,
    mut v___y_1693_: *mut leanh::LeanObject,
    mut v___y_1694_: *mut leanh::LeanObject,
    mut v___y_1695_: *mut leanh::LeanObject,
    mut v___y_1696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pattern_1701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultPos_1702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1704_: u8 = 0;
    let mut v___x_1705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1709_: u8 = 0;
    let mut v_val_1710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1713_: u8 = 0;
    let mut v___x_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1718_: u8 = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1727_: u8 = 0;
    let mut v_unused_1728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1729_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1734_: u8 = 0;
    let mut v_a_1735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1738_: u8 = 0;
    let mut v___x_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1742_: u8 = 0;
    let mut v_a_1743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1746_: u8 = 0;
    let mut v___x_1748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_mvarId_1689_);
                v___x_1698_ = l_Lean_MVarId_getDecl(
                    v_mvarId_1689_,
                    v___y_1693_,
                    v___y_1694_,
                    v___y_1695_,
                    v___y_1696_,
                );
                if leanh::lean_obj_tag(v___x_1698_) == 0 {
                    v_a_1699_ = leanh::lean_ctor_get(v___x_1698_, 0);
                    leanh::lean_inc(v_a_1699_);
                    leanh::lean_dec_ref_known(v___x_1698_, 1);
                    v_expr_1700_ = leanh::lean_ctor_get(v_rule_1690_, 0);
                    leanh::lean_inc_ref(v_expr_1700_);
                    v_pattern_1701_ = leanh::lean_ctor_get(v_rule_1690_, 1);
                    leanh::lean_inc_ref_n(v_pattern_1701_, 2);
                    v_resultPos_1702_ = leanh::lean_ctor_get(v_rule_1690_, 2);
                    leanh::lean_inc(v_resultPos_1702_);
                    leanh::lean_dec_ref(v_rule_1690_);
                    v_type_1703_ = leanh::lean_ctor_get(v_a_1699_, 2);
                    leanh::lean_inc_ref(v_type_1703_);
                    leanh::lean_dec(v_a_1699_);
                    v___x_1704_ = 1;
                    v___x_1705_ = l_Lean_Meta_Sym_Pattern_unify_x3f(
                        v_pattern_1701_,
                        v_type_1703_,
                        v___x_1704_,
                        v___y_1691_,
                        v___y_1692_,
                        v___y_1693_,
                        v___y_1694_,
                        v___y_1695_,
                        v___y_1696_,
                    );
                    if leanh::lean_obj_tag(v___x_1705_) == 0 {
                        v_a_1706_ = leanh::lean_ctor_get(v___x_1705_, 0);
                        v_isSharedCheck_1734_ =
                            (!leanh::lean_is_exclusive(v___x_1705_)) as u8;
                        if v_isSharedCheck_1734_ == 0 {
                            v___x_1708_ = v___x_1705_;
                            v_isShared_1709_ = v_isSharedCheck_1734_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1706_);
                            leanh::lean_dec(v___x_1705_);
                            v___x_1708_ = leanh::lean_box(0);
                            v_isShared_1709_ = v_isSharedCheck_1734_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_resultPos_1702_);
                        leanh::lean_dec_ref(v_pattern_1701_);
                        leanh::lean_dec_ref(v_expr_1700_);
                        leanh::lean_dec(v_mvarId_1689_);
                        v_a_1735_ = leanh::lean_ctor_get(v___x_1705_, 0);
                        v_isSharedCheck_1742_ =
                            (!leanh::lean_is_exclusive(v___x_1705_)) as u8;
                        if v_isSharedCheck_1742_ == 0 {
                            v___x_1737_ = v___x_1705_;
                            v_isShared_1738_ = v_isSharedCheck_1742_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1735_);
                            leanh::lean_dec(v___x_1705_);
                            v___x_1737_ = leanh::lean_box(0);
                            v_isShared_1738_ = v_isSharedCheck_1742_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_rule_1690_);
                    leanh::lean_dec(v_mvarId_1689_);
                    v_a_1743_ = leanh::lean_ctor_get(v___x_1698_, 0);
                    v_isSharedCheck_1750_ = (!leanh::lean_is_exclusive(v___x_1698_)) as u8;
                    if v_isSharedCheck_1750_ == 0 {
                        v___x_1745_ = v___x_1698_;
                        v_isShared_1746_ = v_isSharedCheck_1750_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1743_);
                        leanh::lean_dec(v___x_1698_);
                        v___x_1745_ = leanh::lean_box(0);
                        v_isShared_1746_ = v_isSharedCheck_1750_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1706_) == 1 {
                    leanh::lean_del_object(v___x_1708_);
                    v_val_1710_ = leanh::lean_ctor_get(v_a_1706_, 0);
                    v_isSharedCheck_1729_ = (!leanh::lean_is_exclusive(v_a_1706_)) as u8;
                    if v_isSharedCheck_1729_ == 0 {
                        v___x_1712_ = v_a_1706_;
                        v_isShared_1713_ = v_isSharedCheck_1729_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_1710_);
                        leanh::lean_dec(v_a_1706_);
                        v___x_1712_ = leanh::lean_box(0);
                        v_isShared_1713_ = v_isSharedCheck_1729_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_1706_);
                    leanh::lean_dec(v_resultPos_1702_);
                    leanh::lean_dec_ref(v_pattern_1701_);
                    leanh::lean_dec_ref(v_expr_1700_);
                    leanh::lean_dec(v_mvarId_1689_);
                    v___x_1730_ = leanh::lean_box(0);
                    if v_isShared_1709_ == 0 {
                        leanh::lean_ctor_set(v___x_1708_, 0, v___x_1730_);
                        v___x_1732_ = v___x_1708_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1733_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1733_, 0, v___x_1730_);
                        v___x_1732_ = v_reuseFailAlloc_1733_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                leanh::lean_inc(v_val_1710_);
                v___x_1714_ = l___private_Lean_Meta_Sym_Apply_0__Lean_Meta_Sym_mkValue(
                    v_expr_1700_,
                    v_pattern_1701_,
                    v_val_1710_,
                );
                v___x_1715_ =
                    l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(
                        v_mvarId_1689_,
                        v___x_1714_,
                        v___y_1694_,
                    );
                v_isSharedCheck_1727_ = (!leanh::lean_is_exclusive(v___x_1715_)) as u8;
                if v_isSharedCheck_1727_ == 0 {
                    v_unused_1728_ = leanh::lean_ctor_get(v___x_1715_, 0);
                    leanh::lean_dec(v_unused_1728_);
                    v___x_1717_ = v___x_1715_;
                    v_isShared_1718_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v___x_1715_);
                    v___x_1717_ = leanh::lean_box(0);
                    v_isShared_1718_ = v_isSharedCheck_1727_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1719_ = leanh::lean_box(0);
                v___x_1720_ = l_List_mapTR_loop___at___00Lean_Meta_Sym_BackwardRule_apply_spec__1(
                    v_val_1710_,
                    v_resultPos_1702_,
                    v___x_1719_,
                );
                leanh::lean_dec(v_val_1710_);
                if v_isShared_1713_ == 0 {
                    leanh::lean_ctor_set(v___x_1712_, 0, v___x_1720_);
                    v___x_1722_ = v___x_1712_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1726_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1726_, 0, v___x_1720_);
                    v___x_1722_ = v_reuseFailAlloc_1726_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_1718_ == 0 {
                    leanh::lean_ctor_set(v___x_1717_, 0, v___x_1722_);
                    v___x_1724_ = v___x_1717_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1725_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1725_, 0, v___x_1722_);
                    v___x_1724_ = v_reuseFailAlloc_1725_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1724_;
            }
            6 => {
                return v___x_1732_;
            }
            7 => {
                if v_isShared_1738_ == 0 {
                    v___x_1740_ = v___x_1737_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1741_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_a_1735_);
                    v___x_1740_ = v_reuseFailAlloc_1741_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1740_;
            }
            9 => {
                if v_isShared_1746_ == 0 {
                    v___x_1748_ = v___x_1745_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1749_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1749_, 0, v_a_1743_);
                    v___x_1748_ = v_reuseFailAlloc_1749_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed(
    mut v_mvarId_1751_: *mut leanh::LeanObject,
    mut v_rule_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
    mut v___y_1756_: *mut leanh::LeanObject,
    mut v___y_1757_: *mut leanh::LeanObject,
    mut v___y_1758_: *mut leanh::LeanObject,
    mut v___y_1759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1760_ = l_Lean_Meta_Sym_BackwardRule_apply___lam__0(
        v_mvarId_1751_,
        v_rule_1752_,
        v___y_1753_,
        v___y_1754_,
        v___y_1755_,
        v___y_1756_,
        v___y_1757_,
        v___y_1758_,
    );
    leanh::lean_dec(v___y_1758_);
    leanh::lean_dec_ref(v___y_1757_);
    leanh::lean_dec(v___y_1756_);
    leanh::lean_dec_ref(v___y_1755_);
    leanh::lean_dec(v___y_1754_);
    leanh::lean_dec_ref(v___y_1753_);
    return v_res_1760_;
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply(
    mut v_mvarId_1761_: *mut leanh::LeanObject,
    mut v_rule_1762_: *mut leanh::LeanObject,
    mut v_a_1763_: *mut leanh::LeanObject,
    mut v_a_1764_: *mut leanh::LeanObject,
    mut v_a_1765_: *mut leanh::LeanObject,
    mut v_a_1766_: *mut leanh::LeanObject,
    mut v_a_1767_: *mut leanh::LeanObject,
    mut v_a_1768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v_mvarId_1761_);
    v___f_1770_ = leanh::lean_alloc_closure(
        l_Lean_Meta_Sym_BackwardRule_apply___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_1770_, 0, v_mvarId_1761_);
    leanh::lean_closure_set(v___f_1770_, 1, v_rule_1762_);
    v___x_1771_ =
        l_Lean_MVarId_withContext___at___00Lean_Meta_Sym_BackwardRule_apply_spec__2___redArg(
            v_mvarId_1761_,
            v___f_1770_,
            v_a_1763_,
            v_a_1764_,
            v_a_1765_,
            v_a_1766_,
            v_a_1767_,
            v_a_1768_,
        );
    return v___x_1771_;
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply___boxed(
    mut v_mvarId_1772_: *mut leanh::LeanObject,
    mut v_rule_1773_: *mut leanh::LeanObject,
    mut v_a_1774_: *mut leanh::LeanObject,
    mut v_a_1775_: *mut leanh::LeanObject,
    mut v_a_1776_: *mut leanh::LeanObject,
    mut v_a_1777_: *mut leanh::LeanObject,
    mut v_a_1778_: *mut leanh::LeanObject,
    mut v_a_1779_: *mut leanh::LeanObject,
    mut v_a_1780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1781_ = l_Lean_Meta_Sym_BackwardRule_apply(
        v_mvarId_1772_,
        v_rule_1773_,
        v_a_1774_,
        v_a_1775_,
        v_a_1776_,
        v_a_1777_,
        v_a_1778_,
        v_a_1779_,
    );
    leanh::lean_dec(v_a_1779_);
    leanh::lean_dec_ref(v_a_1778_);
    leanh::lean_dec(v_a_1777_);
    leanh::lean_dec_ref(v_a_1776_);
    leanh::lean_dec(v_a_1775_);
    leanh::lean_dec_ref(v_a_1774_);
    return v_res_1781_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(
    mut v_mvarId_1782_: *mut leanh::LeanObject,
    mut v_val_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
    mut v___y_1785_: *mut leanh::LeanObject,
    mut v___y_1786_: *mut leanh::LeanObject,
    mut v___y_1787_: *mut leanh::LeanObject,
    mut v___y_1788_: *mut leanh::LeanObject,
    mut v___y_1789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1791_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___redArg(
        v_mvarId_1782_,
        v_val_1783_,
        v___y_1787_,
    );
    return v___x_1791_;
}
pub unsafe fn l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0___boxed(
    mut v_mvarId_1792_: *mut leanh::LeanObject,
    mut v_val_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
    mut v___y_1795_: *mut leanh::LeanObject,
    mut v___y_1796_: *mut leanh::LeanObject,
    mut v___y_1797_: *mut leanh::LeanObject,
    mut v___y_1798_: *mut leanh::LeanObject,
    mut v___y_1799_: *mut leanh::LeanObject,
    mut v___y_1800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1801_ = l_Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0(
        v_mvarId_1792_,
        v_val_1793_,
        v___y_1794_,
        v___y_1795_,
        v___y_1796_,
        v___y_1797_,
        v___y_1798_,
        v___y_1799_,
    );
    leanh::lean_dec(v___y_1799_);
    leanh::lean_dec_ref(v___y_1798_);
    leanh::lean_dec(v___y_1797_);
    leanh::lean_dec_ref(v___y_1796_);
    leanh::lean_dec(v___y_1795_);
    leanh::lean_dec_ref(v___y_1794_);
    return v_res_1801_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0(
    mut v_00_u03b2_1802_: *mut leanh::LeanObject,
    mut v_x_1803_: *mut leanh::LeanObject,
    mut v_x_1804_: *mut leanh::LeanObject,
    mut v_x_1805_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1806_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0___redArg(v_x_1803_, v_x_1804_, v_x_1805_);
    return v___x_1806_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1807_: *mut leanh::LeanObject,
    mut v_x_1808_: *mut leanh::LeanObject,
    mut v_x_1809_: usize,
    mut v_x_1810_: usize,
    mut v_x_1811_: *mut leanh::LeanObject,
    mut v_x_1812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1813_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___redArg(v_x_1808_, v_x_1809_, v_x_1810_, v_x_1811_, v_x_1812_);
    return v___x_1813_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1814_: *mut leanh::LeanObject,
    mut v_x_1815_: *mut leanh::LeanObject,
    mut v_x_1816_: *mut leanh::LeanObject,
    mut v_x_1817_: *mut leanh::LeanObject,
    mut v_x_1818_: *mut leanh::LeanObject,
    mut v_x_1819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3204__boxed_1820_: usize = 0;
    let mut v_x_3205__boxed_1821_: usize = 0;
    let mut v_res_1822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3204__boxed_1820_ = leanh::lean_unbox_usize(v_x_1816_);
    leanh::lean_dec(v_x_1816_);
    v_x_3205__boxed_1821_ = leanh::lean_unbox_usize(v_x_1817_);
    leanh::lean_dec(v_x_1817_);
    v_res_1822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2(v_00_u03b2_1814_, v_x_1815_, v_x_3204__boxed_1820_, v_x_3205__boxed_1821_, v_x_1818_, v_x_1819_);
    return v_res_1822_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4(
    mut v_00_u03b2_1823_: *mut leanh::LeanObject,
    mut v_n_1824_: *mut leanh::LeanObject,
    mut v_k_1825_: *mut leanh::LeanObject,
    mut v_v_1826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1827_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4___redArg(v_n_1824_, v_k_1825_, v_v_1826_);
    return v___x_1827_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(
    mut v_00_u03b2_1828_: *mut leanh::LeanObject,
    mut v_depth_1829_: usize,
    mut v_keys_1830_: *mut leanh::LeanObject,
    mut v_vals_1831_: *mut leanh::LeanObject,
    mut v_heq_1832_: *mut leanh::LeanObject,
    mut v_i_1833_: *mut leanh::LeanObject,
    mut v_entries_1834_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1835_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1835_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___redArg(v_depth_1829_, v_keys_1830_, v_vals_1831_, v_i_1833_, v_entries_1834_);
    return v___x_1835_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5___boxed(
    mut v_00_u03b2_1836_: *mut leanh::LeanObject,
    mut v_depth_1837_: *mut leanh::LeanObject,
    mut v_keys_1838_: *mut leanh::LeanObject,
    mut v_vals_1839_: *mut leanh::LeanObject,
    mut v_heq_1840_: *mut leanh::LeanObject,
    mut v_i_1841_: *mut leanh::LeanObject,
    mut v_entries_1842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1843_: usize = 0;
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1843_ = leanh::lean_unbox_usize(v_depth_1837_);
    leanh::lean_dec(v_depth_1837_);
    v_res_1844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__5(v_00_u03b2_1836_, v_depth_boxed_1843_, v_keys_1838_, v_vals_1839_, v_heq_1840_, v_i_1841_, v_entries_1842_);
    leanh::lean_dec_ref(v_vals_1839_);
    leanh::lean_dec_ref(v_keys_1838_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5(
    mut v_00_u03b2_1845_: *mut leanh::LeanObject,
    mut v_x_1846_: *mut leanh::LeanObject,
    mut v_x_1847_: *mut leanh::LeanObject,
    mut v_x_1848_: *mut leanh::LeanObject,
    mut v_x_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1850_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00Lean_Meta_Sym_BackwardRule_apply_spec__0_spec__0_spec__2_spec__4_spec__5___redArg(v_x_1846_, v_x_1847_, v_x_1848_, v_x_1849_);
    return v___x_1850_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(
    mut v_msgData_1851_: *mut leanh::LeanObject,
    mut v___y_1852_: *mut leanh::LeanObject,
    mut v___y_1853_: *mut leanh::LeanObject,
    mut v___y_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_1862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1865_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1857_ = lean_st_ref_get(v___y_1855_);
    v_env_1858_ = leanh::lean_ctor_get(v___x_1857_, 0);
    leanh::lean_inc_ref(v_env_1858_);
    leanh::lean_dec(v___x_1857_);
    v___x_1859_ = lean_st_ref_get(v___y_1853_);
    v_mctx_1860_ = leanh::lean_ctor_get(v___x_1859_, 0);
    leanh::lean_inc_ref(v_mctx_1860_);
    leanh::lean_dec(v___x_1859_);
    v_lctx_1861_ = leanh::lean_ctor_get(v___y_1852_, 2);
    v_options_1862_ = leanh::lean_ctor_get(v___y_1854_, 2);
    leanh::lean_inc_ref(v_options_1862_);
    leanh::lean_inc_ref(v_lctx_1861_);
    v___x_1863_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_1863_, 0, v_env_1858_);
    leanh::lean_ctor_set(v___x_1863_, 1, v_mctx_1860_);
    leanh::lean_ctor_set(v___x_1863_, 2, v_lctx_1861_);
    leanh::lean_ctor_set(v___x_1863_, 3, v_options_1862_);
    v___x_1864_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1864_, 0, v___x_1863_);
    leanh::lean_ctor_set(v___x_1864_, 1, v_msgData_1851_);
    v___x_1865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1865_, 0, v___x_1864_);
    return v___x_1865_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0___boxed(
    mut v_msgData_1866_: *mut leanh::LeanObject,
    mut v___y_1867_: *mut leanh::LeanObject,
    mut v___y_1868_: *mut leanh::LeanObject,
    mut v___y_1869_: *mut leanh::LeanObject,
    mut v___y_1870_: *mut leanh::LeanObject,
    mut v___y_1871_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1872_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1872_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msgData_1866_, v___y_1867_, v___y_1868_, v___y_1869_, v___y_1870_);
    leanh::lean_dec(v___y_1870_);
    leanh::lean_dec_ref(v___y_1869_);
    leanh::lean_dec(v___y_1868_);
    leanh::lean_dec_ref(v___y_1867_);
    return v_res_1872_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(
    mut v_msg_1873_: *mut leanh::LeanObject,
    mut v___y_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_1879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1884_: u8 = 0;
    let mut v___x_1885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1889_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_1879_ = leanh::lean_ctor_get(v___y_1876_, 5);
                v___x_1880_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0_spec__0(v_msg_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_);
                v_a_1881_ = leanh::lean_ctor_get(v___x_1880_, 0);
                v_isSharedCheck_1889_ = (!leanh::lean_is_exclusive(v___x_1880_)) as u8;
                if v_isSharedCheck_1889_ == 0 {
                    v___x_1883_ = v___x_1880_;
                    v_isShared_1884_ = v_isSharedCheck_1889_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_1881_);
                    leanh::lean_dec(v___x_1880_);
                    v___x_1883_ = leanh::lean_box(0);
                    v_isShared_1884_ = v_isSharedCheck_1889_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_1879_);
                v___x_1885_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1885_, 0, v_ref_1879_);
                leanh::lean_ctor_set(v___x_1885_, 1, v_a_1881_);
                if v_isShared_1884_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1883_, 1);
                    leanh::lean_ctor_set(v___x_1883_, 0, v___x_1885_);
                    v___x_1887_ = v___x_1883_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1888_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1888_, 0, v___x_1885_);
                    v___x_1887_ = v_reuseFailAlloc_1888_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1887_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg___boxed(
    mut v_msg_1890_: *mut leanh::LeanObject,
    mut v___y_1891_: *mut leanh::LeanObject,
    mut v___y_1892_: *mut leanh::LeanObject,
    mut v___y_1893_: *mut leanh::LeanObject,
    mut v___y_1894_: *mut leanh::LeanObject,
    mut v___y_1895_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1896_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(
        v_msg_1890_,
        v___y_1891_,
        v___y_1892_,
        v___y_1893_,
        v___y_1894_,
    );
    leanh::lean_dec(v___y_1894_);
    leanh::lean_dec_ref(v___y_1893_);
    leanh::lean_dec(v___y_1892_);
    leanh::lean_dec_ref(v___y_1891_);
    return v_res_1896_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1899_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1898_ = l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__0;
    v___x_1899_ = l_Lean_stringToMessageData(v___x_1898_);
    return v___x_1899_;
}
pub unsafe fn _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_1901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1901_ = l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__2;
    v___x_1902_ = l_Lean_stringToMessageData(v___x_1901_);
    return v___x_1902_;
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply_x27(
    mut v_mvarId_1903_: *mut leanh::LeanObject,
    mut v_rule_1904_: *mut leanh::LeanObject,
    mut v_a_1905_: *mut leanh::LeanObject,
    mut v_a_1906_: *mut leanh::LeanObject,
    mut v_a_1907_: *mut leanh::LeanObject,
    mut v_a_1908_: *mut leanh::LeanObject,
    mut v_a_1909_: *mut leanh::LeanObject,
    mut v_a_1910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1916_: u8 = 0;
    let mut v_mvarIds_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1930_: u8 = 0;
    let mut v_a_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1934_: u8 = 0;
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_rule_1904_);
                leanh::lean_inc(v_mvarId_1903_);
                v___x_1912_ = l_Lean_Meta_Sym_BackwardRule_apply(
                    v_mvarId_1903_,
                    v_rule_1904_,
                    v_a_1905_,
                    v_a_1906_,
                    v_a_1907_,
                    v_a_1908_,
                    v_a_1909_,
                    v_a_1910_,
                );
                if leanh::lean_obj_tag(v___x_1912_) == 0 {
                    v_a_1913_ = leanh::lean_ctor_get(v___x_1912_, 0);
                    v_isSharedCheck_1930_ = (!leanh::lean_is_exclusive(v___x_1912_)) as u8;
                    if v_isSharedCheck_1930_ == 0 {
                        v___x_1915_ = v___x_1912_;
                        v_isShared_1916_ = v_isSharedCheck_1930_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1913_);
                        leanh::lean_dec(v___x_1912_);
                        v___x_1915_ = leanh::lean_box(0);
                        v_isShared_1916_ = v_isSharedCheck_1930_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_rule_1904_);
                    leanh::lean_dec(v_mvarId_1903_);
                    v_a_1931_ = leanh::lean_ctor_get(v___x_1912_, 0);
                    v_isSharedCheck_1938_ = (!leanh::lean_is_exclusive(v___x_1912_)) as u8;
                    if v_isSharedCheck_1938_ == 0 {
                        v___x_1933_ = v___x_1912_;
                        v_isShared_1934_ = v_isSharedCheck_1938_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1931_);
                        leanh::lean_dec(v___x_1912_);
                        v___x_1933_ = leanh::lean_box(0);
                        v_isShared_1934_ = v_isSharedCheck_1938_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_1913_) == 1 {
                    leanh::lean_dec_ref(v_rule_1904_);
                    leanh::lean_dec(v_mvarId_1903_);
                    v_mvarIds_1917_ = leanh::lean_ctor_get(v_a_1913_, 0);
                    leanh::lean_inc(v_mvarIds_1917_);
                    leanh::lean_dec_ref_known(v_a_1913_, 1);
                    if v_isShared_1916_ == 0 {
                        leanh::lean_ctor_set(v___x_1915_, 0, v_mvarIds_1917_);
                        v___x_1919_ = v___x_1915_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1920_, 0, v_mvarIds_1917_);
                        v___x_1919_ = v_reuseFailAlloc_1920_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1915_);
                    leanh::lean_dec(v_a_1913_);
                    v_expr_1921_ = leanh::lean_ctor_get(v_rule_1904_, 0);
                    leanh::lean_inc_ref(v_expr_1921_);
                    leanh::lean_dec_ref(v_rule_1904_);
                    v___x_1922_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1_once
                        ),
                        _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__1,
                    );
                    v___x_1923_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1923_, 0, v_mvarId_1903_);
                    v___x_1924_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1924_, 0, v___x_1922_);
                    leanh::lean_ctor_set(v___x_1924_, 1, v___x_1923_);
                    v___x_1925_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3_once
                        ),
                        _init_l_Lean_Meta_Sym_BackwardRule_apply_x27___closed__3,
                    );
                    v___x_1926_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1926_, 0, v___x_1924_);
                    leanh::lean_ctor_set(v___x_1926_, 1, v___x_1925_);
                    v___x_1927_ = l_Lean_indentExpr(v_expr_1921_);
                    v___x_1928_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1928_, 0, v___x_1926_);
                    leanh::lean_ctor_set(v___x_1928_, 1, v___x_1927_);
                    v___x_1929_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(v___x_1928_, v_a_1907_, v_a_1908_, v_a_1909_, v_a_1910_);
                    return v___x_1929_;
                }
            }
            2 => {
                return v___x_1919_;
            }
            3 => {
                if v_isShared_1934_ == 0 {
                    v___x_1936_ = v___x_1933_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_a_1931_);
                    v___x_1936_ = v_reuseFailAlloc_1937_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1936_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Sym_BackwardRule_apply_x27___boxed(
    mut v_mvarId_1939_: *mut leanh::LeanObject,
    mut v_rule_1940_: *mut leanh::LeanObject,
    mut v_a_1941_: *mut leanh::LeanObject,
    mut v_a_1942_: *mut leanh::LeanObject,
    mut v_a_1943_: *mut leanh::LeanObject,
    mut v_a_1944_: *mut leanh::LeanObject,
    mut v_a_1945_: *mut leanh::LeanObject,
    mut v_a_1946_: *mut leanh::LeanObject,
    mut v_a_1947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1948_ = l_Lean_Meta_Sym_BackwardRule_apply_x27(
        v_mvarId_1939_,
        v_rule_1940_,
        v_a_1941_,
        v_a_1942_,
        v_a_1943_,
        v_a_1944_,
        v_a_1945_,
        v_a_1946_,
    );
    leanh::lean_dec(v_a_1946_);
    leanh::lean_dec_ref(v_a_1945_);
    leanh::lean_dec(v_a_1944_);
    leanh::lean_dec_ref(v_a_1943_);
    leanh::lean_dec(v_a_1942_);
    leanh::lean_dec_ref(v_a_1941_);
    return v_res_1948_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(
    mut v_00_u03b1_1949_: *mut leanh::LeanObject,
    mut v_msg_1950_: *mut leanh::LeanObject,
    mut v___y_1951_: *mut leanh::LeanObject,
    mut v___y_1952_: *mut leanh::LeanObject,
    mut v___y_1953_: *mut leanh::LeanObject,
    mut v___y_1954_: *mut leanh::LeanObject,
    mut v___y_1955_: *mut leanh::LeanObject,
    mut v___y_1956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1958_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___redArg(
        v_msg_1950_,
        v___y_1953_,
        v___y_1954_,
        v___y_1955_,
        v___y_1956_,
    );
    return v___x_1958_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0___boxed(
    mut v_00_u03b1_1959_: *mut leanh::LeanObject,
    mut v_msg_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
    mut v___y_1963_: *mut leanh::LeanObject,
    mut v___y_1964_: *mut leanh::LeanObject,
    mut v___y_1965_: *mut leanh::LeanObject,
    mut v___y_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1968_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1968_ = l_Lean_throwError___at___00Lean_Meta_Sym_BackwardRule_apply_x27_spec__0(
        v_00_u03b1_1959_,
        v_msg_1960_,
        v___y_1961_,
        v___y_1962_,
        v___y_1963_,
        v___y_1964_,
        v___y_1965_,
        v___y_1966_,
    );
    leanh::lean_dec(v___y_1966_);
    leanh::lean_dec_ref(v___y_1965_);
    leanh::lean_dec(v___y_1964_);
    leanh::lean_dec_ref(v___y_1963_);
    leanh::lean_dec(v___y_1962_);
    leanh::lean_dec_ref(v___y_1961_);
    return v_res_1968_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Sym_Apply(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Sym_Apply(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Sym_Apply(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Util_CollectFVars(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Sym_Apply(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Sym_Apply(builtin);
}
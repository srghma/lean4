// Lean compiler output
// Module: Lean.Util.SortExprs
// Imports: Lean.Expr
use crate::r#gen::Lean::Expr::{initialize_Lean_Expr, runtime_initialize_Lean_Expr};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_fswap, lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_array_uset,
    lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::Nat::Bitwise::Basic::lean_nat_shiftr;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_uint64_of_nat, lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Lean::Expr::lean_expr_lt;
static mut l_Lean_sortExprs___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_sortExprs___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_sortExprs___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_sortExprs___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_sortExprs___closed__2_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_sortExprs___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(
    mut v_sz_533_: usize,
    mut v_i_534_: usize,
    mut v_bs_535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_536_: u8 = 0;
    let mut v_v_537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_541_: usize = 0;
    let mut v___x_542_: usize = 0;
    let mut v___x_543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_536_ = lean_usize_dec_lt(v_i_534_, v_sz_533_);
                if v___x_536_ == 0 {
                    return v_bs_535_;
                } else {
                    v_v_537_ = lean_array_uget_borrowed(v_bs_535_, v_i_534_);
                    v_fst_538_ = crate::leanh::lean_ctor_get(v_v_537_, 0);
                    crate::leanh::lean_inc(v_fst_538_);
                    v___x_539_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_540_ = lean_array_uset(v_bs_535_, v_i_534_, v___x_539_);
                    v___x_541_ = 1usize;
                    v___x_542_ = lean_usize_add(v_i_534_, v___x_541_);
                    v___x_543_ = lean_array_uset(v_bs_x27_540_, v_i_534_, v_fst_538_);
                    v_i_534_ = v___x_542_;
                    v_bs_535_ = v___x_543_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1___boxed(
    mut v_sz_545_: *mut crate::leanh::LeanObject,
    mut v_i_546_: *mut crate::leanh::LeanObject,
    mut v_bs_547_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_548_: usize = 0;
    let mut v_i_boxed_549_: usize = 0;
    let mut v_res_550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_548_ = crate::leanh::lean_unbox_usize(v_sz_545_);
    crate::leanh::lean_dec(v_sz_545_);
    v_i_boxed_549_ = crate::leanh::lean_unbox_usize(v_i_546_);
    crate::leanh::lean_dec(v_i_546_);
    v_res_550_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(
            v_sz_boxed_548_,
            v_i_boxed_549_,
            v_bs_547_,
        );
    return v_res_550_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(
    mut v_x_551_: *mut crate::leanh::LeanObject,
    mut v_x_552_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_555_: u8 = 0;
    v_fst_553_ = crate::leanh::lean_ctor_get(v_x_551_, 0);
    v_fst_554_ = crate::leanh::lean_ctor_get(v_x_552_, 0);
    v___x_555_ = lean_expr_lt(v_fst_554_, v_fst_553_);
    return v___x_555_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0___boxed(
    mut v_x_556_: *mut crate::leanh::LeanObject,
    mut v_x_557_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_558_: u8 = 0;
    let mut v_r_559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_558_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v_x_556_, v_x_557_);
    crate::leanh::lean_dec_ref(v_x_557_);
    crate::leanh::lean_dec_ref(v_x_556_);
    v_r_559_ = crate::leanh::lean_box((v_res_558_) as usize);
    return v_r_559_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(
    mut v_hi_560_: *mut crate::leanh::LeanObject,
    mut v_pivot_561_: *mut crate::leanh::LeanObject,
    mut v_as_562_: *mut crate::leanh::LeanObject,
    mut v_i_563_: *mut crate::leanh::LeanObject,
    mut v_k_564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_565_: u8 = 0;
    let mut v___x_566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_571_: u8 = 0;
    let mut v___x_572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_565_ = lean_nat_dec_lt(v_k_564_, v_hi_560_);
                if v___x_565_ == 0 {
                    crate::leanh::lean_dec(v_k_564_);
                    v___x_566_ = lean_array_fswap(v_as_562_, v_i_563_, v_hi_560_);
                    v___x_567_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_567_, 0, v_i_563_);
                    crate::leanh::lean_ctor_set(v___x_567_, 1, v___x_566_);
                    return v___x_567_;
                } else {
                    v___x_568_ = lean_array_fget_borrowed(v_as_562_, v_k_564_);
                    v_fst_569_ = crate::leanh::lean_ctor_get(v___x_568_, 0);
                    v_fst_570_ = crate::leanh::lean_ctor_get(v_pivot_561_, 0);
                    v___x_571_ = lean_expr_lt(v_fst_570_, v_fst_569_);
                    if v___x_571_ == 0 {
                        v___x_572_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_573_ = lean_nat_add(v_k_564_, v___x_572_);
                        crate::leanh::lean_dec(v_k_564_);
                        v_k_564_ = v___x_573_;
                        state = 0;
                        continue;
                    } else {
                        v___x_575_ = lean_array_fswap(v_as_562_, v_i_563_, v_k_564_);
                        v___x_576_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_577_ = lean_nat_add(v_i_563_, v___x_576_);
                        crate::leanh::lean_dec(v_i_563_);
                        v___x_578_ = lean_nat_add(v_k_564_, v___x_576_);
                        crate::leanh::lean_dec(v_k_564_);
                        v_as_562_ = v___x_575_;
                        v_i_563_ = v___x_577_;
                        v_k_564_ = v___x_578_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg___boxed(
    mut v_hi_580_: *mut crate::leanh::LeanObject,
    mut v_pivot_581_: *mut crate::leanh::LeanObject,
    mut v_as_582_: *mut crate::leanh::LeanObject,
    mut v_i_583_: *mut crate::leanh::LeanObject,
    mut v_k_584_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_585_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_580_, v_pivot_581_, v_as_582_, v_i_583_, v_k_584_);
    crate::leanh::lean_dec_ref(v_pivot_581_);
    crate::leanh::lean_dec(v_hi_580_);
    return v_res_585_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(
    mut v_n_586_: *mut crate::leanh::LeanObject,
    mut v_as_587_: *mut crate::leanh::LeanObject,
    mut v_lo_588_: *mut crate::leanh::LeanObject,
    mut v_hi_589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_596_: u8 = 0;
    let mut v___x_597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_601_: u8 = 0;
    let mut v___x_602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_609_: u8 = 0;
    let mut v___x_610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_615_: u8 = 0;
    let mut v___x_616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_601_ = lean_nat_dec_lt(v_lo_588_, v_hi_589_);
                if v___x_601_ == 0 {
                    crate::leanh::lean_dec(v_lo_588_);
                    return v_as_587_;
                } else {
                    v___x_602_ = lean_nat_add(v_lo_588_, v_hi_589_);
                    v___x_603_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_604_ = lean_nat_shiftr(v___x_602_, v___x_603_);
                    crate::leanh::lean_dec(v___x_602_);
                    v___x_617_ = lean_array_fget_borrowed(v_as_587_, v_mid_604_);
                    v___x_618_ = lean_array_fget_borrowed(v_as_587_, v_lo_588_);
                    v___x_619_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_617_, v___x_618_);
                    if v___x_619_ == 0 {
                        v___y_612_ = v_as_587_;
                        state = 3;
                        continue;
                    } else {
                        v___x_620_ = lean_array_fswap(v_as_587_, v_lo_588_, v_mid_604_);
                        v___y_612_ = v___x_620_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_592_ = lean_array_fget(v___y_591_, v_hi_589_);
                crate::leanh::lean_inc_n(v_lo_588_, 2);
                v___x_593_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_589_, v_pivot_592_, v___y_591_, v_lo_588_, v_lo_588_);
                crate::leanh::lean_dec(v_pivot_592_);
                v_fst_594_ = crate::leanh::lean_ctor_get(v___x_593_, 0);
                crate::leanh::lean_inc(v_fst_594_);
                v_snd_595_ = crate::leanh::lean_ctor_get(v___x_593_, 1);
                crate::leanh::lean_inc(v_snd_595_);
                crate::leanh::lean_dec_ref(v___x_593_);
                v___x_596_ = lean_nat_dec_le(v_hi_589_, v_fst_594_);
                if v___x_596_ == 0 {
                    v___x_597_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_586_, v_snd_595_, v_lo_588_, v_fst_594_);
                    v___x_598_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_599_ = lean_nat_add(v_fst_594_, v___x_598_);
                    crate::leanh::lean_dec(v_fst_594_);
                    v_as_587_ = v___x_597_;
                    v_lo_588_ = v___x_599_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_594_);
                    crate::leanh::lean_dec(v_lo_588_);
                    return v_snd_595_;
                }
            }
            2 => {
                v___x_607_ = lean_array_fget_borrowed(v___y_606_, v_mid_604_);
                v___x_608_ = lean_array_fget_borrowed(v___y_606_, v_hi_589_);
                v___x_609_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_607_, v___x_608_);
                if v___x_609_ == 0 {
                    crate::leanh::lean_dec(v_mid_604_);
                    v___y_591_ = v___y_606_;
                    state = 1;
                    continue;
                } else {
                    v___x_610_ = lean_array_fswap(v___y_606_, v_mid_604_, v_hi_589_);
                    crate::leanh::lean_dec(v_mid_604_);
                    v___y_591_ = v___x_610_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_613_ = lean_array_fget_borrowed(v___y_612_, v_hi_589_);
                v___x_614_ = lean_array_fget_borrowed(v___y_612_, v_lo_588_);
                v___x_615_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___lam__0(v___x_613_, v___x_614_);
                if v___x_615_ == 0 {
                    v___y_606_ = v___y_612_;
                    state = 2;
                    continue;
                } else {
                    v___x_616_ = lean_array_fswap(v___y_612_, v_lo_588_, v_hi_589_);
                    v___y_606_ = v___x_616_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg___boxed(
    mut v_n_621_: *mut crate::leanh::LeanObject,
    mut v_as_622_: *mut crate::leanh::LeanObject,
    mut v_lo_623_: *mut crate::leanh::LeanObject,
    mut v_hi_624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_625_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_621_, v_as_622_, v_lo_623_, v_hi_624_);
    crate::leanh::lean_dec(v_hi_624_);
    crate::leanh::lean_dec(v_n_621_);
    return v_res_625_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(
    mut v_a_626_: *mut crate::leanh::LeanObject,
    mut v_b_627_: *mut crate::leanh::LeanObject,
    mut v_x_628_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_634_: u8 = 0;
    let mut v___x_635_: u8 = 0;
    let mut v___x_636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_628_) == 0 {
                    crate::leanh::lean_dec(v_b_627_);
                    crate::leanh::lean_dec(v_a_626_);
                    return v_x_628_;
                } else {
                    v_key_629_ = crate::leanh::lean_ctor_get(v_x_628_, 0);
                    v_value_630_ = crate::leanh::lean_ctor_get(v_x_628_, 1);
                    v_tail_631_ = crate::leanh::lean_ctor_get(v_x_628_, 2);
                    v_isSharedCheck_643_ = (!crate::leanh::lean_is_exclusive(v_x_628_)) as u8;
                    if v_isSharedCheck_643_ == 0 {
                        v___x_633_ = v_x_628_;
                        v_isShared_634_ = v_isSharedCheck_643_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_631_);
                        crate::leanh::lean_inc(v_value_630_);
                        crate::leanh::lean_inc(v_key_629_);
                        crate::leanh::lean_dec(v_x_628_);
                        v___x_633_ = crate::leanh::lean_box(0);
                        v_isShared_634_ = v_isSharedCheck_643_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_635_ = lean_nat_dec_eq(v_key_629_, v_a_626_);
                if v___x_635_ == 0 {
                    v___x_636_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_626_, v_b_627_, v_tail_631_);
                    if v_isShared_634_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_633_, 2, v___x_636_);
                        v___x_638_ = v___x_633_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_639_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_639_, 0, v_key_629_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_639_, 1, v_value_630_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_639_, 2, v___x_636_);
                        v___x_638_ = v_reuseFailAlloc_639_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_630_);
                    crate::leanh::lean_dec(v_key_629_);
                    if v_isShared_634_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_633_, 1, v_b_627_);
                        crate::leanh::lean_ctor_set(v___x_633_, 0, v_a_626_);
                        v___x_641_ = v___x_633_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_642_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 0, v_a_626_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 1, v_b_627_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_642_, 2, v_tail_631_);
                        v___x_641_ = v_reuseFailAlloc_642_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_638_;
            }
            3 => {
                return v___x_641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(
    mut v_x_644_: *mut crate::leanh::LeanObject,
    mut v_x_645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_651_: u8 = 0;
    let mut v___x_652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_653_: u64 = 0;
    let mut v___x_654_: u64 = 0;
    let mut v___x_655_: u64 = 0;
    let mut v_fold_656_: u64 = 0;
    let mut v___x_657_: u64 = 0;
    let mut v___x_658_: u64 = 0;
    let mut v___x_659_: u64 = 0;
    let mut v___x_660_: usize = 0;
    let mut v___x_661_: usize = 0;
    let mut v___x_662_: usize = 0;
    let mut v___x_663_: usize = 0;
    let mut v___x_664_: usize = 0;
    let mut v___x_665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_671_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_645_) == 0 {
                    return v_x_644_;
                } else {
                    v_key_646_ = crate::leanh::lean_ctor_get(v_x_645_, 0);
                    v_value_647_ = crate::leanh::lean_ctor_get(v_x_645_, 1);
                    v_tail_648_ = crate::leanh::lean_ctor_get(v_x_645_, 2);
                    v_isSharedCheck_671_ = (!crate::leanh::lean_is_exclusive(v_x_645_)) as u8;
                    if v_isSharedCheck_671_ == 0 {
                        v___x_650_ = v_x_645_;
                        v_isShared_651_ = v_isSharedCheck_671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_648_);
                        crate::leanh::lean_inc(v_value_647_);
                        crate::leanh::lean_inc(v_key_646_);
                        crate::leanh::lean_dec(v_x_645_);
                        v___x_650_ = crate::leanh::lean_box(0);
                        v_isShared_651_ = v_isSharedCheck_671_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_652_ = lean_array_get_size(v_x_644_);
                v___x_653_ = lean_uint64_of_nat(v_key_646_);
                v___x_654_ = 32u64;
                v___x_655_ = lean_uint64_shift_right(v___x_653_, v___x_654_);
                v_fold_656_ = lean_uint64_xor(v___x_653_, v___x_655_);
                v___x_657_ = 16u64;
                v___x_658_ = lean_uint64_shift_right(v_fold_656_, v___x_657_);
                v___x_659_ = lean_uint64_xor(v_fold_656_, v___x_658_);
                v___x_660_ = lean_uint64_to_usize(v___x_659_);
                v___x_661_ = lean_usize_of_nat(v___x_652_);
                v___x_662_ = 1usize;
                v___x_663_ = lean_usize_sub(v___x_661_, v___x_662_);
                v___x_664_ = lean_usize_land(v___x_660_, v___x_663_);
                v___x_665_ = lean_array_uget_borrowed(v_x_644_, v___x_664_);
                crate::leanh::lean_inc(v___x_665_);
                if v_isShared_651_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_650_, 2, v___x_665_);
                    v___x_667_ = v___x_650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_670_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 0, v_key_646_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 1, v_value_647_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_670_, 2, v___x_665_);
                    v___x_667_ = v_reuseFailAlloc_670_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_668_ = lean_array_uset(v_x_644_, v___x_664_, v___x_667_);
                v_x_644_ = v___x_668_;
                v_x_645_ = v_tail_648_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(
    mut v_i_672_: *mut crate::leanh::LeanObject,
    mut v_source_673_: *mut crate::leanh::LeanObject,
    mut v_target_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: u8 = 0;
    let mut v_es_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_675_ = lean_array_get_size(v_source_673_);
                v___x_676_ = lean_nat_dec_lt(v_i_672_, v___x_675_);
                if v___x_676_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_673_);
                    crate::leanh::lean_dec(v_i_672_);
                    return v_target_674_;
                } else {
                    v_es_677_ = lean_array_fget(v_source_673_, v_i_672_);
                    v___x_678_ = crate::leanh::lean_box(0);
                    v_source_679_ = lean_array_fset(v_source_673_, v_i_672_, v___x_678_);
                    v_target_680_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_target_674_, v_es_677_);
                    v___x_681_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_682_ = lean_nat_add(v_i_672_, v___x_681_);
                    crate::leanh::lean_dec(v_i_672_);
                    v_i_672_ = v___x_682_;
                    v_source_673_ = v_source_679_;
                    v_target_674_ = v_target_680_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(
    mut v_data_684_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_685_ = lean_array_get_size(v_data_684_);
    v___x_686_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_687_ = lean_nat_mul(v___x_685_, v___x_686_);
    v___x_688_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_689_ = crate::leanh::lean_box(0);
    v___x_690_ = lean_mk_array(v_nbuckets_687_, v___x_689_);
    v___x_691_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v___x_688_, v_data_684_, v___x_690_);
    return v___x_691_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(
    mut v_a_692_: *mut crate::leanh::LeanObject,
    mut v_x_693_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_694_: u8 = 0;
    let mut v_key_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_693_) == 0 {
                    v___x_694_ = 0;
                    return v___x_694_;
                } else {
                    v_key_695_ = crate::leanh::lean_ctor_get(v_x_693_, 0);
                    v_tail_696_ = crate::leanh::lean_ctor_get(v_x_693_, 2);
                    v___x_697_ = lean_nat_dec_eq(v_key_695_, v_a_692_);
                    if v___x_697_ == 0 {
                        v_x_693_ = v_tail_696_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_697_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg___boxed(
    mut v_a_699_: *mut crate::leanh::LeanObject,
    mut v_x_700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_701_: u8 = 0;
    let mut v_r_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_701_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_699_, v_x_700_);
    crate::leanh::lean_dec(v_x_700_);
    crate::leanh::lean_dec(v_a_699_);
    v_r_702_ = crate::leanh::lean_box((v_res_701_) as usize);
    return v_r_702_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(
    mut v_m_703_: *mut crate::leanh::LeanObject,
    mut v_a_704_: *mut crate::leanh::LeanObject,
    mut v_b_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_710_: u8 = 0;
    let mut v___x_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: u64 = 0;
    let mut v___x_713_: u64 = 0;
    let mut v___x_714_: u64 = 0;
    let mut v_fold_715_: u64 = 0;
    let mut v___x_716_: u64 = 0;
    let mut v___x_717_: u64 = 0;
    let mut v___x_718_: u64 = 0;
    let mut v___x_719_: usize = 0;
    let mut v___x_720_: usize = 0;
    let mut v___x_721_: usize = 0;
    let mut v___x_722_: usize = 0;
    let mut v___x_723_: usize = 0;
    let mut v_bkt_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: u8 = 0;
    let mut v___x_726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: u8 = 0;
    let mut v_val_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_706_ = crate::leanh::lean_ctor_get(v_m_703_, 0);
                v_buckets_707_ = crate::leanh::lean_ctor_get(v_m_703_, 1);
                v_isSharedCheck_750_ = (!crate::leanh::lean_is_exclusive(v_m_703_)) as u8;
                if v_isSharedCheck_750_ == 0 {
                    v___x_709_ = v_m_703_;
                    v_isShared_710_ = v_isSharedCheck_750_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_707_);
                    crate::leanh::lean_inc(v_size_706_);
                    crate::leanh::lean_dec(v_m_703_);
                    v___x_709_ = crate::leanh::lean_box(0);
                    v_isShared_710_ = v_isSharedCheck_750_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_711_ = lean_array_get_size(v_buckets_707_);
                v___x_712_ = lean_uint64_of_nat(v_a_704_);
                v___x_713_ = 32u64;
                v___x_714_ = lean_uint64_shift_right(v___x_712_, v___x_713_);
                v_fold_715_ = lean_uint64_xor(v___x_712_, v___x_714_);
                v___x_716_ = 16u64;
                v___x_717_ = lean_uint64_shift_right(v_fold_715_, v___x_716_);
                v___x_718_ = lean_uint64_xor(v_fold_715_, v___x_717_);
                v___x_719_ = lean_uint64_to_usize(v___x_718_);
                v___x_720_ = lean_usize_of_nat(v___x_711_);
                v___x_721_ = 1usize;
                v___x_722_ = lean_usize_sub(v___x_720_, v___x_721_);
                v___x_723_ = lean_usize_land(v___x_719_, v___x_722_);
                v_bkt_724_ = lean_array_uget_borrowed(v_buckets_707_, v___x_723_);
                v___x_725_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_704_, v_bkt_724_);
                if v___x_725_ == 0 {
                    v___x_726_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_727_ = lean_nat_add(v_size_706_, v___x_726_);
                    crate::leanh::lean_dec(v_size_706_);
                    crate::leanh::lean_inc(v_bkt_724_);
                    v___x_728_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_728_, 0, v_a_704_);
                    crate::leanh::lean_ctor_set(v___x_728_, 1, v_b_705_);
                    crate::leanh::lean_ctor_set(v___x_728_, 2, v_bkt_724_);
                    v_buckets_x27_729_ = lean_array_uset(v_buckets_707_, v___x_723_, v___x_728_);
                    v___x_730_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_731_ = lean_nat_mul(v_size_x27_727_, v___x_730_);
                    v___x_732_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_733_ = lean_nat_div(v___x_731_, v___x_732_);
                    crate::leanh::lean_dec(v___x_731_);
                    v___x_734_ = lean_array_get_size(v_buckets_x27_729_);
                    v___x_735_ = lean_nat_dec_le(v___x_733_, v___x_734_);
                    crate::leanh::lean_dec(v___x_733_);
                    if v___x_735_ == 0 {
                        v_val_736_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_buckets_x27_729_);
                        if v_isShared_710_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_709_, 1, v_val_736_);
                            crate::leanh::lean_ctor_set(v___x_709_, 0, v_size_x27_727_);
                            v___x_738_ = v___x_709_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_739_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 0, v_size_x27_727_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_739_, 1, v_val_736_);
                            v___x_738_ = v_reuseFailAlloc_739_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_710_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_709_, 1, v_buckets_x27_729_);
                            crate::leanh::lean_ctor_set(v___x_709_, 0, v_size_x27_727_);
                            v___x_741_ = v___x_709_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_742_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_742_, 0, v_size_x27_727_);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_742_,
                                1,
                                v_buckets_x27_729_,
                            );
                            v___x_741_ = v_reuseFailAlloc_742_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_724_);
                    v___x_743_ = crate::leanh::lean_box(0);
                    v_buckets_x27_744_ = lean_array_uset(v_buckets_707_, v___x_723_, v___x_743_);
                    v___x_745_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_704_, v_b_705_, v_bkt_724_);
                    v___x_746_ = lean_array_uset(v_buckets_x27_744_, v___x_723_, v___x_745_);
                    if v_isShared_710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_709_, 1, v___x_746_);
                        v___x_748_ = v___x_709_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_749_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_749_, 0, v_size_706_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_749_, 1, v___x_746_);
                        v___x_748_ = v_reuseFailAlloc_749_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_738_;
            }
            3 => {
                return v___x_741_;
            }
            4 => {
                return v___x_748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(
    mut v_as_751_: *mut crate::leanh::LeanObject,
    mut v_i_752_: usize,
    mut v_stop_753_: usize,
    mut v_b_754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_755_: u8 = 0;
    let mut v_fst_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_762_: u8 = 0;
    let mut v___x_763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: usize = 0;
    let mut v___x_769_: usize = 0;
    let mut v_reuseFailAlloc_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_772_: u8 = 0;
    let mut v_unused_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_755_ = lean_usize_dec_eq(v_i_752_, v_stop_753_);
                if v___x_755_ == 0 {
                    v_fst_756_ = crate::leanh::lean_ctor_get(v_b_754_, 0);
                    crate::leanh::lean_inc(v_fst_756_);
                    v_snd_757_ = crate::leanh::lean_ctor_get(v_b_754_, 1);
                    crate::leanh::lean_inc(v_snd_757_);
                    crate::leanh::lean_dec_ref(v_b_754_);
                    v___x_758_ = lean_array_uget(v_as_751_, v_i_752_);
                    v_snd_759_ = crate::leanh::lean_ctor_get(v___x_758_, 1);
                    v_isSharedCheck_772_ = (!crate::leanh::lean_is_exclusive(v___x_758_)) as u8;
                    if v_isSharedCheck_772_ == 0 {
                        v_unused_773_ = crate::leanh::lean_ctor_get(v___x_758_, 0);
                        crate::leanh::lean_dec(v_unused_773_);
                        v___x_761_ = v___x_758_;
                        v_isShared_762_ = v_isSharedCheck_772_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_759_);
                        crate::leanh::lean_dec(v___x_758_);
                        v___x_761_ = crate::leanh::lean_box(0);
                        v_isShared_762_ = v_isSharedCheck_772_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_754_;
                }
            }
            1 => {
                v___x_763_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_764_ = lean_nat_add(v_fst_756_, v___x_763_);
                v___x_765_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(v_snd_757_, v_snd_759_, v_fst_756_);
                if v_isShared_762_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_761_, 1, v___x_765_);
                    crate::leanh::lean_ctor_set(v___x_761_, 0, v___x_764_);
                    v___x_767_ = v___x_761_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_771_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_771_, 0, v___x_764_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_771_, 1, v___x_765_);
                    v___x_767_ = v_reuseFailAlloc_771_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_768_ = 1usize;
                v___x_769_ = lean_usize_add(v_i_752_, v___x_768_);
                v_i_752_ = v___x_769_;
                v_b_754_ = v___x_767_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2___boxed(
    mut v_as_774_: *mut crate::leanh::LeanObject,
    mut v_i_775_: *mut crate::leanh::LeanObject,
    mut v_stop_776_: *mut crate::leanh::LeanObject,
    mut v_b_777_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_778_: usize = 0;
    let mut v_stop_boxed_779_: usize = 0;
    let mut v_res_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_778_ = crate::leanh::lean_unbox_usize(v_i_775_);
    crate::leanh::lean_dec(v_i_775_);
    v_stop_boxed_779_ = crate::leanh::lean_unbox_usize(v_stop_776_);
    crate::leanh::lean_dec(v_stop_776_);
    v_res_780_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v_as_774_, v_i_boxed_778_, v_stop_boxed_779_, v_b_777_);
    crate::leanh::lean_dec_ref(v_as_774_);
    return v_res_780_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(
    mut v_as_781_: *mut crate::leanh::LeanObject,
    mut v_i_782_: *mut crate::leanh::LeanObject,
    mut v_j_783_: *mut crate::leanh::LeanObject,
    mut v_bs_784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_zero_785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_786_: u8 = 0;
    let mut v_one_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_785_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_786_ = lean_nat_dec_eq(v_i_782_, v_zero_785_);
                if v_isZero_786_ == 1 {
                    crate::leanh::lean_dec(v_j_783_);
                    crate::leanh::lean_dec(v_i_782_);
                    return v_bs_784_;
                } else {
                    v_one_787_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_788_ = lean_nat_sub(v_i_782_, v_one_787_);
                    crate::leanh::lean_dec(v_i_782_);
                    v___x_789_ = lean_array_fget_borrowed(v_as_781_, v_j_783_);
                    crate::leanh::lean_inc(v_j_783_);
                    crate::leanh::lean_inc(v___x_789_);
                    v___x_790_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_790_, 0, v___x_789_);
                    crate::leanh::lean_ctor_set(v___x_790_, 1, v_j_783_);
                    v___x_791_ = lean_nat_add(v_j_783_, v_one_787_);
                    crate::leanh::lean_dec(v_j_783_);
                    v___x_792_ = lean_array_push(v_bs_784_, v___x_790_);
                    v_i_782_ = v_n_788_;
                    v_j_783_ = v___x_791_;
                    v_bs_784_ = v___x_792_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg___boxed(
    mut v_as_794_: *mut crate::leanh::LeanObject,
    mut v_i_795_: *mut crate::leanh::LeanObject,
    mut v_j_796_: *mut crate::leanh::LeanObject,
    mut v_bs_797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_798_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(
        v_as_794_, v_i_795_, v_j_796_, v_bs_797_,
    );
    crate::leanh::lean_dec_ref(v_as_794_);
    return v_res_798_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(
    mut v_hi_799_: *mut crate::leanh::LeanObject,
    mut v_pivot_800_: *mut crate::leanh::LeanObject,
    mut v_as_801_: *mut crate::leanh::LeanObject,
    mut v_i_802_: *mut crate::leanh::LeanObject,
    mut v_k_803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_804_: u8 = 0;
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_804_ = lean_nat_dec_lt(v_k_803_, v_hi_799_);
                if v___x_804_ == 0 {
                    crate::leanh::lean_dec(v_k_803_);
                    v___x_805_ = lean_array_fswap(v_as_801_, v_i_802_, v_hi_799_);
                    v___x_806_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_806_, 0, v_i_802_);
                    crate::leanh::lean_ctor_set(v___x_806_, 1, v___x_805_);
                    return v___x_806_;
                } else {
                    v___x_807_ = lean_array_fget_borrowed(v_as_801_, v_k_803_);
                    v_fst_808_ = crate::leanh::lean_ctor_get(v___x_807_, 0);
                    v_fst_809_ = crate::leanh::lean_ctor_get(v_pivot_800_, 0);
                    v___x_810_ = lean_expr_lt(v_fst_808_, v_fst_809_);
                    if v___x_810_ == 0 {
                        v___x_811_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_812_ = lean_nat_add(v_k_803_, v___x_811_);
                        crate::leanh::lean_dec(v_k_803_);
                        v_k_803_ = v___x_812_;
                        state = 0;
                        continue;
                    } else {
                        v___x_814_ = lean_array_fswap(v_as_801_, v_i_802_, v_k_803_);
                        v___x_815_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_816_ = lean_nat_add(v_i_802_, v___x_815_);
                        crate::leanh::lean_dec(v_i_802_);
                        v___x_817_ = lean_nat_add(v_k_803_, v___x_815_);
                        crate::leanh::lean_dec(v_k_803_);
                        v_as_801_ = v___x_814_;
                        v_i_802_ = v___x_816_;
                        v_k_803_ = v___x_817_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg___boxed(
    mut v_hi_819_: *mut crate::leanh::LeanObject,
    mut v_pivot_820_: *mut crate::leanh::LeanObject,
    mut v_as_821_: *mut crate::leanh::LeanObject,
    mut v_i_822_: *mut crate::leanh::LeanObject,
    mut v_k_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_824_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_819_, v_pivot_820_, v_as_821_, v_i_822_, v_k_823_);
    crate::leanh::lean_dec_ref(v_pivot_820_);
    crate::leanh::lean_dec(v_hi_819_);
    return v_res_824_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(
    mut v_x_825_: *mut crate::leanh::LeanObject,
    mut v_x_826_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_fst_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_829_: u8 = 0;
    v_fst_827_ = crate::leanh::lean_ctor_get(v_x_825_, 0);
    v_fst_828_ = crate::leanh::lean_ctor_get(v_x_826_, 0);
    v___x_829_ = lean_expr_lt(v_fst_827_, v_fst_828_);
    return v___x_829_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0___boxed(
    mut v_x_830_: *mut crate::leanh::LeanObject,
    mut v_x_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: u8 = 0;
    let mut v_r_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v_x_830_, v_x_831_);
    crate::leanh::lean_dec_ref(v_x_831_);
    crate::leanh::lean_dec_ref(v_x_830_);
    v_r_833_ = crate::leanh::lean_box((v_res_832_) as usize);
    return v_r_833_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(
    mut v_n_834_: *mut crate::leanh::LeanObject,
    mut v_as_835_: *mut crate::leanh::LeanObject,
    mut v_lo_836_: *mut crate::leanh::LeanObject,
    mut v_hi_837_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_844_: u8 = 0;
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: u8 = 0;
    let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: u8 = 0;
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_863_: u8 = 0;
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_849_ = lean_nat_dec_lt(v_lo_836_, v_hi_837_);
                if v___x_849_ == 0 {
                    crate::leanh::lean_dec(v_lo_836_);
                    return v_as_835_;
                } else {
                    v___x_850_ = lean_nat_add(v_lo_836_, v_hi_837_);
                    v___x_851_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_mid_852_ = lean_nat_shiftr(v___x_850_, v___x_851_);
                    crate::leanh::lean_dec(v___x_850_);
                    v___x_865_ = lean_array_fget_borrowed(v_as_835_, v_mid_852_);
                    v___x_866_ = lean_array_fget_borrowed(v_as_835_, v_lo_836_);
                    v___x_867_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_865_, v___x_866_);
                    if v___x_867_ == 0 {
                        v___y_860_ = v_as_835_;
                        state = 3;
                        continue;
                    } else {
                        v___x_868_ = lean_array_fswap(v_as_835_, v_lo_836_, v_mid_852_);
                        v___y_860_ = v___x_868_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_840_ = lean_array_fget(v___y_839_, v_hi_837_);
                crate::leanh::lean_inc_n(v_lo_836_, 2);
                v___x_841_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_837_, v_pivot_840_, v___y_839_, v_lo_836_, v_lo_836_);
                crate::leanh::lean_dec(v_pivot_840_);
                v_fst_842_ = crate::leanh::lean_ctor_get(v___x_841_, 0);
                crate::leanh::lean_inc(v_fst_842_);
                v_snd_843_ = crate::leanh::lean_ctor_get(v___x_841_, 1);
                crate::leanh::lean_inc(v_snd_843_);
                crate::leanh::lean_dec_ref(v___x_841_);
                v___x_844_ = lean_nat_dec_le(v_hi_837_, v_fst_842_);
                if v___x_844_ == 0 {
                    v___x_845_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_834_, v_snd_843_, v_lo_836_, v_fst_842_);
                    v___x_846_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_847_ = lean_nat_add(v_fst_842_, v___x_846_);
                    crate::leanh::lean_dec(v_fst_842_);
                    v_as_835_ = v___x_845_;
                    v_lo_836_ = v___x_847_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_fst_842_);
                    crate::leanh::lean_dec(v_lo_836_);
                    return v_snd_843_;
                }
            }
            2 => {
                v___x_855_ = lean_array_fget_borrowed(v___y_854_, v_mid_852_);
                v___x_856_ = lean_array_fget_borrowed(v___y_854_, v_hi_837_);
                v___x_857_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_855_, v___x_856_);
                if v___x_857_ == 0 {
                    crate::leanh::lean_dec(v_mid_852_);
                    v___y_839_ = v___y_854_;
                    state = 1;
                    continue;
                } else {
                    v___x_858_ = lean_array_fswap(v___y_854_, v_mid_852_, v_hi_837_);
                    crate::leanh::lean_dec(v_mid_852_);
                    v___y_839_ = v___x_858_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_861_ = lean_array_fget_borrowed(v___y_860_, v_hi_837_);
                v___x_862_ = lean_array_fget_borrowed(v___y_860_, v_lo_836_);
                v___x_863_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___lam__0(v___x_861_, v___x_862_);
                if v___x_863_ == 0 {
                    v___y_854_ = v___y_860_;
                    state = 2;
                    continue;
                } else {
                    v___x_864_ = lean_array_fswap(v___y_860_, v_lo_836_, v_hi_837_);
                    v___y_854_ = v___x_864_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg___boxed(
    mut v_n_869_: *mut crate::leanh::LeanObject,
    mut v_as_870_: *mut crate::leanh::LeanObject,
    mut v_lo_871_: *mut crate::leanh::LeanObject,
    mut v_hi_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_869_, v_as_870_, v_lo_871_, v_hi_872_);
    crate::leanh::lean_dec(v_hi_872_);
    crate::leanh::lean_dec(v_n_869_);
    return v_res_873_;
}
pub unsafe fn _init_l_Lean_sortExprs___closed__0() -> *mut crate::leanh::LeanObject {
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = crate::leanh::lean_box(0);
    v___x_875_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_876_ = lean_mk_array(v___x_875_, v___x_874_);
    return v___x_876_;
}
pub unsafe fn _init_l_Lean_sortExprs___closed__1() -> *mut crate::leanh::LeanObject {
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_877_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__0),
        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__0_once),
        _init_l_Lean_sortExprs___closed__0,
    );
    v___x_878_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_879_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_879_, 0, v___x_878_);
    crate::leanh::lean_ctor_set(v___x_879_, 1, v___x_877_);
    return v___x_879_;
}
pub unsafe fn _init_l_Lean_sortExprs___closed__2() -> *mut crate::leanh::LeanObject {
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_880_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__1),
        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__1_once),
        _init_l_Lean_sortExprs___closed__1,
    );
    v___x_881_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_882_, 0, v___x_881_);
    crate::leanh::lean_ctor_set(v___x_882_, 1, v___x_880_);
    return v___x_882_;
}
pub unsafe fn l_Lean_sortExprs(
    mut v_es_883_: *mut crate::leanh::LeanObject,
    mut v_lt_884_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_888_: usize = 0;
    let mut v___x_889_: usize = 0;
    let mut v_es_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: u8 = 0;
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: u8 = 0;
    let mut v___x_904_: usize = 0;
    let mut v___x_905_: usize = 0;
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_907_: usize = 0;
    let mut v___x_908_: usize = 0;
    let mut v___x_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_es_913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: u8 = 0;
    let mut v___x_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_924_: u8 = 0;
    let mut v___x_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_931_: u8 = 0;
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v___x_937_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_910_ = lean_array_get_size(v_es_883_);
                v___x_911_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_912_ = lean_mk_empty_array_with_capacity(v___x_910_);
                v_es_913_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(
                    v_es_883_, v___x_910_, v___x_911_, v___x_912_,
                );
                if v_lt_884_ == 0 {
                    v___x_914_ = lean_array_get_size(v_es_913_);
                    v___x_919_ = lean_nat_dec_eq(v___x_914_, v___x_911_);
                    if v___x_919_ == 0 {
                        v___x_920_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_921_ = lean_nat_sub(v___x_914_, v___x_920_);
                        v___x_925_ = lean_nat_dec_le(v___x_911_, v___x_921_);
                        if v___x_925_ == 0 {
                            crate::leanh::lean_inc(v___x_921_);
                            v___y_923_ = v___x_921_;
                            state = 5;
                            continue;
                        } else {
                            v___y_923_ = v___x_911_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v___y_897_ = v_es_913_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_926_ = lean_array_get_size(v_es_913_);
                    v___x_931_ = lean_nat_dec_eq(v___x_926_, v___x_911_);
                    if v___x_931_ == 0 {
                        v___x_932_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_933_ = lean_nat_sub(v___x_926_, v___x_932_);
                        v___x_937_ = lean_nat_dec_le(v___x_911_, v___x_933_);
                        if v___x_937_ == 0 {
                            crate::leanh::lean_inc(v___x_933_);
                            v___y_935_ = v___x_933_;
                            state = 7;
                            continue;
                        } else {
                            v___y_935_ = v___x_911_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v___y_897_ = v_es_913_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_sz_888_ = lean_array_size(v___y_886_);
                v___x_889_ = 0usize;
                v_es_890_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_sortExprs_spec__1(v_sz_888_, v___x_889_, v___y_886_);
                v___x_891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_891_, 0, v_es_890_);
                crate::leanh::lean_ctor_set(v___x_891_, 1, v_snd_887_);
                return v___x_891_;
            }
            2 => {
                v_snd_895_ = crate::leanh::lean_ctor_get(v___y_894_, 1);
                crate::leanh::lean_inc(v_snd_895_);
                crate::leanh::lean_dec_ref(v___y_894_);
                v___y_886_ = v___y_893_;
                v_snd_887_ = v_snd_895_;
                state = 1;
                continue;
            }
            3 => {
                v___x_898_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_899_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__1_once),
                    _init_l_Lean_sortExprs___closed__1,
                );
                v___x_900_ = lean_array_get_size(v___y_897_);
                v___x_901_ = lean_nat_dec_lt(v___x_898_, v___x_900_);
                if v___x_901_ == 0 {
                    v___y_886_ = v___y_897_;
                    v_snd_887_ = v___x_899_;
                    state = 1;
                    continue;
                } else {
                    v___x_902_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__2),
                        core::ptr::addr_of_mut!(l_Lean_sortExprs___closed__2_once),
                        _init_l_Lean_sortExprs___closed__2,
                    );
                    v___x_903_ = lean_nat_dec_le(v___x_900_, v___x_900_);
                    if v___x_903_ == 0 {
                        if v___x_901_ == 0 {
                            v___y_886_ = v___y_897_;
                            v_snd_887_ = v___x_899_;
                            state = 1;
                            continue;
                        } else {
                            v___x_904_ = 0usize;
                            v___x_905_ = lean_usize_of_nat(v___x_900_);
                            v___x_906_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_897_, v___x_904_, v___x_905_, v___x_902_);
                            v___y_893_ = v___y_897_;
                            v___y_894_ = v___x_906_;
                            state = 2;
                            continue;
                        }
                    } else {
                        v___x_907_ = 0usize;
                        v___x_908_ = lean_usize_of_nat(v___x_900_);
                        v___x_909_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_sortExprs_spec__2(v___y_897_, v___x_907_, v___x_908_, v___x_902_);
                        v___y_893_ = v___y_897_;
                        v___y_894_ = v___x_909_;
                        state = 2;
                        continue;
                    }
                }
            }
            4 => {
                v___x_918_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v___x_914_, v_es_913_, v___y_916_, v___y_917_);
                crate::leanh::lean_dec(v___y_917_);
                v___y_897_ = v___x_918_;
                state = 3;
                continue;
            }
            5 => {
                v___x_924_ = lean_nat_dec_le(v___y_923_, v___x_921_);
                if v___x_924_ == 0 {
                    crate::leanh::lean_dec(v___x_921_);
                    crate::leanh::lean_inc(v___y_923_);
                    v___y_916_ = v___y_923_;
                    v___y_917_ = v___y_923_;
                    state = 4;
                    continue;
                } else {
                    v___y_916_ = v___y_923_;
                    v___y_917_ = v___x_921_;
                    state = 4;
                    continue;
                }
            }
            6 => {
                v___x_930_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v___x_926_, v_es_913_, v___y_928_, v___y_929_);
                crate::leanh::lean_dec(v___y_929_);
                v___y_897_ = v___x_930_;
                state = 3;
                continue;
            }
            7 => {
                v___x_936_ = lean_nat_dec_le(v___y_935_, v___x_933_);
                if v___x_936_ == 0 {
                    crate::leanh::lean_dec(v___x_933_);
                    crate::leanh::lean_inc(v___y_935_);
                    v___y_928_ = v___y_935_;
                    v___y_929_ = v___y_935_;
                    state = 6;
                    continue;
                } else {
                    v___y_928_ = v___y_935_;
                    v___y_929_ = v___x_933_;
                    state = 6;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_sortExprs___boxed(
    mut v_es_938_: *mut crate::leanh::LeanObject,
    mut v_lt_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lt_boxed_940_: u8 = 0;
    let mut v_res_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_lt_boxed_940_ = (crate::leanh::lean_unbox(v_lt_939_) as u8);
    v_res_941_ = l_Lean_sortExprs(v_es_938_, v_lt_boxed_940_);
    crate::leanh::lean_dec_ref(v_es_938_);
    return v_res_941_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0(
    mut v_00_u03b2_942_: *mut crate::leanh::LeanObject,
    mut v_m_943_: *mut crate::leanh::LeanObject,
    mut v_a_944_: *mut crate::leanh::LeanObject,
    mut v_b_945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_946_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0___redArg(
        v_m_943_, v_a_944_, v_b_945_,
    );
    return v___x_946_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(
    mut v_as_947_: *mut crate::leanh::LeanObject,
    mut v_i_948_: *mut crate::leanh::LeanObject,
    mut v_j_949_: *mut crate::leanh::LeanObject,
    mut v_inv_950_: *mut crate::leanh::LeanObject,
    mut v_bs_951_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_952_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___redArg(
        v_as_947_, v_i_948_, v_j_949_, v_bs_951_,
    );
    return v___x_952_;
}
pub unsafe fn l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3___boxed(
    mut v_as_953_: *mut crate::leanh::LeanObject,
    mut v_i_954_: *mut crate::leanh::LeanObject,
    mut v_j_955_: *mut crate::leanh::LeanObject,
    mut v_inv_956_: *mut crate::leanh::LeanObject,
    mut v_bs_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_958_ = l_Array_mapFinIdxM_map___at___00Lean_sortExprs_spec__3(
        v_as_953_, v_i_954_, v_j_955_, v_inv_956_, v_bs_957_,
    );
    crate::leanh::lean_dec_ref(v_as_953_);
    return v_res_958_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(
    mut v_n_959_: *mut crate::leanh::LeanObject,
    mut v_as_960_: *mut crate::leanh::LeanObject,
    mut v_lo_961_: *mut crate::leanh::LeanObject,
    mut v_hi_962_: *mut crate::leanh::LeanObject,
    mut v_w_963_: *mut crate::leanh::LeanObject,
    mut v_hlo_964_: *mut crate::leanh::LeanObject,
    mut v_hhi_965_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_966_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___redArg(v_n_959_, v_as_960_, v_lo_961_, v_hi_962_);
    return v___x_966_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4___boxed(
    mut v_n_967_: *mut crate::leanh::LeanObject,
    mut v_as_968_: *mut crate::leanh::LeanObject,
    mut v_lo_969_: *mut crate::leanh::LeanObject,
    mut v_hi_970_: *mut crate::leanh::LeanObject,
    mut v_w_971_: *mut crate::leanh::LeanObject,
    mut v_hlo_972_: *mut crate::leanh::LeanObject,
    mut v_hhi_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_974_ =
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4(
            v_n_967_, v_as_968_, v_lo_969_, v_hi_970_, v_w_971_, v_hlo_972_, v_hhi_973_,
        );
    crate::leanh::lean_dec(v_hi_970_);
    crate::leanh::lean_dec(v_n_967_);
    return v_res_974_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(
    mut v_n_975_: *mut crate::leanh::LeanObject,
    mut v_as_976_: *mut crate::leanh::LeanObject,
    mut v_lo_977_: *mut crate::leanh::LeanObject,
    mut v_hi_978_: *mut crate::leanh::LeanObject,
    mut v_w_979_: *mut crate::leanh::LeanObject,
    mut v_hlo_980_: *mut crate::leanh::LeanObject,
    mut v_hhi_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_982_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___redArg(v_n_975_, v_as_976_, v_lo_977_, v_hi_978_);
    return v___x_982_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5___boxed(
    mut v_n_983_: *mut crate::leanh::LeanObject,
    mut v_as_984_: *mut crate::leanh::LeanObject,
    mut v_lo_985_: *mut crate::leanh::LeanObject,
    mut v_hi_986_: *mut crate::leanh::LeanObject,
    mut v_w_987_: *mut crate::leanh::LeanObject,
    mut v_hlo_988_: *mut crate::leanh::LeanObject,
    mut v_hhi_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_990_ =
        l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5(
            v_n_983_, v_as_984_, v_lo_985_, v_hi_986_, v_w_987_, v_hlo_988_, v_hhi_989_,
        );
    crate::leanh::lean_dec(v_hi_986_);
    crate::leanh::lean_dec(v_n_983_);
    return v_res_990_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(
    mut v_00_u03b2_991_: *mut crate::leanh::LeanObject,
    mut v_a_992_: *mut crate::leanh::LeanObject,
    mut v_x_993_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_994_: u8 = 0;
    v___x_994_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___redArg(v_a_992_, v_x_993_);
    return v___x_994_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0___boxed(
    mut v_00_u03b2_995_: *mut crate::leanh::LeanObject,
    mut v_a_996_: *mut crate::leanh::LeanObject,
    mut v_x_997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_998_: u8 = 0;
    let mut v_r_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_998_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__0(v_00_u03b2_995_, v_a_996_, v_x_997_);
    crate::leanh::lean_dec(v_x_997_);
    crate::leanh::lean_dec(v_a_996_);
    v_r_999_ = crate::leanh::lean_box((v_res_998_) as usize);
    return v_r_999_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1(
    mut v_00_u03b2_1000_: *mut crate::leanh::LeanObject,
    mut v_data_1001_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1002_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1___redArg(v_data_1001_);
    return v___x_1002_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2(
    mut v_00_u03b2_1003_: *mut crate::leanh::LeanObject,
    mut v_a_1004_: *mut crate::leanh::LeanObject,
    mut v_b_1005_: *mut crate::leanh::LeanObject,
    mut v_x_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1007_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__2___redArg(v_a_1004_, v_b_1005_, v_x_1006_);
    return v___x_1007_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(
    mut v_n_1008_: *mut crate::leanh::LeanObject,
    mut v_lo_1009_: *mut crate::leanh::LeanObject,
    mut v_hi_1010_: *mut crate::leanh::LeanObject,
    mut v_hhi_1011_: *mut crate::leanh::LeanObject,
    mut v_pivot_1012_: *mut crate::leanh::LeanObject,
    mut v_as_1013_: *mut crate::leanh::LeanObject,
    mut v_i_1014_: *mut crate::leanh::LeanObject,
    mut v_k_1015_: *mut crate::leanh::LeanObject,
    mut v_ilo_1016_: *mut crate::leanh::LeanObject,
    mut v_ik_1017_: *mut crate::leanh::LeanObject,
    mut v_w_1018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1019_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___redArg(v_hi_1010_, v_pivot_1012_, v_as_1013_, v_i_1014_, v_k_1015_);
    return v___x_1019_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7___boxed(
    mut v_n_1020_: *mut crate::leanh::LeanObject,
    mut v_lo_1021_: *mut crate::leanh::LeanObject,
    mut v_hi_1022_: *mut crate::leanh::LeanObject,
    mut v_hhi_1023_: *mut crate::leanh::LeanObject,
    mut v_pivot_1024_: *mut crate::leanh::LeanObject,
    mut v_as_1025_: *mut crate::leanh::LeanObject,
    mut v_i_1026_: *mut crate::leanh::LeanObject,
    mut v_k_1027_: *mut crate::leanh::LeanObject,
    mut v_ilo_1028_: *mut crate::leanh::LeanObject,
    mut v_ik_1029_: *mut crate::leanh::LeanObject,
    mut v_w_1030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1031_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__4_spec__7(v_n_1020_, v_lo_1021_, v_hi_1022_, v_hhi_1023_, v_pivot_1024_, v_as_1025_, v_i_1026_, v_k_1027_, v_ilo_1028_, v_ik_1029_, v_w_1030_);
    crate::leanh::lean_dec_ref(v_pivot_1024_);
    crate::leanh::lean_dec(v_hi_1022_);
    crate::leanh::lean_dec(v_lo_1021_);
    crate::leanh::lean_dec(v_n_1020_);
    return v_res_1031_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(
    mut v_n_1032_: *mut crate::leanh::LeanObject,
    mut v_lo_1033_: *mut crate::leanh::LeanObject,
    mut v_hi_1034_: *mut crate::leanh::LeanObject,
    mut v_hhi_1035_: *mut crate::leanh::LeanObject,
    mut v_pivot_1036_: *mut crate::leanh::LeanObject,
    mut v_as_1037_: *mut crate::leanh::LeanObject,
    mut v_i_1038_: *mut crate::leanh::LeanObject,
    mut v_k_1039_: *mut crate::leanh::LeanObject,
    mut v_ilo_1040_: *mut crate::leanh::LeanObject,
    mut v_ik_1041_: *mut crate::leanh::LeanObject,
    mut v_w_1042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1043_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___redArg(v_hi_1034_, v_pivot_1036_, v_as_1037_, v_i_1038_, v_k_1039_);
    return v___x_1043_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9___boxed(
    mut v_n_1044_: *mut crate::leanh::LeanObject,
    mut v_lo_1045_: *mut crate::leanh::LeanObject,
    mut v_hi_1046_: *mut crate::leanh::LeanObject,
    mut v_hhi_1047_: *mut crate::leanh::LeanObject,
    mut v_pivot_1048_: *mut crate::leanh::LeanObject,
    mut v_as_1049_: *mut crate::leanh::LeanObject,
    mut v_i_1050_: *mut crate::leanh::LeanObject,
    mut v_k_1051_: *mut crate::leanh::LeanObject,
    mut v_ilo_1052_: *mut crate::leanh::LeanObject,
    mut v_ik_1053_: *mut crate::leanh::LeanObject,
    mut v_w_1054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1055_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00Lean_sortExprs_spec__5_spec__9(v_n_1044_, v_lo_1045_, v_hi_1046_, v_hhi_1047_, v_pivot_1048_, v_as_1049_, v_i_1050_, v_k_1051_, v_ilo_1052_, v_ik_1053_, v_w_1054_);
    crate::leanh::lean_dec_ref(v_pivot_1048_);
    crate::leanh::lean_dec(v_hi_1046_);
    crate::leanh::lean_dec(v_lo_1045_);
    crate::leanh::lean_dec(v_n_1044_);
    return v_res_1055_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1056_: *mut crate::leanh::LeanObject,
    mut v_i_1057_: *mut crate::leanh::LeanObject,
    mut v_source_1058_: *mut crate::leanh::LeanObject,
    mut v_target_1059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1060_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2___redArg(v_i_1057_, v_source_1058_, v_target_1059_);
    return v___x_1060_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8(
    mut v_00_u03b2_1061_: *mut crate::leanh::LeanObject,
    mut v_x_1062_: *mut crate::leanh::LeanObject,
    mut v_x_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1064_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_sortExprs_spec__0_spec__1_spec__2_spec__8___redArg(v_x_1062_, v_x_1063_);
    return v___x_1064_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Util_SortExprs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Util_SortExprs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Util_SortExprs(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Expr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Util_SortExprs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Util_SortExprs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Util_SortExprs(builtin);
}

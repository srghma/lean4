// Lean compiler output
// Module: Lean.Meta.KExprMap
// Imports: Lean.Data.AssocList Lean.HeadIndex Lean.Meta.Basic
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get_borrowed,
    lean_array_get_size, lean_array_push, lean_nat_add, lean_nat_dec_lt, lean_uint64_to_usize,
    lean_usize_add, lean_usize_dec_le, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Lean::Data::AssocList::{
    initialize_Lean_Data_AssocList, runtime_initialize_Lean_Data_AssocList,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::HeadIndex::{
    initialize_Lean_HeadIndex, l_Lean_Expr_toHeadIndex, l_Lean_HeadIndex_hash,
    l_Lean_instBEqHeadIndex_beq, runtime_initialize_Lean_HeadIndex,
};
use crate::r#gen::Lean::Meta::Basic::{
    initialize_Lean_Meta_Basic, l_Lean_Meta_isExprDefEq, runtime_initialize_Lean_Meta_Basic,
};
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedKExprMap___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedKExprMap___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_574_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_574_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_575_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0,
    );
    v___x_576_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_576_, 0, v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_Lean_Meta_instInhabitedKExprMap_default(
    mut v_00_u03b1_577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_578_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_578_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1,
    );
    return v___x_578_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap___closed__0() -> *mut leanh::LeanObject
{
    let mut v___x_579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_579_ = l_Lean_Meta_instInhabitedKExprMap_default(leanh::lean_box(0));
    return v___x_579_;
}
pub unsafe fn l_Lean_Meta_instInhabitedKExprMap(
    mut v_a_580_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_581_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_581_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap___closed__0_once),
        _init_l_Lean_Meta_instInhabitedKExprMap___closed__0,
    );
    return v___x_581_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_582_: *mut leanh::LeanObject,
    mut v_vals_583_: *mut leanh::LeanObject,
    mut v_i_584_: *mut leanh::LeanObject,
    mut v_k_585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_586_ = lean_array_get_size(v_keys_582_);
                v___x_587_ = lean_nat_dec_lt(v_i_584_, v___x_586_);
                if v___x_587_ == 0 {
                    leanh::lean_dec(v_i_584_);
                    v___x_588_ = leanh::lean_box(0);
                    return v___x_588_;
                } else {
                    v_k_x27_589_ = lean_array_fget_borrowed(v_keys_582_, v_i_584_);
                    v___x_590_ = l_Lean_instBEqHeadIndex_beq(v_k_585_, v_k_x27_589_);
                    if v___x_590_ == 0 {
                        v___x_591_ = leanh::lean_unsigned_to_nat(1);
                        v___x_592_ = lean_nat_add(v_i_584_, v___x_591_);
                        leanh::lean_dec(v_i_584_);
                        v_i_584_ = v___x_592_;
                        state = 0;
                        continue;
                    } else {
                        v___x_594_ = lean_array_fget_borrowed(v_vals_583_, v_i_584_);
                        leanh::lean_dec(v_i_584_);
                        leanh::lean_inc(v___x_594_);
                        v___x_595_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_595_, 0, v___x_594_);
                        return v___x_595_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_596_: *mut leanh::LeanObject,
    mut v_vals_597_: *mut leanh::LeanObject,
    mut v_i_598_: *mut leanh::LeanObject,
    mut v_k_599_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_600_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_596_, v_vals_597_, v_i_598_, v_k_599_);
    leanh::lean_dec(v_k_599_);
    leanh::lean_dec_ref(v_vals_597_);
    leanh::lean_dec_ref(v_keys_596_);
    return v_res_600_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_601_: usize = 0;
    let mut v___x_602_: usize = 0;
    let mut v___x_603_: usize = 0;
    v___x_601_ = 5usize;
    v___x_602_ = 1usize;
    v___x_603_ = lean_usize_shift_left(v___x_602_, v___x_601_);
    return v___x_603_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_604_: usize = 0;
    let mut v___x_605_: usize = 0;
    let mut v___x_606_: usize = 0;
    v___x_604_ = 1usize;
    v___x_605_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_606_ = lean_usize_sub(v___x_605_, v___x_604_);
    return v___x_606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(
    mut v_x_607_: *mut leanh::LeanObject,
    mut v_x_608_: usize,
    mut v_x_609_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_612_: usize = 0;
    let mut v___x_613_: usize = 0;
    let mut v___x_614_: usize = 0;
    let mut v_j_615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_623_: usize = 0;
    let mut v___x_625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_607_) == 0 {
                    v_es_610_ = leanh::lean_ctor_get(v_x_607_, 0);
                    v___x_611_ = leanh::lean_box(2);
                    v___x_612_ = 5usize;
                    v___x_613_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_614_ = lean_usize_land(v_x_608_, v___x_613_);
                    v_j_615_ = lean_usize_to_nat(v___x_614_);
                    v___x_616_ = lean_array_get_borrowed(v___x_611_, v_es_610_, v_j_615_);
                    leanh::lean_dec(v_j_615_);
                    match leanh::lean_obj_tag(v___x_616_) {
                        0 => {
                            v_key_617_ = leanh::lean_ctor_get(v___x_616_, 0);
                            v_val_618_ = leanh::lean_ctor_get(v___x_616_, 1);
                            v___x_619_ = l_Lean_instBEqHeadIndex_beq(v_x_609_, v_key_617_);
                            if v___x_619_ == 0 {
                                v___x_620_ = leanh::lean_box(0);
                                return v___x_620_;
                            } else {
                                leanh::lean_inc(v_val_618_);
                                v___x_621_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_621_, 0, v_val_618_);
                                return v___x_621_;
                            }
                        }
                        1 => {
                            v_node_622_ = leanh::lean_ctor_get(v___x_616_, 0);
                            v___x_623_ = lean_usize_shift_right(v_x_608_, v___x_612_);
                            v_x_607_ = v_node_622_;
                            v_x_608_ = v___x_623_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_625_ = leanh::lean_box(0);
                            return v___x_625_;
                        }
                    }
                } else {
                    v_ks_626_ = leanh::lean_ctor_get(v_x_607_, 0);
                    v_vs_627_ = leanh::lean_ctor_get(v_x_607_, 1);
                    v___x_628_ = leanh::lean_unsigned_to_nat(0);
                    v___x_629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_626_, v_vs_627_, v___x_628_, v_x_609_);
                    return v___x_629_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_630_: *mut leanh::LeanObject,
    mut v_x_631_: *mut leanh::LeanObject,
    mut v_x_632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1462__boxed_633_: usize = 0;
    let mut v_res_634_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1462__boxed_633_ = leanh::lean_unbox_usize(v_x_631_);
    leanh::lean_dec(v_x_631_);
    v_res_634_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_630_, v_x_1462__boxed_633_, v_x_632_);
    leanh::lean_dec(v_x_632_);
    leanh::lean_dec_ref(v_x_630_);
    return v_res_634_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
    mut v_x_635_: *mut leanh::LeanObject,
    mut v_x_636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_637_: u64 = 0;
    let mut v___x_638_: usize = 0;
    let mut v___x_639_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_637_ = l_Lean_HeadIndex_hash(v_x_636_);
    v___x_638_ = lean_uint64_to_usize(v___x_637_);
    v___x_639_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_635_, v___x_638_, v_x_636_);
    return v___x_639_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(
    mut v_x_640_: *mut leanh::LeanObject,
    mut v_x_641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_642_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
            v_x_640_, v_x_641_,
        );
    leanh::lean_dec(v_x_641_);
    leanh::lean_dec_ref(v_x_640_);
    return v_res_642_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(
    mut v_e_646_: *mut leanh::LeanObject,
    mut v_x_647_: *mut leanh::LeanObject,
    mut v_x_648_: *mut leanh::LeanObject,
    mut v___y_649_: *mut leanh::LeanObject,
    mut v___y_650_: *mut leanh::LeanObject,
    mut v___y_651_: *mut leanh::LeanObject,
    mut v___y_652_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_a_674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_648_) == 0 {
                    leanh::lean_dec_ref(v_e_646_);
                    v___x_654_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_654_, 0, v_x_647_);
                    return v___x_654_;
                } else {
                    leanh::lean_dec_ref(v_x_647_);
                    v_key_655_ = leanh::lean_ctor_get(v_x_648_, 0);
                    leanh::lean_inc(v_key_655_);
                    v_value_656_ = leanh::lean_ctor_get(v_x_648_, 1);
                    leanh::lean_inc(v_value_656_);
                    v_tail_657_ = leanh::lean_ctor_get(v_x_648_, 2);
                    leanh::lean_inc(v_tail_657_);
                    leanh::lean_dec_ref_known(v_x_648_, 3);
                    leanh::lean_inc_ref(v_e_646_);
                    v___x_658_ = l_Lean_Meta_isExprDefEq(
                        v_e_646_, v_key_655_, v___y_649_, v___y_650_, v___y_651_, v___y_652_,
                    );
                    if leanh::lean_obj_tag(v___x_658_) == 0 {
                        v_a_659_ = leanh::lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_673_ = (!leanh::lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_661_ = v___x_658_;
                            v_isShared_662_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_659_);
                            leanh::lean_dec(v___x_658_);
                            v___x_661_ = leanh::lean_box(0);
                            v_isShared_662_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_tail_657_);
                        leanh::lean_dec(v_value_656_);
                        leanh::lean_dec_ref(v_e_646_);
                        v_a_674_ = leanh::lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_681_ = (!leanh::lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_681_ == 0 {
                            v___x_676_ = v___x_658_;
                            v_isShared_677_ = v_isSharedCheck_681_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_674_);
                            leanh::lean_dec(v___x_658_);
                            v___x_676_ = leanh::lean_box(0);
                            v_isShared_677_ = v_isSharedCheck_681_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_663_ = leanh::lean_box(0);
                v___x_664_ = (leanh::lean_unbox(v_a_659_) as u8);
                leanh::lean_dec(v_a_659_);
                if v___x_664_ == 0 {
                    leanh::lean_del_object(v___x_661_);
                    leanh::lean_dec(v_value_656_);
                    v___x_665_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0;
                    v_x_647_ = v___x_665_;
                    v_x_648_ = v_tail_657_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_tail_657_);
                    leanh::lean_dec_ref(v_e_646_);
                    v___x_667_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_667_, 0, v_value_656_);
                    v___x_668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_668_, 0, v___x_667_);
                    v___x_669_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_669_, 0, v___x_668_);
                    leanh::lean_ctor_set(v___x_669_, 1, v___x_663_);
                    if v_isShared_662_ == 0 {
                        leanh::lean_ctor_set(v___x_661_, 0, v___x_669_);
                        v___x_671_ = v___x_661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_672_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
                        v___x_671_ = v_reuseFailAlloc_672_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_671_;
            }
            3 => {
                if v_isShared_677_ == 0 {
                    v___x_679_ = v___x_676_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_680_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
                    v___x_679_ = v_reuseFailAlloc_680_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_679_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___boxed(
    mut v_e_682_: *mut leanh::LeanObject,
    mut v_x_683_: *mut leanh::LeanObject,
    mut v_x_684_: *mut leanh::LeanObject,
    mut v___y_685_: *mut leanh::LeanObject,
    mut v___y_686_: *mut leanh::LeanObject,
    mut v___y_687_: *mut leanh::LeanObject,
    mut v___y_688_: *mut leanh::LeanObject,
    mut v___y_689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_690_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_682_, v_x_683_, v_x_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
    leanh::lean_dec(v___y_688_);
    leanh::lean_dec_ref(v___y_687_);
    leanh::lean_dec(v___y_686_);
    leanh::lean_dec_ref(v___y_685_);
    return v_res_690_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f___redArg(
    mut v_m_691_: *mut leanh::LeanObject,
    mut v_e_692_: *mut leanh::LeanObject,
    mut v_a_693_: *mut leanh::LeanObject,
    mut v_a_694_: *mut leanh::LeanObject,
    mut v_a_695_: *mut leanh::LeanObject,
    mut v_a_696_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v_fst_710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_a_719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_692_);
                v___x_698_ = l_Lean_Expr_toHeadIndex(v_e_692_);
                v___x_699_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_691_, v___x_698_);
                leanh::lean_dec(v___x_698_);
                if leanh::lean_obj_tag(v___x_699_) == 0 {
                    leanh::lean_dec_ref(v_e_692_);
                    v___x_700_ = leanh::lean_box(0);
                    v___x_701_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_701_, 0, v___x_700_);
                    return v___x_701_;
                } else {
                    v_val_702_ = leanh::lean_ctor_get(v___x_699_, 0);
                    leanh::lean_inc(v_val_702_);
                    leanh::lean_dec_ref_known(v___x_699_, 1);
                    v___x_703_ = leanh::lean_box(0);
                    v___x_704_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0;
                    v___x_705_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_692_, v___x_704_, v_val_702_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
                    if leanh::lean_obj_tag(v___x_705_) == 0 {
                        v_a_706_ = leanh::lean_ctor_get(v___x_705_, 0);
                        v_isSharedCheck_718_ = (!leanh::lean_is_exclusive(v___x_705_)) as u8;
                        if v_isSharedCheck_718_ == 0 {
                            v___x_708_ = v___x_705_;
                            v_isShared_709_ = v_isSharedCheck_718_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_706_);
                            leanh::lean_dec(v___x_705_);
                            v___x_708_ = leanh::lean_box(0);
                            v_isShared_709_ = v_isSharedCheck_718_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_719_ = leanh::lean_ctor_get(v___x_705_, 0);
                        v_isSharedCheck_726_ = (!leanh::lean_is_exclusive(v___x_705_)) as u8;
                        if v_isSharedCheck_726_ == 0 {
                            v___x_721_ = v___x_705_;
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_719_);
                            leanh::lean_dec(v___x_705_);
                            v___x_721_ = leanh::lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_710_ = leanh::lean_ctor_get(v_a_706_, 0);
                leanh::lean_inc(v_fst_710_);
                leanh::lean_dec(v_a_706_);
                if leanh::lean_obj_tag(v_fst_710_) == 0 {
                    if v_isShared_709_ == 0 {
                        leanh::lean_ctor_set(v___x_708_, 0, v___x_703_);
                        v___x_712_ = v___x_708_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_713_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_703_);
                        v___x_712_ = v_reuseFailAlloc_713_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_714_ = leanh::lean_ctor_get(v_fst_710_, 0);
                    leanh::lean_inc(v_val_714_);
                    leanh::lean_dec_ref_known(v_fst_710_, 1);
                    if v_isShared_709_ == 0 {
                        leanh::lean_ctor_set(v___x_708_, 0, v_val_714_);
                        v___x_716_ = v___x_708_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_717_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_717_, 0, v_val_714_);
                        v___x_716_ = v_reuseFailAlloc_717_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_712_;
            }
            3 => {
                return v___x_716_;
            }
            4 => {
                if v_isShared_722_ == 0 {
                    v___x_724_ = v___x_721_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_725_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
                    v___x_724_ = v_reuseFailAlloc_725_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_724_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f___redArg___boxed(
    mut v_m_727_: *mut leanh::LeanObject,
    mut v_e_728_: *mut leanh::LeanObject,
    mut v_a_729_: *mut leanh::LeanObject,
    mut v_a_730_: *mut leanh::LeanObject,
    mut v_a_731_: *mut leanh::LeanObject,
    mut v_a_732_: *mut leanh::LeanObject,
    mut v_a_733_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
        v_m_727_, v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
    );
    leanh::lean_dec(v_a_732_);
    leanh::lean_dec_ref(v_a_731_);
    leanh::lean_dec(v_a_730_);
    leanh::lean_dec_ref(v_a_729_);
    leanh::lean_dec_ref(v_m_727_);
    return v_res_734_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f(
    mut v_00_u03b1_735_: *mut leanh::LeanObject,
    mut v_m_736_: *mut leanh::LeanObject,
    mut v_e_737_: *mut leanh::LeanObject,
    mut v_a_738_: *mut leanh::LeanObject,
    mut v_a_739_: *mut leanh::LeanObject,
    mut v_a_740_: *mut leanh::LeanObject,
    mut v_a_741_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_743_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
        v_m_736_, v_e_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_,
    );
    return v___x_743_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f___boxed(
    mut v_00_u03b1_744_: *mut leanh::LeanObject,
    mut v_m_745_: *mut leanh::LeanObject,
    mut v_e_746_: *mut leanh::LeanObject,
    mut v_a_747_: *mut leanh::LeanObject,
    mut v_a_748_: *mut leanh::LeanObject,
    mut v_a_749_: *mut leanh::LeanObject,
    mut v_a_750_: *mut leanh::LeanObject,
    mut v_a_751_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_752_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_752_ = l_Lean_Meta_KExprMap_find_x3f(
        v_00_u03b1_744_,
        v_m_745_,
        v_e_746_,
        v_a_747_,
        v_a_748_,
        v_a_749_,
        v_a_750_,
    );
    leanh::lean_dec(v_a_750_);
    leanh::lean_dec_ref(v_a_749_);
    leanh::lean_dec(v_a_748_);
    leanh::lean_dec_ref(v_a_747_);
    leanh::lean_dec_ref(v_m_745_);
    return v_res_752_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(
    mut v_00_u03b2_753_: *mut leanh::LeanObject,
    mut v_x_754_: *mut leanh::LeanObject,
    mut v_x_755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_756_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
            v_x_754_, v_x_755_,
        );
    return v___x_756_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(
    mut v_00_u03b2_757_: *mut leanh::LeanObject,
    mut v_x_758_: *mut leanh::LeanObject,
    mut v_x_759_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(
        v_00_u03b2_757_,
        v_x_758_,
        v_x_759_,
    );
    leanh::lean_dec(v_x_759_);
    leanh::lean_dec_ref(v_x_758_);
    return v_res_760_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(
    mut v_00_u03b1_761_: *mut leanh::LeanObject,
    mut v_e_762_: *mut leanh::LeanObject,
    mut v_x_763_: *mut leanh::LeanObject,
    mut v_x_764_: *mut leanh::LeanObject,
    mut v___y_765_: *mut leanh::LeanObject,
    mut v___y_766_: *mut leanh::LeanObject,
    mut v___y_767_: *mut leanh::LeanObject,
    mut v___y_768_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_770_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_770_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_762_, v_x_763_, v_x_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
    return v___x_770_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(
    mut v_00_u03b1_771_: *mut leanh::LeanObject,
    mut v_e_772_: *mut leanh::LeanObject,
    mut v_x_773_: *mut leanh::LeanObject,
    mut v_x_774_: *mut leanh::LeanObject,
    mut v___y_775_: *mut leanh::LeanObject,
    mut v___y_776_: *mut leanh::LeanObject,
    mut v___y_777_: *mut leanh::LeanObject,
    mut v___y_778_: *mut leanh::LeanObject,
    mut v___y_779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_780_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_780_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_771_, v_e_772_, v_x_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
    leanh::lean_dec(v___y_778_);
    leanh::lean_dec_ref(v___y_777_);
    leanh::lean_dec(v___y_776_);
    leanh::lean_dec_ref(v___y_775_);
    return v_res_780_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(
    mut v_00_u03b2_781_: *mut leanh::LeanObject,
    mut v_x_782_: *mut leanh::LeanObject,
    mut v_x_783_: usize,
    mut v_x_784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_785_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_782_, v_x_783_, v_x_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_786_: *mut leanh::LeanObject,
    mut v_x_787_: *mut leanh::LeanObject,
    mut v_x_788_: *mut leanh::LeanObject,
    mut v_x_789_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1712__boxed_790_: usize = 0;
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1712__boxed_790_ = leanh::lean_unbox_usize(v_x_788_);
    leanh::lean_dec(v_x_788_);
    v_res_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_786_, v_x_787_, v_x_1712__boxed_790_, v_x_789_);
    leanh::lean_dec(v_x_789_);
    leanh::lean_dec_ref(v_x_787_);
    return v_res_791_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_792_: *mut leanh::LeanObject,
    mut v_keys_793_: *mut leanh::LeanObject,
    mut v_vals_794_: *mut leanh::LeanObject,
    mut v_heq_795_: *mut leanh::LeanObject,
    mut v_i_796_: *mut leanh::LeanObject,
    mut v_k_797_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_798_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_793_, v_vals_794_, v_i_796_, v_k_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_799_: *mut leanh::LeanObject,
    mut v_keys_800_: *mut leanh::LeanObject,
    mut v_vals_801_: *mut leanh::LeanObject,
    mut v_heq_802_: *mut leanh::LeanObject,
    mut v_i_803_: *mut leanh::LeanObject,
    mut v_k_804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_799_, v_keys_800_, v_vals_801_, v_heq_802_, v_i_803_, v_k_804_);
    leanh::lean_dec(v_k_804_);
    leanh::lean_dec_ref(v_vals_801_);
    leanh::lean_dec_ref(v_keys_800_);
    return v_res_805_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
    mut v_ps_806_: *mut leanh::LeanObject,
    mut v_e_807_: *mut leanh::LeanObject,
    mut v_v_808_: *mut leanh::LeanObject,
    mut v_a_809_: *mut leanh::LeanObject,
    mut v_a_810_: *mut leanh::LeanObject,
    mut v_a_811_: *mut leanh::LeanObject,
    mut v_a_812_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v___x_822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v___x_834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut v_a_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_ps_806_) == 0 {
                    v___x_814_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_814_, 0, v_e_807_);
                    leanh::lean_ctor_set(v___x_814_, 1, v_v_808_);
                    leanh::lean_ctor_set(v___x_814_, 2, v_ps_806_);
                    v___x_815_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_815_, 0, v___x_814_);
                    return v___x_815_;
                } else {
                    v_key_816_ = leanh::lean_ctor_get(v_ps_806_, 0);
                    v_value_817_ = leanh::lean_ctor_get(v_ps_806_, 1);
                    v_tail_818_ = leanh::lean_ctor_get(v_ps_806_, 2);
                    v_isSharedCheck_855_ = (!leanh::lean_is_exclusive(v_ps_806_)) as u8;
                    if v_isSharedCheck_855_ == 0 {
                        v___x_820_ = v_ps_806_;
                        v_isShared_821_ = v_isSharedCheck_855_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_818_);
                        leanh::lean_inc(v_value_817_);
                        leanh::lean_inc(v_key_816_);
                        leanh::lean_dec(v_ps_806_);
                        v___x_820_ = leanh::lean_box(0);
                        v_isShared_821_ = v_isSharedCheck_855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc(v_key_816_);
                leanh::lean_inc_ref(v_e_807_);
                v___x_822_ = l_Lean_Meta_isExprDefEq(
                    v_e_807_, v_key_816_, v_a_809_, v_a_810_, v_a_811_, v_a_812_,
                );
                if leanh::lean_obj_tag(v___x_822_) == 0 {
                    v_a_823_ = leanh::lean_ctor_get(v___x_822_, 0);
                    v_isSharedCheck_846_ = (!leanh::lean_is_exclusive(v___x_822_)) as u8;
                    if v_isSharedCheck_846_ == 0 {
                        v___x_825_ = v___x_822_;
                        v_isShared_826_ = v_isSharedCheck_846_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_823_);
                        leanh::lean_dec(v___x_822_);
                        v___x_825_ = leanh::lean_box(0);
                        v_isShared_826_ = v_isSharedCheck_846_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_820_);
                    leanh::lean_dec(v_tail_818_);
                    leanh::lean_dec(v_value_817_);
                    leanh::lean_dec(v_key_816_);
                    leanh::lean_dec(v_v_808_);
                    leanh::lean_dec_ref(v_e_807_);
                    v_a_847_ = leanh::lean_ctor_get(v___x_822_, 0);
                    v_isSharedCheck_854_ = (!leanh::lean_is_exclusive(v___x_822_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_849_ = v___x_822_;
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_847_);
                        leanh::lean_dec(v___x_822_);
                        v___x_849_ = leanh::lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_827_ = (leanh::lean_unbox(v_a_823_) as u8);
                leanh::lean_dec(v_a_823_);
                if v___x_827_ == 0 {
                    leanh::lean_del_object(v___x_825_);
                    v___x_828_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
                        v_tail_818_,
                        v_e_807_,
                        v_v_808_,
                        v_a_809_,
                        v_a_810_,
                        v_a_811_,
                        v_a_812_,
                    );
                    if leanh::lean_obj_tag(v___x_828_) == 0 {
                        v_a_829_ = leanh::lean_ctor_get(v___x_828_, 0);
                        v_isSharedCheck_839_ = (!leanh::lean_is_exclusive(v___x_828_)) as u8;
                        if v_isSharedCheck_839_ == 0 {
                            v___x_831_ = v___x_828_;
                            v_isShared_832_ = v_isSharedCheck_839_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_829_);
                            leanh::lean_dec(v___x_828_);
                            v___x_831_ = leanh::lean_box(0);
                            v_isShared_832_ = v_isSharedCheck_839_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_820_);
                        leanh::lean_dec(v_value_817_);
                        leanh::lean_dec(v_key_816_);
                        return v___x_828_;
                    }
                } else {
                    leanh::lean_dec(v_value_817_);
                    leanh::lean_dec(v_key_816_);
                    if v_isShared_821_ == 0 {
                        leanh::lean_ctor_set(v___x_820_, 1, v_v_808_);
                        leanh::lean_ctor_set(v___x_820_, 0, v_e_807_);
                        v___x_841_ = v___x_820_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_845_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_845_, 0, v_e_807_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_845_, 1, v_v_808_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_845_, 2, v_tail_818_);
                        v___x_841_ = v_reuseFailAlloc_845_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_821_ == 0 {
                    leanh::lean_ctor_set(v___x_820_, 2, v_a_829_);
                    v___x_834_ = v___x_820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_838_, 0, v_key_816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_838_, 1, v_value_817_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_838_, 2, v_a_829_);
                    v___x_834_ = v_reuseFailAlloc_838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_832_ == 0 {
                    leanh::lean_ctor_set(v___x_831_, 0, v___x_834_);
                    v___x_836_ = v___x_831_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_837_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
                    v___x_836_ = v_reuseFailAlloc_837_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_836_;
            }
            6 => {
                if v_isShared_826_ == 0 {
                    leanh::lean_ctor_set(v___x_825_, 0, v___x_841_);
                    v___x_843_ = v___x_825_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
                    v___x_843_ = v_reuseFailAlloc_844_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_843_;
            }
            8 => {
                if v_isShared_850_ == 0 {
                    v___x_852_ = v___x_849_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_853_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
                    v___x_852_ = v_reuseFailAlloc_853_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_852_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg___boxed(
    mut v_ps_856_: *mut leanh::LeanObject,
    mut v_e_857_: *mut leanh::LeanObject,
    mut v_v_858_: *mut leanh::LeanObject,
    mut v_a_859_: *mut leanh::LeanObject,
    mut v_a_860_: *mut leanh::LeanObject,
    mut v_a_861_: *mut leanh::LeanObject,
    mut v_a_862_: *mut leanh::LeanObject,
    mut v_a_863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_864_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
        v_ps_856_, v_e_857_, v_v_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_,
    );
    leanh::lean_dec(v_a_862_);
    leanh::lean_dec_ref(v_a_861_);
    leanh::lean_dec(v_a_860_);
    leanh::lean_dec_ref(v_a_859_);
    return v_res_864_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(
    mut v_00_u03b1_865_: *mut leanh::LeanObject,
    mut v_ps_866_: *mut leanh::LeanObject,
    mut v_e_867_: *mut leanh::LeanObject,
    mut v_v_868_: *mut leanh::LeanObject,
    mut v_a_869_: *mut leanh::LeanObject,
    mut v_a_870_: *mut leanh::LeanObject,
    mut v_a_871_: *mut leanh::LeanObject,
    mut v_a_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_874_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
        v_ps_866_, v_e_867_, v_v_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_,
    );
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(
    mut v_00_u03b1_875_: *mut leanh::LeanObject,
    mut v_ps_876_: *mut leanh::LeanObject,
    mut v_e_877_: *mut leanh::LeanObject,
    mut v_v_878_: *mut leanh::LeanObject,
    mut v_a_879_: *mut leanh::LeanObject,
    mut v_a_880_: *mut leanh::LeanObject,
    mut v_a_881_: *mut leanh::LeanObject,
    mut v_a_882_: *mut leanh::LeanObject,
    mut v_a_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_884_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(
        v_00_u03b1_875_,
        v_ps_876_,
        v_e_877_,
        v_v_878_,
        v_a_879_,
        v_a_880_,
        v_a_881_,
        v_a_882_,
    );
    leanh::lean_dec(v_a_882_);
    leanh::lean_dec_ref(v_a_881_);
    leanh::lean_dec(v_a_880_);
    leanh::lean_dec_ref(v_a_879_);
    return v_res_884_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_885_: *mut leanh::LeanObject,
    mut v_x_886_: *mut leanh::LeanObject,
    mut v_x_887_: *mut leanh::LeanObject,
    mut v_x_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_889_ = leanh::lean_ctor_get(v_x_885_, 0);
                v_vs_890_ = leanh::lean_ctor_get(v_x_885_, 1);
                v_isSharedCheck_914_ = (!leanh::lean_is_exclusive(v_x_885_)) as u8;
                if v_isSharedCheck_914_ == 0 {
                    v___x_892_ = v_x_885_;
                    v_isShared_893_ = v_isSharedCheck_914_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_890_);
                    leanh::lean_inc(v_ks_889_);
                    leanh::lean_dec(v_x_885_);
                    v___x_892_ = leanh::lean_box(0);
                    v_isShared_893_ = v_isSharedCheck_914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_894_ = lean_array_get_size(v_ks_889_);
                v___x_895_ = lean_nat_dec_lt(v_x_886_, v___x_894_);
                if v___x_895_ == 0 {
                    leanh::lean_dec(v_x_886_);
                    v___x_896_ = lean_array_push(v_ks_889_, v_x_887_);
                    v___x_897_ = lean_array_push(v_vs_890_, v_x_888_);
                    if v_isShared_893_ == 0 {
                        leanh::lean_ctor_set(v___x_892_, 1, v___x_897_);
                        leanh::lean_ctor_set(v___x_892_, 0, v___x_896_);
                        v___x_899_ = v___x_892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_896_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
                        v___x_899_ = v_reuseFailAlloc_900_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_901_ = lean_array_fget_borrowed(v_ks_889_, v_x_886_);
                    v___x_902_ = l_Lean_instBEqHeadIndex_beq(v_x_887_, v_k_x27_901_);
                    if v___x_902_ == 0 {
                        if v_isShared_893_ == 0 {
                            v___x_904_ = v___x_892_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_908_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_908_, 0, v_ks_889_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_908_, 1, v_vs_890_);
                            v___x_904_ = v_reuseFailAlloc_908_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_909_ = lean_array_fset(v_ks_889_, v_x_886_, v_x_887_);
                        v___x_910_ = lean_array_fset(v_vs_890_, v_x_886_, v_x_888_);
                        leanh::lean_dec(v_x_886_);
                        if v_isShared_893_ == 0 {
                            leanh::lean_ctor_set(v___x_892_, 1, v___x_910_);
                            leanh::lean_ctor_set(v___x_892_, 0, v___x_909_);
                            v___x_912_ = v___x_892_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_913_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_909_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
                            v___x_912_ = v_reuseFailAlloc_913_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_899_;
            }
            3 => {
                v___x_905_ = leanh::lean_unsigned_to_nat(1);
                v___x_906_ = lean_nat_add(v_x_886_, v___x_905_);
                leanh::lean_dec(v_x_886_);
                v_x_885_ = v___x_904_;
                v_x_886_ = v___x_906_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_912_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(
    mut v_n_915_: *mut leanh::LeanObject,
    mut v_k_916_: *mut leanh::LeanObject,
    mut v_v_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = leanh::lean_unsigned_to_nat(0);
    v___x_919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_915_, v___x_918_, v_k_916_, v_v_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_920_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_920_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(
    mut v_x_921_: *mut leanh::LeanObject,
    mut v_x_922_: usize,
    mut v_x_923_: usize,
    mut v_x_924_: *mut leanh::LeanObject,
    mut v_x_925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: usize = 0;
    let mut v___x_928_: usize = 0;
    let mut v___x_929_: usize = 0;
    let mut v___x_930_: usize = 0;
    let mut v_j_931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v_v_937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_950_: u8 = 0;
    let mut v___x_951_: u8 = 0;
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_node_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut v___x_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_unused_971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_981_: u8 = 0;
    let mut v_ks_982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut v_reuseFailAlloc_992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_921_) == 0 {
                    v_es_926_ = leanh::lean_ctor_get(v_x_921_, 0);
                    v___x_927_ = 5usize;
                    v___x_928_ = 1usize;
                    v___x_929_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_930_ = lean_usize_land(v_x_922_, v___x_929_);
                    v_j_931_ = lean_usize_to_nat(v___x_930_);
                    v___x_932_ = lean_array_get_size(v_es_926_);
                    v___x_933_ = lean_nat_dec_lt(v_j_931_, v___x_932_);
                    if v___x_933_ == 0 {
                        leanh::lean_dec(v_j_931_);
                        leanh::lean_dec(v_x_925_);
                        leanh::lean_dec(v_x_924_);
                        return v_x_921_;
                    } else {
                        leanh::lean_inc_ref(v_es_926_);
                        v_isSharedCheck_970_ = (!leanh::lean_is_exclusive(v_x_921_)) as u8;
                        if v_isSharedCheck_970_ == 0 {
                            v_unused_971_ = leanh::lean_ctor_get(v_x_921_, 0);
                            leanh::lean_dec(v_unused_971_);
                            v___x_935_ = v_x_921_;
                            v_isShared_936_ = v_isSharedCheck_970_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_921_);
                            v___x_935_ = leanh::lean_box(0);
                            v_isShared_936_ = v_isSharedCheck_970_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_972_ = leanh::lean_ctor_get(v_x_921_, 0);
                    v_vs_973_ = leanh::lean_ctor_get(v_x_921_, 1);
                    v_isSharedCheck_993_ = (!leanh::lean_is_exclusive(v_x_921_)) as u8;
                    if v_isSharedCheck_993_ == 0 {
                        v___x_975_ = v_x_921_;
                        v_isShared_976_ = v_isSharedCheck_993_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_973_);
                        leanh::lean_inc(v_ks_972_);
                        leanh::lean_dec(v_x_921_);
                        v___x_975_ = leanh::lean_box(0);
                        v_isShared_976_ = v_isSharedCheck_993_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_937_ = lean_array_fget(v_es_926_, v_j_931_);
                v___x_938_ = leanh::lean_box(0);
                v_xs_x27_939_ = lean_array_fset(v_es_926_, v_j_931_, v___x_938_);
                match leanh::lean_obj_tag(v_v_937_) {
                    0 => {
                        v_key_946_ = leanh::lean_ctor_get(v_v_937_, 0);
                        v_val_947_ = leanh::lean_ctor_get(v_v_937_, 1);
                        v_isSharedCheck_957_ = (!leanh::lean_is_exclusive(v_v_937_)) as u8;
                        if v_isSharedCheck_957_ == 0 {
                            v___x_949_ = v_v_937_;
                            v_isShared_950_ = v_isSharedCheck_957_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_947_);
                            leanh::lean_inc(v_key_946_);
                            leanh::lean_dec(v_v_937_);
                            v___x_949_ = leanh::lean_box(0);
                            v_isShared_950_ = v_isSharedCheck_957_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_958_ = leanh::lean_ctor_get(v_v_937_, 0);
                        v_isSharedCheck_968_ = (!leanh::lean_is_exclusive(v_v_937_)) as u8;
                        if v_isSharedCheck_968_ == 0 {
                            v___x_960_ = v_v_937_;
                            v_isShared_961_ = v_isSharedCheck_968_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_958_);
                            leanh::lean_dec(v_v_937_);
                            v___x_960_ = leanh::lean_box(0);
                            v_isShared_961_ = v_isSharedCheck_968_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_969_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_969_, 0, v_x_924_);
                        leanh::lean_ctor_set(v___x_969_, 1, v_x_925_);
                        v___y_941_ = v___x_969_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_942_ = lean_array_fset(v_xs_x27_939_, v_j_931_, v___y_941_);
                leanh::lean_dec(v_j_931_);
                if v_isShared_936_ == 0 {
                    leanh::lean_ctor_set(v___x_935_, 0, v___x_942_);
                    v___x_944_ = v___x_935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_945_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
                    v___x_944_ = v_reuseFailAlloc_945_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_944_;
            }
            4 => {
                v___x_951_ = l_Lean_instBEqHeadIndex_beq(v_x_924_, v_key_946_);
                if v___x_951_ == 0 {
                    leanh::lean_del_object(v___x_949_);
                    v___x_952_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_946_, v_val_947_, v_x_924_, v_x_925_,
                    );
                    v___x_953_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_953_, 0, v___x_952_);
                    v___y_941_ = v___x_953_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_947_);
                    leanh::lean_dec(v_key_946_);
                    if v_isShared_950_ == 0 {
                        leanh::lean_ctor_set(v___x_949_, 1, v_x_925_);
                        leanh::lean_ctor_set(v___x_949_, 0, v_x_924_);
                        v___x_955_ = v___x_949_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_956_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_956_, 0, v_x_924_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_956_, 1, v_x_925_);
                        v___x_955_ = v_reuseFailAlloc_956_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_941_ = v___x_955_;
                state = 2;
                continue;
            }
            6 => {
                v___x_962_ = lean_usize_shift_right(v_x_922_, v___x_927_);
                v___x_963_ = lean_usize_add(v_x_923_, v___x_928_);
                v___x_964_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_node_958_, v___x_962_, v___x_963_, v_x_924_, v_x_925_);
                if v_isShared_961_ == 0 {
                    leanh::lean_ctor_set(v___x_960_, 0, v___x_964_);
                    v___x_966_ = v___x_960_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_967_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
                    v___x_966_ = v_reuseFailAlloc_967_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_941_ = v___x_966_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_976_ == 0 {
                    v___x_978_ = v___x_975_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_992_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_992_, 0, v_ks_972_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_992_, 1, v_vs_973_);
                    v___x_978_ = v_reuseFailAlloc_992_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_979_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v___x_978_, v_x_924_, v_x_925_);
                v___x_987_ = 7usize;
                v___x_988_ = lean_usize_dec_le(v___x_987_, v_x_923_);
                if v___x_988_ == 0 {
                    v___x_989_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_979_);
                    v___x_990_ = leanh::lean_unsigned_to_nat(4);
                    v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
                    leanh::lean_dec(v___x_989_);
                    v___y_981_ = v___x_991_;
                    state = 10;
                    continue;
                } else {
                    v___y_981_ = v___x_988_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_981_ == 0 {
                    v_ks_982_ = leanh::lean_ctor_get(v_newNode_979_, 0);
                    leanh::lean_inc_ref(v_ks_982_);
                    v_vs_983_ = leanh::lean_ctor_get(v_newNode_979_, 1);
                    leanh::lean_inc_ref(v_vs_983_);
                    leanh::lean_dec_ref(v_newNode_979_);
                    v___x_984_ = leanh::lean_unsigned_to_nat(0);
                    v___x_985_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
                    v___x_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_923_, v_ks_982_, v_vs_983_, v___x_984_, v___x_985_);
                    leanh::lean_dec_ref(v_vs_983_);
                    leanh::lean_dec_ref(v_ks_982_);
                    return v___x_986_;
                } else {
                    return v_newNode_979_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(
    mut v_depth_994_: usize,
    mut v_keys_995_: *mut leanh::LeanObject,
    mut v_vals_996_: *mut leanh::LeanObject,
    mut v_i_997_: *mut leanh::LeanObject,
    mut v_entries_998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v_k_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u64 = 0;
    let mut v_h_1004_: usize = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: usize = 0;
    let mut v_h_1010_: usize = 0;
    let mut v___x_1011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_keys_995_);
                v___x_1000_ = lean_nat_dec_lt(v_i_997_, v___x_999_);
                if v___x_1000_ == 0 {
                    leanh::lean_dec(v_i_997_);
                    return v_entries_998_;
                } else {
                    v_k_1001_ = lean_array_fget_borrowed(v_keys_995_, v_i_997_);
                    v_v_1002_ = lean_array_fget_borrowed(v_vals_996_, v_i_997_);
                    v___x_1003_ = l_Lean_HeadIndex_hash(v_k_1001_);
                    v_h_1004_ = lean_uint64_to_usize(v___x_1003_);
                    v___x_1005_ = 5usize;
                    v___x_1006_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1007_ = 1usize;
                    v___x_1008_ = lean_usize_sub(v_depth_994_, v___x_1007_);
                    v___x_1009_ = lean_usize_mul(v___x_1005_, v___x_1008_);
                    v_h_1010_ = lean_usize_shift_right(v_h_1004_, v___x_1009_);
                    v___x_1011_ = lean_nat_add(v_i_997_, v___x_1006_);
                    leanh::lean_dec(v_i_997_);
                    leanh::lean_inc(v_v_1002_);
                    leanh::lean_inc(v_k_1001_);
                    v___x_1012_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_entries_998_, v_h_1010_, v_depth_994_, v_k_1001_, v_v_1002_);
                    v_i_997_ = v___x_1011_;
                    v_entries_998_ = v___x_1012_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_1014_: *mut leanh::LeanObject,
    mut v_keys_1015_: *mut leanh::LeanObject,
    mut v_vals_1016_: *mut leanh::LeanObject,
    mut v_i_1017_: *mut leanh::LeanObject,
    mut v_entries_1018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1019_: usize = 0;
    let mut v_res_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1019_ = leanh::lean_unbox_usize(v_depth_1014_);
    leanh::lean_dec(v_depth_1014_);
    v_res_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1019_, v_keys_1015_, v_vals_1016_, v_i_1017_, v_entries_1018_);
    leanh::lean_dec_ref(v_vals_1016_);
    leanh::lean_dec_ref(v_keys_1015_);
    return v_res_1020_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_1021_: *mut leanh::LeanObject,
    mut v_x_1022_: *mut leanh::LeanObject,
    mut v_x_1023_: *mut leanh::LeanObject,
    mut v_x_1024_: *mut leanh::LeanObject,
    mut v_x_1025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_737__boxed_1026_: usize = 0;
    let mut v_x_738__boxed_1027_: usize = 0;
    let mut v_res_1028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_737__boxed_1026_ = leanh::lean_unbox_usize(v_x_1022_);
    leanh::lean_dec(v_x_1022_);
    v_x_738__boxed_1027_ = leanh::lean_unbox_usize(v_x_1023_);
    leanh::lean_dec(v_x_1023_);
    v_res_1028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1021_, v_x_737__boxed_1026_, v_x_738__boxed_1027_, v_x_1024_, v_x_1025_);
    return v_res_1028_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(
    mut v_x_1029_: *mut leanh::LeanObject,
    mut v_x_1030_: *mut leanh::LeanObject,
    mut v_x_1031_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1032_: u64 = 0;
    let mut v___x_1033_: usize = 0;
    let mut v___x_1034_: usize = 0;
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_HeadIndex_hash(v_x_1030_);
    v___x_1033_ = lean_uint64_to_usize(v___x_1032_);
    v___x_1034_ = 1usize;
    v___x_1035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1029_, v___x_1033_, v___x_1034_, v_x_1030_, v_x_1031_);
    return v___x_1035_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert___redArg(
    mut v_m_1036_: *mut leanh::LeanObject,
    mut v_e_1037_: *mut leanh::LeanObject,
    mut v_v_1038_: *mut leanh::LeanObject,
    mut v_a_1039_: *mut leanh::LeanObject,
    mut v_a_1040_: *mut leanh::LeanObject,
    mut v_a_1041_: *mut leanh::LeanObject,
    mut v_a_1042_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_k_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_e_1037_);
                v_k_1044_ = l_Lean_Expr_toHeadIndex(v_e_1037_);
                v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_1036_, v_k_1044_);
                if leanh::lean_obj_tag(v___x_1045_) == 0 {
                    v___x_1046_ = leanh::lean_box(0);
                    v___x_1047_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_1047_, 0, v_e_1037_);
                    leanh::lean_ctor_set(v___x_1047_, 1, v_v_1038_);
                    leanh::lean_ctor_set(v___x_1047_, 2, v___x_1046_);
                    v___x_1048_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_1036_, v_k_1044_, v___x_1047_);
                    v___x_1049_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1049_, 0, v___x_1048_);
                    return v___x_1049_;
                } else {
                    v_val_1050_ = leanh::lean_ctor_get(v___x_1045_, 0);
                    leanh::lean_inc(v_val_1050_);
                    leanh::lean_dec_ref_known(v___x_1045_, 1);
                    v___x_1051_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
                        v_val_1050_,
                        v_e_1037_,
                        v_v_1038_,
                        v_a_1039_,
                        v_a_1040_,
                        v_a_1041_,
                        v_a_1042_,
                    );
                    if leanh::lean_obj_tag(v___x_1051_) == 0 {
                        v_a_1052_ = leanh::lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1060_ =
                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v___x_1054_ = v___x_1051_;
                            v_isShared_1055_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1052_);
                            leanh::lean_dec(v___x_1051_);
                            v___x_1054_ = leanh::lean_box(0);
                            v_isShared_1055_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_k_1044_);
                        leanh::lean_dec_ref(v_m_1036_);
                        v_a_1061_ = leanh::lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1068_ =
                            (!leanh::lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1068_ == 0 {
                            v___x_1063_ = v___x_1051_;
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_1061_);
                            leanh::lean_dec(v___x_1051_);
                            v___x_1063_ = leanh::lean_box(0);
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_1056_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_1036_, v_k_1044_, v_a_1052_);
                if v_isShared_1055_ == 0 {
                    leanh::lean_ctor_set(v___x_1054_, 0, v___x_1056_);
                    v___x_1058_ = v___x_1054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
                    v___x_1058_ = v_reuseFailAlloc_1059_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1058_;
            }
            3 => {
                if v_isShared_1064_ == 0 {
                    v___x_1066_ = v___x_1063_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1067_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
                    v___x_1066_ = v_reuseFailAlloc_1067_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1066_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_KExprMap_insert___redArg___boxed(
    mut v_m_1069_: *mut leanh::LeanObject,
    mut v_e_1070_: *mut leanh::LeanObject,
    mut v_v_1071_: *mut leanh::LeanObject,
    mut v_a_1072_: *mut leanh::LeanObject,
    mut v_a_1073_: *mut leanh::LeanObject,
    mut v_a_1074_: *mut leanh::LeanObject,
    mut v_a_1075_: *mut leanh::LeanObject,
    mut v_a_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Lean_Meta_KExprMap_insert___redArg(
        v_m_1069_, v_e_1070_, v_v_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_,
    );
    leanh::lean_dec(v_a_1075_);
    leanh::lean_dec_ref(v_a_1074_);
    leanh::lean_dec(v_a_1073_);
    leanh::lean_dec_ref(v_a_1072_);
    return v_res_1077_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert(
    mut v_00_u03b1_1078_: *mut leanh::LeanObject,
    mut v_m_1079_: *mut leanh::LeanObject,
    mut v_e_1080_: *mut leanh::LeanObject,
    mut v_v_1081_: *mut leanh::LeanObject,
    mut v_a_1082_: *mut leanh::LeanObject,
    mut v_a_1083_: *mut leanh::LeanObject,
    mut v_a_1084_: *mut leanh::LeanObject,
    mut v_a_1085_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_Lean_Meta_KExprMap_insert___redArg(
        v_m_1079_, v_e_1080_, v_v_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_,
    );
    return v___x_1087_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert___boxed(
    mut v_00_u03b1_1088_: *mut leanh::LeanObject,
    mut v_m_1089_: *mut leanh::LeanObject,
    mut v_e_1090_: *mut leanh::LeanObject,
    mut v_v_1091_: *mut leanh::LeanObject,
    mut v_a_1092_: *mut leanh::LeanObject,
    mut v_a_1093_: *mut leanh::LeanObject,
    mut v_a_1094_: *mut leanh::LeanObject,
    mut v_a_1095_: *mut leanh::LeanObject,
    mut v_a_1096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1097_ = l_Lean_Meta_KExprMap_insert(
        v_00_u03b1_1088_,
        v_m_1089_,
        v_e_1090_,
        v_v_1091_,
        v_a_1092_,
        v_a_1093_,
        v_a_1094_,
        v_a_1095_,
    );
    leanh::lean_dec(v_a_1095_);
    leanh::lean_dec_ref(v_a_1094_);
    leanh::lean_dec(v_a_1093_);
    leanh::lean_dec_ref(v_a_1092_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(
    mut v_00_u03b2_1098_: *mut leanh::LeanObject,
    mut v_x_1099_: *mut leanh::LeanObject,
    mut v_x_1100_: *mut leanh::LeanObject,
    mut v_x_1101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1102_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(
            v_x_1099_, v_x_1100_, v_x_1101_,
        );
    return v___x_1102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(
    mut v_00_u03b2_1103_: *mut leanh::LeanObject,
    mut v_x_1104_: *mut leanh::LeanObject,
    mut v_x_1105_: usize,
    mut v_x_1106_: usize,
    mut v_x_1107_: *mut leanh::LeanObject,
    mut v_x_1108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1104_, v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
    return v___x_1109_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_1110_: *mut leanh::LeanObject,
    mut v_x_1111_: *mut leanh::LeanObject,
    mut v_x_1112_: *mut leanh::LeanObject,
    mut v_x_1113_: *mut leanh::LeanObject,
    mut v_x_1114_: *mut leanh::LeanObject,
    mut v_x_1115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_971__boxed_1116_: usize = 0;
    let mut v_x_972__boxed_1117_: usize = 0;
    let mut v_res_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_971__boxed_1116_ = leanh::lean_unbox_usize(v_x_1112_);
    leanh::lean_dec(v_x_1112_);
    v_x_972__boxed_1117_ = leanh::lean_unbox_usize(v_x_1113_);
    leanh::lean_dec(v_x_1113_);
    v_res_1118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_1110_, v_x_1111_, v_x_971__boxed_1116_, v_x_972__boxed_1117_, v_x_1114_, v_x_1115_);
    return v_res_1118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1119_: *mut leanh::LeanObject,
    mut v_n_1120_: *mut leanh::LeanObject,
    mut v_k_1121_: *mut leanh::LeanObject,
    mut v_v_1122_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_1120_, v_k_1121_, v_v_1122_);
    return v___x_1123_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1124_: *mut leanh::LeanObject,
    mut v_depth_1125_: usize,
    mut v_keys_1126_: *mut leanh::LeanObject,
    mut v_vals_1127_: *mut leanh::LeanObject,
    mut v_heq_1128_: *mut leanh::LeanObject,
    mut v_i_1129_: *mut leanh::LeanObject,
    mut v_entries_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_1125_, v_keys_1126_, v_vals_1127_, v_i_1129_, v_entries_1130_);
    return v___x_1131_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1132_: *mut leanh::LeanObject,
    mut v_depth_1133_: *mut leanh::LeanObject,
    mut v_keys_1134_: *mut leanh::LeanObject,
    mut v_vals_1135_: *mut leanh::LeanObject,
    mut v_heq_1136_: *mut leanh::LeanObject,
    mut v_i_1137_: *mut leanh::LeanObject,
    mut v_entries_1138_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_1139_: usize = 0;
    let mut v_res_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_1139_ = leanh::lean_unbox_usize(v_depth_1133_);
    leanh::lean_dec(v_depth_1133_);
    v_res_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_1132_, v_depth_boxed_1139_, v_keys_1134_, v_vals_1135_, v_heq_1136_, v_i_1137_, v_entries_1138_);
    leanh::lean_dec_ref(v_vals_1135_);
    leanh::lean_dec_ref(v_keys_1134_);
    return v_res_1140_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1141_: *mut leanh::LeanObject,
    mut v_x_1142_: *mut leanh::LeanObject,
    mut v_x_1143_: *mut leanh::LeanObject,
    mut v_x_1144_: *mut leanh::LeanObject,
    mut v_x_1145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1142_, v_x_1143_, v_x_1144_, v_x_1145_);
    return v___x_1146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_AssocList(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_HeadIndex(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KExprMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_KExprMap(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_KExprMap(builtin);
}
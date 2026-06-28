// Lean compiler output
// Module: Lean.Meta.KExprMap
// Imports: Lean.Data.AssocList Lean.HeadIndex Lean.Meta.Basic
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
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_to_usize, lean_usize_land, lean_usize_mul, lean_usize_shift_left,
    lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_lt,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_set,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_instInhabitedKExprMap_default___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_instInhabitedKExprMap___closed__0_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_instInhabitedKExprMap___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
pub static l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0_value) as *mut LeanObject;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0() -> *mut LeanObject {
    let mut v___x_574_: *mut LeanObject = core::ptr::null_mut();
    v___x_574_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_574_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1() -> *mut LeanObject {
    let mut v___x_575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_576_: *mut LeanObject = core::ptr::null_mut();
    v___x_575_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__0_once),
        _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__0,
    );
    v___x_576_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_576_, 0, v___x_575_);
    return v___x_576_;
}
pub unsafe fn l_Lean_Meta_instInhabitedKExprMap_default(
    mut v_00_u03b1_577_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_578_: *mut LeanObject = core::ptr::null_mut();
    v___x_578_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap_default___closed__1_once),
        _init_l_Lean_Meta_instInhabitedKExprMap_default___closed__1,
    );
    return v___x_578_;
}
pub unsafe fn _init_l_Lean_Meta_instInhabitedKExprMap___closed__0() -> *mut LeanObject {
    let mut v___x_579_: *mut LeanObject = core::ptr::null_mut();
    v___x_579_ = l_Lean_Meta_instInhabitedKExprMap_default(lean_box(0));
    return v___x_579_;
}
pub unsafe fn l_Lean_Meta_instInhabitedKExprMap(mut v_a_580_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_581_: *mut LeanObject = core::ptr::null_mut();
    v___x_581_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_instInhabitedKExprMap___closed__0_once),
        _init_l_Lean_Meta_instInhabitedKExprMap___closed__0,
    );
    return v___x_581_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_582_: *mut LeanObject,
    mut v_vals_583_: *mut LeanObject,
    mut v_i_584_: *mut LeanObject,
    mut v_k_585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_587_: u8 = 0;
    let mut v___x_588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_590_: u8 = 0;
    let mut v___x_591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_595_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_586_ = lean_array_get_size(v_keys_582_);
                v___x_587_ = lean_nat_dec_lt(v_i_584_, v___x_586_);
                if v___x_587_ == 0 {
                    lean_dec(v_i_584_);
                    v___x_588_ = lean_box(0);
                    return v___x_588_;
                } else {
                    v_k_x27_589_ = lean_array_fget_borrowed(v_keys_582_, v_i_584_);
                    v___x_590_ = l_Lean_instBEqHeadIndex_beq(v_k_585_, v_k_x27_589_);
                    if v___x_590_ == 0 {
                        v___x_591_ = lean_unsigned_to_nat(1);
                        v___x_592_ = lean_nat_add(v_i_584_, v___x_591_);
                        lean_dec(v_i_584_);
                        v_i_584_ = v___x_592_;
                        state = 0;
                        continue;
                    } else {
                        v___x_594_ = lean_array_fget_borrowed(v_vals_583_, v_i_584_);
                        lean_dec(v_i_584_);
                        lean_inc(v___x_594_);
                        v___x_595_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_595_, 0, v___x_594_);
                        return v___x_595_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_596_: *mut LeanObject,
    mut v_vals_597_: *mut LeanObject,
    mut v_i_598_: *mut LeanObject,
    mut v_k_599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_600_: *mut LeanObject = core::ptr::null_mut();
    v_res_600_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_596_, v_vals_597_, v_i_598_, v_k_599_);
    lean_dec(v_k_599_);
    lean_dec_ref(v_vals_597_);
    lean_dec_ref(v_keys_596_);
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
    v___x_605_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_606_ = lean_usize_sub(v___x_605_, v___x_604_);
    return v___x_606_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(
    mut v_x_607_: *mut LeanObject,
    mut v_x_608_: usize,
    mut v_x_609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_612_: usize = 0;
    let mut v___x_613_: usize = 0;
    let mut v___x_614_: usize = 0;
    let mut v_j_615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_619_: u8 = 0;
    let mut v___x_620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_623_: usize = 0;
    let mut v___x_625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_629_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_607_) == 0 {
                    v_es_610_ = lean_ctor_get(v_x_607_, 0);
                    v___x_611_ = lean_box(2);
                    v___x_612_ = 5usize;
                    v___x_613_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_614_ = lean_usize_land(v_x_608_, v___x_613_);
                    v_j_615_ = lean_usize_to_nat(v___x_614_);
                    v___x_616_ = lean_array_get_borrowed(v___x_611_, v_es_610_, v_j_615_);
                    lean_dec(v_j_615_);
                    match lean_obj_tag(v___x_616_) {
                        0 => {
                            v_key_617_ = lean_ctor_get(v___x_616_, 0);
                            v_val_618_ = lean_ctor_get(v___x_616_, 1);
                            v___x_619_ = l_Lean_instBEqHeadIndex_beq(v_x_609_, v_key_617_);
                            if v___x_619_ == 0 {
                                v___x_620_ = lean_box(0);
                                return v___x_620_;
                            } else {
                                lean_inc(v_val_618_);
                                v___x_621_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_621_, 0, v_val_618_);
                                return v___x_621_;
                            }
                        }
                        1 => {
                            v_node_622_ = lean_ctor_get(v___x_616_, 0);
                            v___x_623_ = lean_usize_shift_right(v_x_608_, v___x_612_);
                            v_x_607_ = v_node_622_;
                            v_x_608_ = v___x_623_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_625_ = lean_box(0);
                            return v___x_625_;
                        }
                    }
                } else {
                    v_ks_626_ = lean_ctor_get(v_x_607_, 0);
                    v_vs_627_ = lean_ctor_get(v_x_607_, 1);
                    v___x_628_ = lean_unsigned_to_nat(0);
                    v___x_629_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_ks_626_, v_vs_627_, v___x_628_, v_x_609_);
                    return v___x_629_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_630_: *mut LeanObject,
    mut v_x_631_: *mut LeanObject,
    mut v_x_632_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1462__boxed_633_: usize = 0;
    let mut v_res_634_: *mut LeanObject = core::ptr::null_mut();
    v_x_1462__boxed_633_ = lean_unbox_usize(v_x_631_);
    lean_dec(v_x_631_);
    v_res_634_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_630_, v_x_1462__boxed_633_, v_x_632_);
    lean_dec(v_x_632_);
    lean_dec_ref(v_x_630_);
    return v_res_634_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
    mut v_x_635_: *mut LeanObject,
    mut v_x_636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_637_: u64 = 0;
    let mut v___x_638_: usize = 0;
    let mut v___x_639_: *mut LeanObject = core::ptr::null_mut();
    v___x_637_ = l_Lean_HeadIndex_hash(v_x_636_);
    v___x_638_ = lean_uint64_to_usize(v___x_637_);
    v___x_639_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_635_, v___x_638_, v_x_636_);
    return v___x_639_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg___boxed(
    mut v_x_640_: *mut LeanObject,
    mut v_x_641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_642_: *mut LeanObject = core::ptr::null_mut();
    v_res_642_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
            v_x_640_, v_x_641_,
        );
    lean_dec(v_x_641_);
    lean_dec_ref(v_x_640_);
    return v_res_642_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(
    mut v_e_646_: *mut LeanObject,
    mut v_x_647_: *mut LeanObject,
    mut v_x_648_: *mut LeanObject,
    mut v___y_649_: *mut LeanObject,
    mut v___y_650_: *mut LeanObject,
    mut v___y_651_: *mut LeanObject,
    mut v___y_652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_662_: u8 = 0;
    let mut v___x_663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_664_: u8 = 0;
    let mut v___x_665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_673_: u8 = 0;
    let mut v_a_674_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_677_: u8 = 0;
    let mut v___x_679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_648_) == 0 {
                    lean_dec_ref(v_e_646_);
                    v___x_654_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_654_, 0, v_x_647_);
                    return v___x_654_;
                } else {
                    lean_dec_ref(v_x_647_);
                    v_key_655_ = lean_ctor_get(v_x_648_, 0);
                    lean_inc(v_key_655_);
                    v_value_656_ = lean_ctor_get(v_x_648_, 1);
                    lean_inc(v_value_656_);
                    v_tail_657_ = lean_ctor_get(v_x_648_, 2);
                    lean_inc(v_tail_657_);
                    lean_dec_ref_known(v_x_648_, 3);
                    lean_inc_ref(v_e_646_);
                    v___x_658_ = l_Lean_Meta_isExprDefEq(
                        v_e_646_, v_key_655_, v___y_649_, v___y_650_, v___y_651_, v___y_652_,
                    );
                    if lean_obj_tag(v___x_658_) == 0 {
                        v_a_659_ = lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_673_ = (!lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_673_ == 0 {
                            v___x_661_ = v___x_658_;
                            v_isShared_662_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_659_);
                            lean_dec(v___x_658_);
                            v___x_661_ = lean_box(0);
                            v_isShared_662_ = v_isSharedCheck_673_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_tail_657_);
                        lean_dec(v_value_656_);
                        lean_dec_ref(v_e_646_);
                        v_a_674_ = lean_ctor_get(v___x_658_, 0);
                        v_isSharedCheck_681_ = (!lean_is_exclusive(v___x_658_)) as u8;
                        if v_isSharedCheck_681_ == 0 {
                            v___x_676_ = v___x_658_;
                            v_isShared_677_ = v_isSharedCheck_681_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_674_);
                            lean_dec(v___x_658_);
                            v___x_676_ = lean_box(0);
                            v_isShared_677_ = v_isSharedCheck_681_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_663_ = lean_box(0);
                v___x_664_ = (lean_unbox(v_a_659_) as u8);
                lean_dec(v_a_659_);
                if v___x_664_ == 0 {
                    lean_del_object(v___x_661_);
                    lean_dec(v_value_656_);
                    v___x_665_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0;
                    v_x_647_ = v___x_665_;
                    v_x_648_ = v_tail_657_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_tail_657_);
                    lean_dec_ref(v_e_646_);
                    v___x_667_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_667_, 0, v_value_656_);
                    v___x_668_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_668_, 0, v___x_667_);
                    v___x_669_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_669_, 0, v___x_668_);
                    lean_ctor_set(v___x_669_, 1, v___x_663_);
                    if v_isShared_662_ == 0 {
                        lean_ctor_set(v___x_661_, 0, v___x_669_);
                        v___x_671_ = v___x_661_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_672_, 0, v___x_669_);
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
                    v_reuseFailAlloc_680_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_680_, 0, v_a_674_);
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
    mut v_e_682_: *mut LeanObject,
    mut v_x_683_: *mut LeanObject,
    mut v_x_684_: *mut LeanObject,
    mut v___y_685_: *mut LeanObject,
    mut v___y_686_: *mut LeanObject,
    mut v___y_687_: *mut LeanObject,
    mut v___y_688_: *mut LeanObject,
    mut v___y_689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_690_: *mut LeanObject = core::ptr::null_mut();
    v_res_690_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_682_, v_x_683_, v_x_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_);
    lean_dec(v___y_688_);
    lean_dec_ref(v___y_687_);
    lean_dec(v___y_686_);
    lean_dec_ref(v___y_685_);
    return v_res_690_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f___redArg(
    mut v_m_691_: *mut LeanObject,
    mut v_e_692_: *mut LeanObject,
    mut v_a_693_: *mut LeanObject,
    mut v_a_694_: *mut LeanObject,
    mut v_a_695_: *mut LeanObject,
    mut v_a_696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_702_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_709_: u8 = 0;
    let mut v_fst_710_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_718_: u8 = 0;
    let mut v_a_719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_726_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_692_);
                v___x_698_ = l_Lean_Expr_toHeadIndex(v_e_692_);
                v___x_699_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_691_, v___x_698_);
                lean_dec(v___x_698_);
                if lean_obj_tag(v___x_699_) == 0 {
                    lean_dec_ref(v_e_692_);
                    v___x_700_ = lean_box(0);
                    v___x_701_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_701_, 0, v___x_700_);
                    return v___x_701_;
                } else {
                    v_val_702_ = lean_ctor_get(v___x_699_, 0);
                    lean_inc(v_val_702_);
                    lean_dec_ref_known(v___x_699_, 1);
                    v___x_703_ = lean_box(0);
                    v___x_704_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg___closed__0;
                    v___x_705_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_692_, v___x_704_, v_val_702_, v_a_693_, v_a_694_, v_a_695_, v_a_696_);
                    if lean_obj_tag(v___x_705_) == 0 {
                        v_a_706_ = lean_ctor_get(v___x_705_, 0);
                        v_isSharedCheck_718_ = (!lean_is_exclusive(v___x_705_)) as u8;
                        if v_isSharedCheck_718_ == 0 {
                            v___x_708_ = v___x_705_;
                            v_isShared_709_ = v_isSharedCheck_718_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_706_);
                            lean_dec(v___x_705_);
                            v___x_708_ = lean_box(0);
                            v_isShared_709_ = v_isSharedCheck_718_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_719_ = lean_ctor_get(v___x_705_, 0);
                        v_isSharedCheck_726_ = (!lean_is_exclusive(v___x_705_)) as u8;
                        if v_isSharedCheck_726_ == 0 {
                            v___x_721_ = v___x_705_;
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_719_);
                            lean_dec(v___x_705_);
                            v___x_721_ = lean_box(0);
                            v_isShared_722_ = v_isSharedCheck_726_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_710_ = lean_ctor_get(v_a_706_, 0);
                lean_inc(v_fst_710_);
                lean_dec(v_a_706_);
                if lean_obj_tag(v_fst_710_) == 0 {
                    if v_isShared_709_ == 0 {
                        lean_ctor_set(v___x_708_, 0, v___x_703_);
                        v___x_712_ = v___x_708_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_713_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_713_, 0, v___x_703_);
                        v___x_712_ = v_reuseFailAlloc_713_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_714_ = lean_ctor_get(v_fst_710_, 0);
                    lean_inc(v_val_714_);
                    lean_dec_ref_known(v_fst_710_, 1);
                    if v_isShared_709_ == 0 {
                        lean_ctor_set(v___x_708_, 0, v_val_714_);
                        v___x_716_ = v___x_708_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_717_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_717_, 0, v_val_714_);
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
                    v_reuseFailAlloc_725_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_725_, 0, v_a_719_);
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
    mut v_m_727_: *mut LeanObject,
    mut v_e_728_: *mut LeanObject,
    mut v_a_729_: *mut LeanObject,
    mut v_a_730_: *mut LeanObject,
    mut v_a_731_: *mut LeanObject,
    mut v_a_732_: *mut LeanObject,
    mut v_a_733_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_734_: *mut LeanObject = core::ptr::null_mut();
    v_res_734_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
        v_m_727_, v_e_728_, v_a_729_, v_a_730_, v_a_731_, v_a_732_,
    );
    lean_dec(v_a_732_);
    lean_dec_ref(v_a_731_);
    lean_dec(v_a_730_);
    lean_dec_ref(v_a_729_);
    lean_dec_ref(v_m_727_);
    return v_res_734_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f(
    mut v_00_u03b1_735_: *mut LeanObject,
    mut v_m_736_: *mut LeanObject,
    mut v_e_737_: *mut LeanObject,
    mut v_a_738_: *mut LeanObject,
    mut v_a_739_: *mut LeanObject,
    mut v_a_740_: *mut LeanObject,
    mut v_a_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_743_: *mut LeanObject = core::ptr::null_mut();
    v___x_743_ = l_Lean_Meta_KExprMap_find_x3f___redArg(
        v_m_736_, v_e_737_, v_a_738_, v_a_739_, v_a_740_, v_a_741_,
    );
    return v___x_743_;
}
pub unsafe fn l_Lean_Meta_KExprMap_find_x3f___boxed(
    mut v_00_u03b1_744_: *mut LeanObject,
    mut v_m_745_: *mut LeanObject,
    mut v_e_746_: *mut LeanObject,
    mut v_a_747_: *mut LeanObject,
    mut v_a_748_: *mut LeanObject,
    mut v_a_749_: *mut LeanObject,
    mut v_a_750_: *mut LeanObject,
    mut v_a_751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_752_: *mut LeanObject = core::ptr::null_mut();
    v_res_752_ = l_Lean_Meta_KExprMap_find_x3f(
        v_00_u03b1_744_,
        v_m_745_,
        v_e_746_,
        v_a_747_,
        v_a_748_,
        v_a_749_,
        v_a_750_,
    );
    lean_dec(v_a_750_);
    lean_dec_ref(v_a_749_);
    lean_dec(v_a_748_);
    lean_dec_ref(v_a_747_);
    lean_dec_ref(v_m_745_);
    return v_res_752_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(
    mut v_00_u03b2_753_: *mut LeanObject,
    mut v_x_754_: *mut LeanObject,
    mut v_x_755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
    v___x_756_ =
        l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(
            v_x_754_, v_x_755_,
        );
    return v___x_756_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___boxed(
    mut v_00_u03b2_757_: *mut LeanObject,
    mut v_x_758_: *mut LeanObject,
    mut v_x_759_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_760_: *mut LeanObject = core::ptr::null_mut();
    v_res_760_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0(
        v_00_u03b2_757_,
        v_x_758_,
        v_x_759_,
    );
    lean_dec(v_x_759_);
    lean_dec_ref(v_x_758_);
    return v_res_760_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(
    mut v_00_u03b1_761_: *mut LeanObject,
    mut v_e_762_: *mut LeanObject,
    mut v_x_763_: *mut LeanObject,
    mut v_x_764_: *mut LeanObject,
    mut v___y_765_: *mut LeanObject,
    mut v___y_766_: *mut LeanObject,
    mut v___y_767_: *mut LeanObject,
    mut v___y_768_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_770_: *mut LeanObject = core::ptr::null_mut();
    v___x_770_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___redArg(v_e_762_, v_x_763_, v_x_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
    return v___x_770_;
}
pub unsafe fn l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1___boxed(
    mut v_00_u03b1_771_: *mut LeanObject,
    mut v_e_772_: *mut LeanObject,
    mut v_x_773_: *mut LeanObject,
    mut v_x_774_: *mut LeanObject,
    mut v___y_775_: *mut LeanObject,
    mut v___y_776_: *mut LeanObject,
    mut v___y_777_: *mut LeanObject,
    mut v___y_778_: *mut LeanObject,
    mut v___y_779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_780_: *mut LeanObject = core::ptr::null_mut();
    v_res_780_ = l___private_Lean_Data_AssocList_0__Lean_AssocList_forIn_loop___at___00Lean_Meta_KExprMap_find_x3f_spec__1(v_00_u03b1_771_, v_e_772_, v_x_773_, v_x_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_);
    lean_dec(v___y_778_);
    lean_dec_ref(v___y_777_);
    lean_dec(v___y_776_);
    lean_dec_ref(v___y_775_);
    return v_res_780_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(
    mut v_00_u03b2_781_: *mut LeanObject,
    mut v_x_782_: *mut LeanObject,
    mut v_x_783_: usize,
    mut v_x_784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_785_: *mut LeanObject = core::ptr::null_mut();
    v___x_785_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg(v_x_782_, v_x_783_, v_x_784_);
    return v___x_785_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_786_: *mut LeanObject,
    mut v_x_787_: *mut LeanObject,
    mut v_x_788_: *mut LeanObject,
    mut v_x_789_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_1712__boxed_790_: usize = 0;
    let mut v_res_791_: *mut LeanObject = core::ptr::null_mut();
    v_x_1712__boxed_790_ = lean_unbox_usize(v_x_788_);
    lean_dec(v_x_788_);
    v_res_791_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0(v_00_u03b2_786_, v_x_787_, v_x_1712__boxed_790_, v_x_789_);
    lean_dec(v_x_789_);
    lean_dec_ref(v_x_787_);
    return v_res_791_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_792_: *mut LeanObject,
    mut v_keys_793_: *mut LeanObject,
    mut v_vals_794_: *mut LeanObject,
    mut v_heq_795_: *mut LeanObject,
    mut v_i_796_: *mut LeanObject,
    mut v_k_797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_798_: *mut LeanObject = core::ptr::null_mut();
    v___x_798_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___redArg(v_keys_793_, v_vals_794_, v_i_796_, v_k_797_);
    return v___x_798_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_799_: *mut LeanObject,
    mut v_keys_800_: *mut LeanObject,
    mut v_vals_801_: *mut LeanObject,
    mut v_heq_802_: *mut LeanObject,
    mut v_i_803_: *mut LeanObject,
    mut v_k_804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_805_: *mut LeanObject = core::ptr::null_mut();
    v_res_805_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0_spec__1(v_00_u03b2_799_, v_keys_800_, v_vals_801_, v_heq_802_, v_i_803_, v_k_804_);
    lean_dec(v_k_804_);
    lean_dec_ref(v_vals_801_);
    lean_dec_ref(v_keys_800_);
    return v_res_805_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
    mut v_ps_806_: *mut LeanObject,
    mut v_e_807_: *mut LeanObject,
    mut v_v_808_: *mut LeanObject,
    mut v_a_809_: *mut LeanObject,
    mut v_a_810_: *mut LeanObject,
    mut v_a_811_: *mut LeanObject,
    mut v_a_812_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_818_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_821_: u8 = 0;
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_826_: u8 = 0;
    let mut v___x_827_: u8 = 0;
    let mut v___x_828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_832_: u8 = 0;
    let mut v___x_834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_839_: u8 = 0;
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_846_: u8 = 0;
    let mut v_a_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_854_: u8 = 0;
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_ps_806_) == 0 {
                    v___x_814_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_814_, 0, v_e_807_);
                    lean_ctor_set(v___x_814_, 1, v_v_808_);
                    lean_ctor_set(v___x_814_, 2, v_ps_806_);
                    v___x_815_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_815_, 0, v___x_814_);
                    return v___x_815_;
                } else {
                    v_key_816_ = lean_ctor_get(v_ps_806_, 0);
                    v_value_817_ = lean_ctor_get(v_ps_806_, 1);
                    v_tail_818_ = lean_ctor_get(v_ps_806_, 2);
                    v_isSharedCheck_855_ = (!lean_is_exclusive(v_ps_806_)) as u8;
                    if v_isSharedCheck_855_ == 0 {
                        v___x_820_ = v_ps_806_;
                        v_isShared_821_ = v_isSharedCheck_855_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_818_);
                        lean_inc(v_value_817_);
                        lean_inc(v_key_816_);
                        lean_dec(v_ps_806_);
                        v___x_820_ = lean_box(0);
                        v_isShared_821_ = v_isSharedCheck_855_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc(v_key_816_);
                lean_inc_ref(v_e_807_);
                v___x_822_ = l_Lean_Meta_isExprDefEq(
                    v_e_807_, v_key_816_, v_a_809_, v_a_810_, v_a_811_, v_a_812_,
                );
                if lean_obj_tag(v___x_822_) == 0 {
                    v_a_823_ = lean_ctor_get(v___x_822_, 0);
                    v_isSharedCheck_846_ = (!lean_is_exclusive(v___x_822_)) as u8;
                    if v_isSharedCheck_846_ == 0 {
                        v___x_825_ = v___x_822_;
                        v_isShared_826_ = v_isSharedCheck_846_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_823_);
                        lean_dec(v___x_822_);
                        v___x_825_ = lean_box(0);
                        v_isShared_826_ = v_isSharedCheck_846_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_820_);
                    lean_dec(v_tail_818_);
                    lean_dec(v_value_817_);
                    lean_dec(v_key_816_);
                    lean_dec(v_v_808_);
                    lean_dec_ref(v_e_807_);
                    v_a_847_ = lean_ctor_get(v___x_822_, 0);
                    v_isSharedCheck_854_ = (!lean_is_exclusive(v___x_822_)) as u8;
                    if v_isSharedCheck_854_ == 0 {
                        v___x_849_ = v___x_822_;
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_847_);
                        lean_dec(v___x_822_);
                        v___x_849_ = lean_box(0);
                        v_isShared_850_ = v_isSharedCheck_854_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                v___x_827_ = (lean_unbox(v_a_823_) as u8);
                lean_dec(v_a_823_);
                if v___x_827_ == 0 {
                    lean_del_object(v___x_825_);
                    v___x_828_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
                        v_tail_818_,
                        v_e_807_,
                        v_v_808_,
                        v_a_809_,
                        v_a_810_,
                        v_a_811_,
                        v_a_812_,
                    );
                    if lean_obj_tag(v___x_828_) == 0 {
                        v_a_829_ = lean_ctor_get(v___x_828_, 0);
                        v_isSharedCheck_839_ = (!lean_is_exclusive(v___x_828_)) as u8;
                        if v_isSharedCheck_839_ == 0 {
                            v___x_831_ = v___x_828_;
                            v_isShared_832_ = v_isSharedCheck_839_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_829_);
                            lean_dec(v___x_828_);
                            v___x_831_ = lean_box(0);
                            v_isShared_832_ = v_isSharedCheck_839_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_820_);
                        lean_dec(v_value_817_);
                        lean_dec(v_key_816_);
                        return v___x_828_;
                    }
                } else {
                    lean_dec(v_value_817_);
                    lean_dec(v_key_816_);
                    if v_isShared_821_ == 0 {
                        lean_ctor_set(v___x_820_, 1, v_v_808_);
                        lean_ctor_set(v___x_820_, 0, v_e_807_);
                        v___x_841_ = v___x_820_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_845_, 0, v_e_807_);
                        lean_ctor_set(v_reuseFailAlloc_845_, 1, v_v_808_);
                        lean_ctor_set(v_reuseFailAlloc_845_, 2, v_tail_818_);
                        v___x_841_ = v_reuseFailAlloc_845_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_821_ == 0 {
                    lean_ctor_set(v___x_820_, 2, v_a_829_);
                    v___x_834_ = v___x_820_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_838_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_838_, 0, v_key_816_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 1, v_value_817_);
                    lean_ctor_set(v_reuseFailAlloc_838_, 2, v_a_829_);
                    v___x_834_ = v_reuseFailAlloc_838_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_832_ == 0 {
                    lean_ctor_set(v___x_831_, 0, v___x_834_);
                    v___x_836_ = v___x_831_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_837_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_837_, 0, v___x_834_);
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
                    lean_ctor_set(v___x_825_, 0, v___x_841_);
                    v___x_843_ = v___x_825_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
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
                    v_reuseFailAlloc_853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_853_, 0, v_a_847_);
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
    mut v_ps_856_: *mut LeanObject,
    mut v_e_857_: *mut LeanObject,
    mut v_v_858_: *mut LeanObject,
    mut v_a_859_: *mut LeanObject,
    mut v_a_860_: *mut LeanObject,
    mut v_a_861_: *mut LeanObject,
    mut v_a_862_: *mut LeanObject,
    mut v_a_863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_864_: *mut LeanObject = core::ptr::null_mut();
    v_res_864_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
        v_ps_856_, v_e_857_, v_v_858_, v_a_859_, v_a_860_, v_a_861_, v_a_862_,
    );
    lean_dec(v_a_862_);
    lean_dec_ref(v_a_861_);
    lean_dec(v_a_860_);
    lean_dec_ref(v_a_859_);
    return v_res_864_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList(
    mut v_00_u03b1_865_: *mut LeanObject,
    mut v_ps_866_: *mut LeanObject,
    mut v_e_867_: *mut LeanObject,
    mut v_v_868_: *mut LeanObject,
    mut v_a_869_: *mut LeanObject,
    mut v_a_870_: *mut LeanObject,
    mut v_a_871_: *mut LeanObject,
    mut v_a_872_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_874_: *mut LeanObject = core::ptr::null_mut();
    v___x_874_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
        v_ps_866_, v_e_867_, v_v_868_, v_a_869_, v_a_870_, v_a_871_, v_a_872_,
    );
    return v___x_874_;
}
pub unsafe fn l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___boxed(
    mut v_00_u03b1_875_: *mut LeanObject,
    mut v_ps_876_: *mut LeanObject,
    mut v_e_877_: *mut LeanObject,
    mut v_v_878_: *mut LeanObject,
    mut v_a_879_: *mut LeanObject,
    mut v_a_880_: *mut LeanObject,
    mut v_a_881_: *mut LeanObject,
    mut v_a_882_: *mut LeanObject,
    mut v_a_883_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_884_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_882_);
    lean_dec_ref(v_a_881_);
    lean_dec(v_a_880_);
    lean_dec_ref(v_a_879_);
    return v_res_884_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_885_: *mut LeanObject,
    mut v_x_886_: *mut LeanObject,
    mut v_x_887_: *mut LeanObject,
    mut v_x_888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_893_: u8 = 0;
    let mut v___x_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_895_: u8 = 0;
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_914_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_889_ = lean_ctor_get(v_x_885_, 0);
                v_vs_890_ = lean_ctor_get(v_x_885_, 1);
                v_isSharedCheck_914_ = (!lean_is_exclusive(v_x_885_)) as u8;
                if v_isSharedCheck_914_ == 0 {
                    v___x_892_ = v_x_885_;
                    v_isShared_893_ = v_isSharedCheck_914_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_890_);
                    lean_inc(v_ks_889_);
                    lean_dec(v_x_885_);
                    v___x_892_ = lean_box(0);
                    v_isShared_893_ = v_isSharedCheck_914_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_894_ = lean_array_get_size(v_ks_889_);
                v___x_895_ = lean_nat_dec_lt(v_x_886_, v___x_894_);
                if v___x_895_ == 0 {
                    lean_dec(v_x_886_);
                    v___x_896_ = lean_array_push(v_ks_889_, v_x_887_);
                    v___x_897_ = lean_array_push(v_vs_890_, v_x_888_);
                    if v_isShared_893_ == 0 {
                        lean_ctor_set(v___x_892_, 1, v___x_897_);
                        lean_ctor_set(v___x_892_, 0, v___x_896_);
                        v___x_899_ = v___x_892_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_900_, 0, v___x_896_);
                        lean_ctor_set(v_reuseFailAlloc_900_, 1, v___x_897_);
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
                            v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_908_, 0, v_ks_889_);
                            lean_ctor_set(v_reuseFailAlloc_908_, 1, v_vs_890_);
                            v___x_904_ = v_reuseFailAlloc_908_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_909_ = lean_array_fset(v_ks_889_, v_x_886_, v_x_887_);
                        v___x_910_ = lean_array_fset(v_vs_890_, v_x_886_, v_x_888_);
                        lean_dec(v_x_886_);
                        if v_isShared_893_ == 0 {
                            lean_ctor_set(v___x_892_, 1, v___x_910_);
                            lean_ctor_set(v___x_892_, 0, v___x_909_);
                            v___x_912_ = v___x_892_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_913_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_913_, 0, v___x_909_);
                            lean_ctor_set(v_reuseFailAlloc_913_, 1, v___x_910_);
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
                v___x_905_ = lean_unsigned_to_nat(1);
                v___x_906_ = lean_nat_add(v_x_886_, v___x_905_);
                lean_dec(v_x_886_);
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
    mut v_n_915_: *mut LeanObject,
    mut v_k_916_: *mut LeanObject,
    mut v_v_917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut LeanObject = core::ptr::null_mut();
    v___x_918_ = lean_unsigned_to_nat(0);
    v___x_919_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_n_915_, v___x_918_, v_k_916_, v_v_917_);
    return v___x_919_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_920_: *mut LeanObject = core::ptr::null_mut();
    v___x_920_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_920_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(
    mut v_x_921_: *mut LeanObject,
    mut v_x_922_: usize,
    mut v_x_923_: usize,
    mut v_x_924_: *mut LeanObject,
    mut v_x_925_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_927_: usize = 0;
    let mut v___x_928_: usize = 0;
    let mut v___x_929_: usize = 0;
    let mut v___x_930_: usize = 0;
    let mut v_j_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_933_: u8 = 0;
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v_v_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_950_: u8 = 0;
    let mut v___x_951_: u8 = 0;
    let mut v___x_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_957_: u8 = 0;
    let mut v_node_958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_961_: u8 = 0;
    let mut v___x_962_: usize = 0;
    let mut v___x_963_: usize = 0;
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_968_: u8 = 0;
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_970_: u8 = 0;
    let mut v_unused_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_976_: u8 = 0;
    let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_981_: u8 = 0;
    let mut v_ks_982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_987_: usize = 0;
    let mut v___x_988_: u8 = 0;
    let mut v___x_989_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_991_: u8 = 0;
    let mut v_reuseFailAlloc_992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_993_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_921_) == 0 {
                    v_es_926_ = lean_ctor_get(v_x_921_, 0);
                    v___x_927_ = 5usize;
                    v___x_928_ = 1usize;
                    v___x_929_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_930_ = lean_usize_land(v_x_922_, v___x_929_);
                    v_j_931_ = lean_usize_to_nat(v___x_930_);
                    v___x_932_ = lean_array_get_size(v_es_926_);
                    v___x_933_ = lean_nat_dec_lt(v_j_931_, v___x_932_);
                    if v___x_933_ == 0 {
                        lean_dec(v_j_931_);
                        lean_dec(v_x_925_);
                        lean_dec(v_x_924_);
                        return v_x_921_;
                    } else {
                        lean_inc_ref(v_es_926_);
                        v_isSharedCheck_970_ = (!lean_is_exclusive(v_x_921_)) as u8;
                        if v_isSharedCheck_970_ == 0 {
                            v_unused_971_ = lean_ctor_get(v_x_921_, 0);
                            lean_dec(v_unused_971_);
                            v___x_935_ = v_x_921_;
                            v_isShared_936_ = v_isSharedCheck_970_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_921_);
                            v___x_935_ = lean_box(0);
                            v_isShared_936_ = v_isSharedCheck_970_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_972_ = lean_ctor_get(v_x_921_, 0);
                    v_vs_973_ = lean_ctor_get(v_x_921_, 1);
                    v_isSharedCheck_993_ = (!lean_is_exclusive(v_x_921_)) as u8;
                    if v_isSharedCheck_993_ == 0 {
                        v___x_975_ = v_x_921_;
                        v_isShared_976_ = v_isSharedCheck_993_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_973_);
                        lean_inc(v_ks_972_);
                        lean_dec(v_x_921_);
                        v___x_975_ = lean_box(0);
                        v_isShared_976_ = v_isSharedCheck_993_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_937_ = lean_array_fget(v_es_926_, v_j_931_);
                v___x_938_ = lean_box(0);
                v_xs_x27_939_ = lean_array_fset(v_es_926_, v_j_931_, v___x_938_);
                match lean_obj_tag(v_v_937_) {
                    0 => {
                        v_key_946_ = lean_ctor_get(v_v_937_, 0);
                        v_val_947_ = lean_ctor_get(v_v_937_, 1);
                        v_isSharedCheck_957_ = (!lean_is_exclusive(v_v_937_)) as u8;
                        if v_isSharedCheck_957_ == 0 {
                            v___x_949_ = v_v_937_;
                            v_isShared_950_ = v_isSharedCheck_957_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_947_);
                            lean_inc(v_key_946_);
                            lean_dec(v_v_937_);
                            v___x_949_ = lean_box(0);
                            v_isShared_950_ = v_isSharedCheck_957_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_958_ = lean_ctor_get(v_v_937_, 0);
                        v_isSharedCheck_968_ = (!lean_is_exclusive(v_v_937_)) as u8;
                        if v_isSharedCheck_968_ == 0 {
                            v___x_960_ = v_v_937_;
                            v_isShared_961_ = v_isSharedCheck_968_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_958_);
                            lean_dec(v_v_937_);
                            v___x_960_ = lean_box(0);
                            v_isShared_961_ = v_isSharedCheck_968_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_969_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_969_, 0, v_x_924_);
                        lean_ctor_set(v___x_969_, 1, v_x_925_);
                        v___y_941_ = v___x_969_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_942_ = lean_array_fset(v_xs_x27_939_, v_j_931_, v___y_941_);
                lean_dec(v_j_931_);
                if v_isShared_936_ == 0 {
                    lean_ctor_set(v___x_935_, 0, v___x_942_);
                    v___x_944_ = v___x_935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_945_, 0, v___x_942_);
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
                    lean_del_object(v___x_949_);
                    v___x_952_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_946_, v_val_947_, v_x_924_, v_x_925_,
                    );
                    v___x_953_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_953_, 0, v___x_952_);
                    v___y_941_ = v___x_953_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_947_);
                    lean_dec(v_key_946_);
                    if v_isShared_950_ == 0 {
                        lean_ctor_set(v___x_949_, 1, v_x_925_);
                        lean_ctor_set(v___x_949_, 0, v_x_924_);
                        v___x_955_ = v___x_949_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_956_, 0, v_x_924_);
                        lean_ctor_set(v_reuseFailAlloc_956_, 1, v_x_925_);
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
                    lean_ctor_set(v___x_960_, 0, v___x_964_);
                    v___x_966_ = v___x_960_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_967_, 0, v___x_964_);
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
                    v_reuseFailAlloc_992_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_992_, 0, v_ks_972_);
                    lean_ctor_set(v_reuseFailAlloc_992_, 1, v_vs_973_);
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
                    v___x_990_ = lean_unsigned_to_nat(4);
                    v___x_991_ = lean_nat_dec_lt(v___x_989_, v___x_990_);
                    lean_dec(v___x_989_);
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
                    v_ks_982_ = lean_ctor_get(v_newNode_979_, 0);
                    lean_inc_ref(v_ks_982_);
                    v_vs_983_ = lean_ctor_get(v_newNode_979_, 1);
                    lean_inc_ref(v_vs_983_);
                    lean_dec_ref(v_newNode_979_);
                    v___x_984_ = lean_unsigned_to_nat(0);
                    v___x_985_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___closed__0);
                    v___x_986_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_x_923_, v_ks_982_, v_vs_983_, v___x_984_, v___x_985_);
                    lean_dec_ref(v_vs_983_);
                    lean_dec_ref(v_ks_982_);
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
    mut v_keys_995_: *mut LeanObject,
    mut v_vals_996_: *mut LeanObject,
    mut v_i_997_: *mut LeanObject,
    mut v_entries_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    let mut v_k_1001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1003_: u64 = 0;
    let mut v_h_1004_: usize = 0;
    let mut v___x_1005_: usize = 0;
    let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1007_: usize = 0;
    let mut v___x_1008_: usize = 0;
    let mut v___x_1009_: usize = 0;
    let mut v_h_1010_: usize = 0;
    let mut v___x_1011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_999_ = lean_array_get_size(v_keys_995_);
                v___x_1000_ = lean_nat_dec_lt(v_i_997_, v___x_999_);
                if v___x_1000_ == 0 {
                    lean_dec(v_i_997_);
                    return v_entries_998_;
                } else {
                    v_k_1001_ = lean_array_fget_borrowed(v_keys_995_, v_i_997_);
                    v_v_1002_ = lean_array_fget_borrowed(v_vals_996_, v_i_997_);
                    v___x_1003_ = l_Lean_HeadIndex_hash(v_k_1001_);
                    v_h_1004_ = lean_uint64_to_usize(v___x_1003_);
                    v___x_1005_ = 5usize;
                    v___x_1006_ = lean_unsigned_to_nat(1);
                    v___x_1007_ = 1usize;
                    v___x_1008_ = lean_usize_sub(v_depth_994_, v___x_1007_);
                    v___x_1009_ = lean_usize_mul(v___x_1005_, v___x_1008_);
                    v_h_1010_ = lean_usize_shift_right(v_h_1004_, v___x_1009_);
                    v___x_1011_ = lean_nat_add(v_i_997_, v___x_1006_);
                    lean_dec(v_i_997_);
                    lean_inc(v_v_1002_);
                    lean_inc(v_k_1001_);
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
    mut v_depth_1014_: *mut LeanObject,
    mut v_keys_1015_: *mut LeanObject,
    mut v_vals_1016_: *mut LeanObject,
    mut v_i_1017_: *mut LeanObject,
    mut v_entries_1018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1019_: usize = 0;
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1019_ = lean_unbox_usize(v_depth_1014_);
    lean_dec(v_depth_1014_);
    v_res_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_boxed_1019_, v_keys_1015_, v_vals_1016_, v_i_1017_, v_entries_1018_);
    lean_dec_ref(v_vals_1016_);
    lean_dec_ref(v_keys_1015_);
    return v_res_1020_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg___boxed(
    mut v_x_1021_: *mut LeanObject,
    mut v_x_1022_: *mut LeanObject,
    mut v_x_1023_: *mut LeanObject,
    mut v_x_1024_: *mut LeanObject,
    mut v_x_1025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_737__boxed_1026_: usize = 0;
    let mut v_x_738__boxed_1027_: usize = 0;
    let mut v_res_1028_: *mut LeanObject = core::ptr::null_mut();
    v_x_737__boxed_1026_ = lean_unbox_usize(v_x_1022_);
    lean_dec(v_x_1022_);
    v_x_738__boxed_1027_ = lean_unbox_usize(v_x_1023_);
    lean_dec(v_x_1023_);
    v_res_1028_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1021_, v_x_737__boxed_1026_, v_x_738__boxed_1027_, v_x_1024_, v_x_1025_);
    return v_res_1028_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(
    mut v_x_1029_: *mut LeanObject,
    mut v_x_1030_: *mut LeanObject,
    mut v_x_1031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1032_: u64 = 0;
    let mut v___x_1033_: usize = 0;
    let mut v___x_1034_: usize = 0;
    let mut v___x_1035_: *mut LeanObject = core::ptr::null_mut();
    v___x_1032_ = l_Lean_HeadIndex_hash(v_x_1030_);
    v___x_1033_ = lean_uint64_to_usize(v___x_1032_);
    v___x_1034_ = 1usize;
    v___x_1035_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1029_, v___x_1033_, v___x_1034_, v_x_1030_, v_x_1031_);
    return v___x_1035_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert___redArg(
    mut v_m_1036_: *mut LeanObject,
    mut v_e_1037_: *mut LeanObject,
    mut v_v_1038_: *mut LeanObject,
    mut v_a_1039_: *mut LeanObject,
    mut v_a_1040_: *mut LeanObject,
    mut v_a_1041_: *mut LeanObject,
    mut v_a_1042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_1044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1050_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1060_: u8 = 0;
    let mut v_a_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1064_: u8 = 0;
    let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1068_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_e_1037_);
                v_k_1044_ = l_Lean_Expr_toHeadIndex(v_e_1037_);
                v___x_1045_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_KExprMap_find_x3f_spec__0___redArg(v_m_1036_, v_k_1044_);
                if lean_obj_tag(v___x_1045_) == 0 {
                    v___x_1046_ = lean_box(0);
                    v___x_1047_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_1047_, 0, v_e_1037_);
                    lean_ctor_set(v___x_1047_, 1, v_v_1038_);
                    lean_ctor_set(v___x_1047_, 2, v___x_1046_);
                    v___x_1048_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(v_m_1036_, v_k_1044_, v___x_1047_);
                    v___x_1049_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1049_, 0, v___x_1048_);
                    return v___x_1049_;
                } else {
                    v_val_1050_ = lean_ctor_get(v___x_1045_, 0);
                    lean_inc(v_val_1050_);
                    lean_dec_ref_known(v___x_1045_, 1);
                    v___x_1051_ = l___private_Lean_Meta_KExprMap_0__Lean_Meta_updateList___redArg(
                        v_val_1050_,
                        v_e_1037_,
                        v_v_1038_,
                        v_a_1039_,
                        v_a_1040_,
                        v_a_1041_,
                        v_a_1042_,
                    );
                    if lean_obj_tag(v___x_1051_) == 0 {
                        v_a_1052_ = lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1060_ = (!lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1060_ == 0 {
                            v___x_1054_ = v___x_1051_;
                            v_isShared_1055_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1052_);
                            lean_dec(v___x_1051_);
                            v___x_1054_ = lean_box(0);
                            v_isShared_1055_ = v_isSharedCheck_1060_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_k_1044_);
                        lean_dec_ref(v_m_1036_);
                        v_a_1061_ = lean_ctor_get(v___x_1051_, 0);
                        v_isSharedCheck_1068_ = (!lean_is_exclusive(v___x_1051_)) as u8;
                        if v_isSharedCheck_1068_ == 0 {
                            v___x_1063_ = v___x_1051_;
                            v_isShared_1064_ = v_isSharedCheck_1068_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_1061_);
                            lean_dec(v___x_1051_);
                            v___x_1063_ = lean_box(0);
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
                    lean_ctor_set(v___x_1054_, 0, v___x_1056_);
                    v___x_1058_ = v___x_1054_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1059_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1059_, 0, v___x_1056_);
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
                    v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
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
    mut v_m_1069_: *mut LeanObject,
    mut v_e_1070_: *mut LeanObject,
    mut v_v_1071_: *mut LeanObject,
    mut v_a_1072_: *mut LeanObject,
    mut v_a_1073_: *mut LeanObject,
    mut v_a_1074_: *mut LeanObject,
    mut v_a_1075_: *mut LeanObject,
    mut v_a_1076_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1077_: *mut LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_Lean_Meta_KExprMap_insert___redArg(
        v_m_1069_, v_e_1070_, v_v_1071_, v_a_1072_, v_a_1073_, v_a_1074_, v_a_1075_,
    );
    lean_dec(v_a_1075_);
    lean_dec_ref(v_a_1074_);
    lean_dec(v_a_1073_);
    lean_dec_ref(v_a_1072_);
    return v_res_1077_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert(
    mut v_00_u03b1_1078_: *mut LeanObject,
    mut v_m_1079_: *mut LeanObject,
    mut v_e_1080_: *mut LeanObject,
    mut v_v_1081_: *mut LeanObject,
    mut v_a_1082_: *mut LeanObject,
    mut v_a_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
    mut v_a_1085_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1087_: *mut LeanObject = core::ptr::null_mut();
    v___x_1087_ = l_Lean_Meta_KExprMap_insert___redArg(
        v_m_1079_, v_e_1080_, v_v_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_,
    );
    return v___x_1087_;
}
pub unsafe fn l_Lean_Meta_KExprMap_insert___boxed(
    mut v_00_u03b1_1088_: *mut LeanObject,
    mut v_m_1089_: *mut LeanObject,
    mut v_e_1090_: *mut LeanObject,
    mut v_v_1091_: *mut LeanObject,
    mut v_a_1092_: *mut LeanObject,
    mut v_a_1093_: *mut LeanObject,
    mut v_a_1094_: *mut LeanObject,
    mut v_a_1095_: *mut LeanObject,
    mut v_a_1096_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1097_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_1095_);
    lean_dec_ref(v_a_1094_);
    lean_dec(v_a_1093_);
    lean_dec_ref(v_a_1092_);
    return v_res_1097_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0(
    mut v_00_u03b2_1098_: *mut LeanObject,
    mut v_x_1099_: *mut LeanObject,
    mut v_x_1100_: *mut LeanObject,
    mut v_x_1101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    v___x_1102_ =
        l_Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0___redArg(
            v_x_1099_, v_x_1100_, v_x_1101_,
        );
    return v___x_1102_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(
    mut v_00_u03b2_1103_: *mut LeanObject,
    mut v_x_1104_: *mut LeanObject,
    mut v_x_1105_: usize,
    mut v_x_1106_: usize,
    mut v_x_1107_: *mut LeanObject,
    mut v_x_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1109_: *mut LeanObject = core::ptr::null_mut();
    v___x_1109_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___redArg(v_x_1104_, v_x_1105_, v_x_1106_, v_x_1107_, v_x_1108_);
    return v___x_1109_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0___boxed(
    mut v_00_u03b2_1110_: *mut LeanObject,
    mut v_x_1111_: *mut LeanObject,
    mut v_x_1112_: *mut LeanObject,
    mut v_x_1113_: *mut LeanObject,
    mut v_x_1114_: *mut LeanObject,
    mut v_x_1115_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_971__boxed_1116_: usize = 0;
    let mut v_x_972__boxed_1117_: usize = 0;
    let mut v_res_1118_: *mut LeanObject = core::ptr::null_mut();
    v_x_971__boxed_1116_ = lean_unbox_usize(v_x_1112_);
    lean_dec(v_x_1112_);
    v_x_972__boxed_1117_ = lean_unbox_usize(v_x_1113_);
    lean_dec(v_x_1113_);
    v_res_1118_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0(v_00_u03b2_1110_, v_x_1111_, v_x_971__boxed_1116_, v_x_972__boxed_1117_, v_x_1114_, v_x_1115_);
    return v_res_1118_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1(
    mut v_00_u03b2_1119_: *mut LeanObject,
    mut v_n_1120_: *mut LeanObject,
    mut v_k_1121_: *mut LeanObject,
    mut v_v_1122_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1123_: *mut LeanObject = core::ptr::null_mut();
    v___x_1123_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1___redArg(v_n_1120_, v_k_1121_, v_v_1122_);
    return v___x_1123_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(
    mut v_00_u03b2_1124_: *mut LeanObject,
    mut v_depth_1125_: usize,
    mut v_keys_1126_: *mut LeanObject,
    mut v_vals_1127_: *mut LeanObject,
    mut v_heq_1128_: *mut LeanObject,
    mut v_i_1129_: *mut LeanObject,
    mut v_entries_1130_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1131_: *mut LeanObject = core::ptr::null_mut();
    v___x_1131_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___redArg(v_depth_1125_, v_keys_1126_, v_vals_1127_, v_i_1129_, v_entries_1130_);
    return v___x_1131_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_1132_: *mut LeanObject,
    mut v_depth_1133_: *mut LeanObject,
    mut v_keys_1134_: *mut LeanObject,
    mut v_vals_1135_: *mut LeanObject,
    mut v_heq_1136_: *mut LeanObject,
    mut v_i_1137_: *mut LeanObject,
    mut v_entries_1138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_1139_: usize = 0;
    let mut v_res_1140_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_1139_ = lean_unbox_usize(v_depth_1133_);
    lean_dec(v_depth_1133_);
    v_res_1140_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__2(v_00_u03b2_1132_, v_depth_boxed_1139_, v_keys_1134_, v_vals_1135_, v_heq_1136_, v_i_1137_, v_entries_1138_);
    lean_dec_ref(v_vals_1135_);
    lean_dec_ref(v_keys_1134_);
    return v_res_1140_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_1141_: *mut LeanObject,
    mut v_x_1142_: *mut LeanObject,
    mut v_x_1143_: *mut LeanObject,
    mut v_x_1144_: *mut LeanObject,
    mut v_x_1145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
    v___x_1146_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_KExprMap_insert_spec__0_spec__0_spec__1_spec__2___redArg(v_x_1142_, v_x_1143_, v_x_1144_, v_x_1145_);
    return v___x_1146_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_HeadIndex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_KExprMap(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Data_AssocList(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_HeadIndex(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_KExprMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_KExprMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_KExprMap(builtin);
}

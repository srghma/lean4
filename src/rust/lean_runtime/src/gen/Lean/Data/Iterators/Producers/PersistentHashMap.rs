// Lean compiler output
// Module: Lean.Data.Iterators.Producers.PersistentHashMap
// Imports: Init.Data.Array.Subarray Init.Data.Array.Subarray.Split Lean.Data.PersistentHashMap Init.Data.Iterators.Consumers Init.Omega Init.Data.Slice.Array.Lemmas Init.Data.Array.Mem Init.Data.List.TakeDrop
use crate::r#gen::Init::Data::Array::Mem::{
    initialize_Init_Data_Array_Mem, runtime_initialize_Init_Data_Array_Mem,
};
use crate::r#gen::Init::Data::Array::Subarray::Split::{
    initialize_Init_Data_Array_Subarray_Split, l_Subarray_drop___redArg,
    runtime_initialize_Init_Data_Array_Subarray_Split,
};
use crate::r#gen::Init::Data::Array::Subarray::{
    initialize_Init_Data_Array_Subarray, l_Array_toSubarray___redArg, l_Subarray_get___redArg,
    runtime_initialize_Init_Data_Array_Subarray,
};
use crate::r#gen::Init::Data::Iterators::Consumers::{
    initialize_Init_Data_Iterators_Consumers, runtime_initialize_Init_Data_Iterators_Consumers,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Slice::Array::Lemmas::{
    initialize_Init_Data_Slice_Array_Lemmas, runtime_initialize_Init_Data_Slice_Array_Lemmas,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    initialize_Lean_Data_PersistentHashMap, runtime_initialize_Lean_Data_PersistentHashMap,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_array_to_list, lean_nat_add, lean_nat_dec_lt, lean_nat_sub,
};
pub static l_Lean_PersistentHashMap_instIterator___closed__0_value:
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
    m_fun: l_Lean_PersistentHashMap_instIterator___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_PersistentHashMap_instIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value:
    crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(
    mut v_x_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_674_) {
        0 => {
            let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_675_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_675_;
        }
        1 => {
            let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_676_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_676_;
        }
        _ => {
            let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_677_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_677_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg___boxed(
    mut v_x_678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_679_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_678_);
    crate::leanh::lean_dec(v_x_678_);
    return v_res_679_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx(
    mut v_00_u03b1_680_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_681_: *mut crate::leanh::LeanObject,
    mut v_x_682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_682_);
    return v___x_683_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___boxed(
    mut v_00_u03b1_684_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_685_: *mut crate::leanh::LeanObject,
    mut v_x_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_687_ =
        l_Lean_PersistentHashMap_Zipper_ctorIdx(v_00_u03b1_684_, v_00_u03b2_685_, v_x_686_);
    crate::leanh::lean_dec(v_x_686_);
    return v_res_687_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(
    mut v_t_688_: *mut crate::leanh::LeanObject,
    mut v_k_689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_688_) {
        0 => {
            return v_k_689_;
        }
        1 => {
            let mut v_a_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_690_ = crate::leanh::lean_ctor_get(v_t_688_, 0);
            crate::leanh::lean_inc_ref(v_a_690_);
            v_a_691_ = crate::leanh::lean_ctor_get(v_t_688_, 1);
            crate::leanh::lean_inc(v_a_691_);
            crate::leanh::lean_dec_ref_known(v_t_688_, 2);
            v___x_692_ = crate::leanh::lean_apply_2(v_k_689_, v_a_690_, v_a_691_);
            return v___x_692_;
        }
        _ => {
            let mut v_keys_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_vals_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_keys_693_ = crate::leanh::lean_ctor_get(v_t_688_, 0);
            crate::leanh::lean_inc_ref(v_keys_693_);
            v_vals_694_ = crate::leanh::lean_ctor_get(v_t_688_, 1);
            crate::leanh::lean_inc_ref(v_vals_694_);
            v_a_695_ = crate::leanh::lean_ctor_get(v_t_688_, 2);
            crate::leanh::lean_inc(v_a_695_);
            crate::leanh::lean_dec_ref_known(v_t_688_, 3);
            v___x_696_ = crate::leanh::lean_apply_4(
                v_k_689_,
                v_keys_693_,
                v_vals_694_,
                crate::leanh::lean_box(0),
                v_a_695_,
            );
            return v___x_696_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim(
    mut v_00_u03b1_697_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_698_: *mut crate::leanh::LeanObject,
    mut v_motive_699_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_700_: *mut crate::leanh::LeanObject,
    mut v_t_701_: *mut crate::leanh::LeanObject,
    mut v_h_702_: *mut crate::leanh::LeanObject,
    mut v_k_703_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_701_, v_k_703_);
    return v___x_704_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim___boxed(
    mut v_00_u03b1_705_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_706_: *mut crate::leanh::LeanObject,
    mut v_motive_707_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_708_: *mut crate::leanh::LeanObject,
    mut v_t_709_: *mut crate::leanh::LeanObject,
    mut v_h_710_: *mut crate::leanh::LeanObject,
    mut v_k_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_PersistentHashMap_Zipper_ctorElim(
        v_00_u03b1_705_,
        v_00_u03b2_706_,
        v_motive_707_,
        v_ctorIdx_708_,
        v_t_709_,
        v_h_710_,
        v_k_711_,
    );
    crate::leanh::lean_dec(v_ctorIdx_708_);
    return v_res_712_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_done_elim___redArg(
    mut v_t_713_: *mut crate::leanh::LeanObject,
    mut v_done_714_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_715_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_713_, v_done_714_);
    return v___x_715_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_done_elim(
    mut v_00_u03b1_716_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_717_: *mut crate::leanh::LeanObject,
    mut v_motive_718_: *mut crate::leanh::LeanObject,
    mut v_t_719_: *mut crate::leanh::LeanObject,
    mut v_h_720_: *mut crate::leanh::LeanObject,
    mut v_done_721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_722_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_719_, v_done_721_);
    return v___x_722_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consEntries_elim___redArg(
    mut v_t_723_: *mut crate::leanh::LeanObject,
    mut v_consEntries_724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_723_, v_consEntries_724_);
    return v___x_725_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consEntries_elim(
    mut v_00_u03b1_726_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_727_: *mut crate::leanh::LeanObject,
    mut v_motive_728_: *mut crate::leanh::LeanObject,
    mut v_t_729_: *mut crate::leanh::LeanObject,
    mut v_h_730_: *mut crate::leanh::LeanObject,
    mut v_consEntries_731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_729_, v_consEntries_731_);
    return v___x_732_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consCollision_elim___redArg(
    mut v_t_733_: *mut crate::leanh::LeanObject,
    mut v_consCollision_734_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_735_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_733_, v_consCollision_734_);
    return v___x_735_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consCollision_elim(
    mut v_00_u03b1_736_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_737_: *mut crate::leanh::LeanObject,
    mut v_motive_738_: *mut crate::leanh::LeanObject,
    mut v_t_739_: *mut crate::leanh::LeanObject,
    mut v_h_740_: *mut crate::leanh::LeanObject,
    mut v_consCollision_741_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_742_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_739_, v_consCollision_741_);
    return v___x_742_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_prependNode___redArg(
    mut v_node_743_: *mut crate::leanh::LeanObject,
    mut v_z_744_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_node_743_) == 0 {
        let mut v_es_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_es_745_ = crate::leanh::lean_ctor_get(v_node_743_, 0);
        crate::leanh::lean_inc_ref(v_es_745_);
        crate::leanh::lean_dec_ref_known(v_node_743_, 1);
        v___x_746_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_747_ = lean_array_get_size(v_es_745_);
        v___x_748_ = l_Array_toSubarray___redArg(v_es_745_, v___x_746_, v___x_747_);
        v___x_749_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_749_, 0, v___x_748_);
        crate::leanh::lean_ctor_set(v___x_749_, 1, v_z_744_);
        return v___x_749_;
    } else {
        let mut v_ks_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_ks_750_ = crate::leanh::lean_ctor_get(v_node_743_, 0);
        crate::leanh::lean_inc_ref(v_ks_750_);
        v_vs_751_ = crate::leanh::lean_ctor_get(v_node_743_, 1);
        crate::leanh::lean_inc_ref(v_vs_751_);
        crate::leanh::lean_dec_ref_known(v_node_743_, 2);
        v___x_752_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_753_ = lean_array_get_size(v_ks_750_);
        v___x_754_ = l_Array_toSubarray___redArg(v_ks_750_, v___x_752_, v___x_753_);
        v___x_755_ = lean_array_get_size(v_vs_751_);
        v___x_756_ = l_Array_toSubarray___redArg(v_vs_751_, v___x_752_, v___x_755_);
        v___x_757_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_757_, 0, v___x_754_);
        crate::leanh::lean_ctor_set(v___x_757_, 1, v___x_756_);
        crate::leanh::lean_ctor_set(v___x_757_, 2, v_z_744_);
        return v___x_757_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_prependNode(
    mut v_00_u03b1_758_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_759_: *mut crate::leanh::LeanObject,
    mut v_node_760_: *mut crate::leanh::LeanObject,
    mut v_z_761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_762_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_760_, v_z_761_);
    return v___x_762_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_step___redArg(
    mut v_it_763_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_769_: u8 = 0;
    let mut v_start_770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_774_: u8 = 0;
    let mut v___x_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v_node_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_794_: u8 = 0;
    let mut v___x_795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v___x_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_802_: u8 = 0;
    let mut v_vals_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_808_: u8 = 0;
    let mut v_start_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_it_763_) {
                0 => {
                    v___x_764_ = crate::leanh::lean_box(2);
                    return v___x_764_;
                }
                1 => {
                    v_a_765_ = crate::leanh::lean_ctor_get(v_it_763_, 0);
                    v_a_766_ = crate::leanh::lean_ctor_get(v_it_763_, 1);
                    v_isSharedCheck_802_ = (!crate::leanh::lean_is_exclusive(v_it_763_)) as u8;
                    if v_isSharedCheck_802_ == 0 {
                        v___x_768_ = v_it_763_;
                        v_isShared_769_ = v_isSharedCheck_802_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_766_);
                        crate::leanh::lean_inc(v_a_765_);
                        crate::leanh::lean_dec(v_it_763_);
                        v___x_768_ = crate::leanh::lean_box(0);
                        v_isShared_769_ = v_isSharedCheck_802_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_803_ = crate::leanh::lean_ctor_get(v_it_763_, 1);
                    v_keys_804_ = crate::leanh::lean_ctor_get(v_it_763_, 0);
                    v_a_805_ = crate::leanh::lean_ctor_get(v_it_763_, 2);
                    v_isSharedCheck_825_ = (!crate::leanh::lean_is_exclusive(v_it_763_)) as u8;
                    if v_isSharedCheck_825_ == 0 {
                        v___x_807_ = v_it_763_;
                        v_isShared_808_ = v_isSharedCheck_825_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_805_);
                        crate::leanh::lean_inc(v_vals_803_);
                        crate::leanh::lean_inc(v_keys_804_);
                        crate::leanh::lean_dec(v_it_763_);
                        v___x_807_ = crate::leanh::lean_box(0);
                        v_isShared_808_ = v_isSharedCheck_825_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_770_ = crate::leanh::lean_ctor_get(v_a_765_, 1);
                v_stop_771_ = crate::leanh::lean_ctor_get(v_a_765_, 2);
                v___x_772_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_773_ = lean_nat_sub(v_stop_771_, v_start_770_);
                v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
                crate::leanh::lean_dec(v___x_773_);
                if v___x_774_ == 0 {
                    crate::leanh::lean_del_object(v___x_768_);
                    crate::leanh::lean_dec_ref(v_a_765_);
                    v___x_775_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_775_, 0, v_a_766_);
                    return v___x_775_;
                } else {
                    v___x_776_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_a_765_);
                    v___x_777_ = l_Subarray_drop___redArg(v_a_765_, v___x_776_);
                    if v_isShared_769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_768_, 0, v___x_777_);
                        v_z_779_ = v___x_768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_801_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_777_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_766_);
                        v_z_779_ = v_reuseFailAlloc_801_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_780_ = l_Subarray_get___redArg(v_a_765_, v___x_772_);
                crate::leanh::lean_dec_ref(v_a_765_);
                match crate::leanh::lean_obj_tag(v___x_780_) {
                    0 => {
                        v_key_781_ = crate::leanh::lean_ctor_get(v___x_780_, 0);
                        v_val_782_ = crate::leanh::lean_ctor_get(v___x_780_, 1);
                        v_isSharedCheck_790_ = (!crate::leanh::lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_790_ == 0 {
                            v___x_784_ = v___x_780_;
                            v_isShared_785_ = v_isSharedCheck_790_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_782_);
                            crate::leanh::lean_inc(v_key_781_);
                            crate::leanh::lean_dec(v___x_780_);
                            v___x_784_ = crate::leanh::lean_box(0);
                            v_isShared_785_ = v_isSharedCheck_790_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_791_ = crate::leanh::lean_ctor_get(v___x_780_, 0);
                        v_isSharedCheck_799_ = (!crate::leanh::lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_799_ == 0 {
                            v___x_793_ = v___x_780_;
                            v_isShared_794_ = v_isSharedCheck_799_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_791_);
                            crate::leanh::lean_dec(v___x_780_);
                            v___x_793_ = crate::leanh::lean_box(0);
                            v_isShared_794_ = v_isSharedCheck_799_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_800_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_800_, 0, v_z_779_);
                        return v___x_800_;
                    }
                }
            }
            3 => {
                if v_isShared_785_ == 0 {
                    v___x_787_ = v___x_784_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_789_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 0, v_key_781_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_789_, 1, v_val_782_);
                    v___x_787_ = v_reuseFailAlloc_789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_788_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_788_, 0, v_z_779_);
                crate::leanh::lean_ctor_set(v___x_788_, 1, v___x_787_);
                return v___x_788_;
            }
            5 => {
                v___x_795_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_791_, v_z_779_);
                if v_isShared_794_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_793_, 0, v___x_795_);
                    v___x_797_ = v___x_793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_797_;
            }
            7 => {
                v_start_809_ = crate::leanh::lean_ctor_get(v_vals_803_, 1);
                v_stop_810_ = crate::leanh::lean_ctor_get(v_vals_803_, 2);
                v___x_811_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_812_ = lean_nat_sub(v_stop_810_, v_start_809_);
                v___x_813_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
                crate::leanh::lean_dec(v___x_812_);
                if v___x_813_ == 0 {
                    crate::leanh::lean_del_object(v___x_807_);
                    crate::leanh::lean_dec_ref(v_keys_804_);
                    crate::leanh::lean_dec_ref(v_vals_803_);
                    v___x_814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_814_, 0, v_a_805_);
                    return v___x_814_;
                } else {
                    v___x_815_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_keys_804_);
                    v___x_816_ = l_Subarray_drop___redArg(v_keys_804_, v___x_815_);
                    crate::leanh::lean_inc_ref(v_vals_803_);
                    v___x_817_ = l_Subarray_drop___redArg(v_vals_803_, v___x_815_);
                    if v_isShared_808_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_807_, 1, v___x_817_);
                        crate::leanh::lean_ctor_set(v___x_807_, 0, v___x_816_);
                        v___x_819_ = v___x_807_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_824_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_816_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_817_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_824_, 2, v_a_805_);
                        v___x_819_ = v_reuseFailAlloc_824_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_820_ = l_Subarray_get___redArg(v_keys_804_, v___x_811_);
                crate::leanh::lean_dec_ref(v_keys_804_);
                v___x_821_ = l_Subarray_get___redArg(v_vals_803_, v___x_811_);
                crate::leanh::lean_dec_ref(v_vals_803_);
                v___x_822_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_822_, 0, v___x_820_);
                crate::leanh::lean_ctor_set(v___x_822_, 1, v___x_821_);
                v___x_823_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_823_, 0, v___x_819_);
                crate::leanh::lean_ctor_set(v___x_823_, 1, v___x_822_);
                return v___x_823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_step(
    mut v_00_u03b1_826_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_827_: *mut crate::leanh::LeanObject,
    mut v_it_828_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_834_: u8 = 0;
    let mut v_start_835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut v_node_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_vals_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_873_: u8 = 0;
    let mut v_start_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_it_828_) {
                0 => {
                    v___x_829_ = crate::leanh::lean_box(2);
                    return v___x_829_;
                }
                1 => {
                    v_a_830_ = crate::leanh::lean_ctor_get(v_it_828_, 0);
                    v_a_831_ = crate::leanh::lean_ctor_get(v_it_828_, 1);
                    v_isSharedCheck_867_ = (!crate::leanh::lean_is_exclusive(v_it_828_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v___x_833_ = v_it_828_;
                        v_isShared_834_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_831_);
                        crate::leanh::lean_inc(v_a_830_);
                        crate::leanh::lean_dec(v_it_828_);
                        v___x_833_ = crate::leanh::lean_box(0);
                        v_isShared_834_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_868_ = crate::leanh::lean_ctor_get(v_it_828_, 1);
                    v_keys_869_ = crate::leanh::lean_ctor_get(v_it_828_, 0);
                    v_a_870_ = crate::leanh::lean_ctor_get(v_it_828_, 2);
                    v_isSharedCheck_890_ = (!crate::leanh::lean_is_exclusive(v_it_828_)) as u8;
                    if v_isSharedCheck_890_ == 0 {
                        v___x_872_ = v_it_828_;
                        v_isShared_873_ = v_isSharedCheck_890_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_870_);
                        crate::leanh::lean_inc(v_vals_868_);
                        crate::leanh::lean_inc(v_keys_869_);
                        crate::leanh::lean_dec(v_it_828_);
                        v___x_872_ = crate::leanh::lean_box(0);
                        v_isShared_873_ = v_isSharedCheck_890_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_835_ = crate::leanh::lean_ctor_get(v_a_830_, 1);
                v_stop_836_ = crate::leanh::lean_ctor_get(v_a_830_, 2);
                v___x_837_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_838_ = lean_nat_sub(v_stop_836_, v_start_835_);
                v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
                crate::leanh::lean_dec(v___x_838_);
                if v___x_839_ == 0 {
                    crate::leanh::lean_del_object(v___x_833_);
                    crate::leanh::lean_dec_ref(v_a_830_);
                    v___x_840_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_840_, 0, v_a_831_);
                    return v___x_840_;
                } else {
                    v___x_841_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_a_830_);
                    v___x_842_ = l_Subarray_drop___redArg(v_a_830_, v___x_841_);
                    if v_isShared_834_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_833_, 0, v___x_842_);
                        v_z_844_ = v___x_833_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_866_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_842_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_831_);
                        v_z_844_ = v_reuseFailAlloc_866_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_845_ = l_Subarray_get___redArg(v_a_830_, v___x_837_);
                crate::leanh::lean_dec_ref(v_a_830_);
                match crate::leanh::lean_obj_tag(v___x_845_) {
                    0 => {
                        v_key_846_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                        v_val_847_ = crate::leanh::lean_ctor_get(v___x_845_, 1);
                        v_isSharedCheck_855_ = (!crate::leanh::lean_is_exclusive(v___x_845_)) as u8;
                        if v_isSharedCheck_855_ == 0 {
                            v___x_849_ = v___x_845_;
                            v_isShared_850_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_847_);
                            crate::leanh::lean_inc(v_key_846_);
                            crate::leanh::lean_dec(v___x_845_);
                            v___x_849_ = crate::leanh::lean_box(0);
                            v_isShared_850_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_856_ = crate::leanh::lean_ctor_get(v___x_845_, 0);
                        v_isSharedCheck_864_ = (!crate::leanh::lean_is_exclusive(v___x_845_)) as u8;
                        if v_isSharedCheck_864_ == 0 {
                            v___x_858_ = v___x_845_;
                            v_isShared_859_ = v_isSharedCheck_864_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_856_);
                            crate::leanh::lean_dec(v___x_845_);
                            v___x_858_ = crate::leanh::lean_box(0);
                            v_isShared_859_ = v_isSharedCheck_864_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_865_, 0, v_z_844_);
                        return v___x_865_;
                    }
                }
            }
            3 => {
                if v_isShared_850_ == 0 {
                    v___x_852_ = v___x_849_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_854_, 0, v_key_846_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_854_, 1, v_val_847_);
                    v___x_852_ = v_reuseFailAlloc_854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_853_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_853_, 0, v_z_844_);
                crate::leanh::lean_ctor_set(v___x_853_, 1, v___x_852_);
                return v___x_853_;
            }
            5 => {
                v___x_860_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_856_, v_z_844_);
                if v_isShared_859_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_862_;
            }
            7 => {
                v_start_874_ = crate::leanh::lean_ctor_get(v_vals_868_, 1);
                v_stop_875_ = crate::leanh::lean_ctor_get(v_vals_868_, 2);
                v___x_876_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_877_ = lean_nat_sub(v_stop_875_, v_start_874_);
                v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
                crate::leanh::lean_dec(v___x_877_);
                if v___x_878_ == 0 {
                    crate::leanh::lean_del_object(v___x_872_);
                    crate::leanh::lean_dec_ref(v_keys_869_);
                    crate::leanh::lean_dec_ref(v_vals_868_);
                    v___x_879_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_879_, 0, v_a_870_);
                    return v___x_879_;
                } else {
                    v___x_880_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_keys_869_);
                    v___x_881_ = l_Subarray_drop___redArg(v_keys_869_, v___x_880_);
                    crate::leanh::lean_inc_ref(v_vals_868_);
                    v___x_882_ = l_Subarray_drop___redArg(v_vals_868_, v___x_880_);
                    if v_isShared_873_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_872_, 1, v___x_882_);
                        crate::leanh::lean_ctor_set(v___x_872_, 0, v___x_881_);
                        v___x_884_ = v___x_872_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_889_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_881_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_882_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_889_, 2, v_a_870_);
                        v___x_884_ = v_reuseFailAlloc_889_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_885_ = l_Subarray_get___redArg(v_keys_869_, v___x_876_);
                crate::leanh::lean_dec_ref(v_keys_869_);
                v___x_886_ = l_Subarray_get___redArg(v_vals_868_, v___x_876_);
                crate::leanh::lean_dec_ref(v_vals_868_);
                v___x_887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_887_, 0, v___x_885_);
                crate::leanh::lean_ctor_set(v___x_887_, 1, v___x_886_);
                v___x_888_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_888_, 0, v___x_884_);
                crate::leanh::lean_ctor_set(v___x_888_, 1, v___x_887_);
                return v___x_888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIterator___lam__0(
    mut v_it_891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v_start_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_918_: u8 = 0;
    let mut v_node_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_922_: u8 = 0;
    let mut v___x_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_927_: u8 = 0;
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut v_vals_931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v_start_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_it_891_) {
                0 => {
                    v___x_892_ = crate::leanh::lean_box(2);
                    return v___x_892_;
                }
                1 => {
                    v_a_893_ = crate::leanh::lean_ctor_get(v_it_891_, 0);
                    v_a_894_ = crate::leanh::lean_ctor_get(v_it_891_, 1);
                    v_isSharedCheck_930_ = (!crate::leanh::lean_is_exclusive(v_it_891_)) as u8;
                    if v_isSharedCheck_930_ == 0 {
                        v___x_896_ = v_it_891_;
                        v_isShared_897_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_894_);
                        crate::leanh::lean_inc(v_a_893_);
                        crate::leanh::lean_dec(v_it_891_);
                        v___x_896_ = crate::leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_931_ = crate::leanh::lean_ctor_get(v_it_891_, 1);
                    v_keys_932_ = crate::leanh::lean_ctor_get(v_it_891_, 0);
                    v_a_933_ = crate::leanh::lean_ctor_get(v_it_891_, 2);
                    v_isSharedCheck_953_ = (!crate::leanh::lean_is_exclusive(v_it_891_)) as u8;
                    if v_isSharedCheck_953_ == 0 {
                        v___x_935_ = v_it_891_;
                        v_isShared_936_ = v_isSharedCheck_953_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_933_);
                        crate::leanh::lean_inc(v_vals_931_);
                        crate::leanh::lean_inc(v_keys_932_);
                        crate::leanh::lean_dec(v_it_891_);
                        v___x_935_ = crate::leanh::lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_953_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_898_ = crate::leanh::lean_ctor_get(v_a_893_, 1);
                v_stop_899_ = crate::leanh::lean_ctor_get(v_a_893_, 2);
                v___x_900_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_901_ = lean_nat_sub(v_stop_899_, v_start_898_);
                v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_901_);
                crate::leanh::lean_dec(v___x_901_);
                if v___x_902_ == 0 {
                    crate::leanh::lean_del_object(v___x_896_);
                    crate::leanh::lean_dec_ref(v_a_893_);
                    v___x_903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_903_, 0, v_a_894_);
                    return v___x_903_;
                } else {
                    v___x_904_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_a_893_);
                    v___x_905_ = l_Subarray_drop___redArg(v_a_893_, v___x_904_);
                    if v_isShared_897_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_896_, 0, v___x_905_);
                        v_z_907_ = v___x_896_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_929_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_905_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_894_);
                        v_z_907_ = v_reuseFailAlloc_929_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_908_ = l_Subarray_get___redArg(v_a_893_, v___x_900_);
                crate::leanh::lean_dec_ref(v_a_893_);
                match crate::leanh::lean_obj_tag(v___x_908_) {
                    0 => {
                        v_key_909_ = crate::leanh::lean_ctor_get(v___x_908_, 0);
                        v_val_910_ = crate::leanh::lean_ctor_get(v___x_908_, 1);
                        v_isSharedCheck_918_ = (!crate::leanh::lean_is_exclusive(v___x_908_)) as u8;
                        if v_isSharedCheck_918_ == 0 {
                            v___x_912_ = v___x_908_;
                            v_isShared_913_ = v_isSharedCheck_918_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_910_);
                            crate::leanh::lean_inc(v_key_909_);
                            crate::leanh::lean_dec(v___x_908_);
                            v___x_912_ = crate::leanh::lean_box(0);
                            v_isShared_913_ = v_isSharedCheck_918_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_919_ = crate::leanh::lean_ctor_get(v___x_908_, 0);
                        v_isSharedCheck_927_ = (!crate::leanh::lean_is_exclusive(v___x_908_)) as u8;
                        if v_isSharedCheck_927_ == 0 {
                            v___x_921_ = v___x_908_;
                            v_isShared_922_ = v_isSharedCheck_927_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_919_);
                            crate::leanh::lean_dec(v___x_908_);
                            v___x_921_ = crate::leanh::lean_box(0);
                            v_isShared_922_ = v_isSharedCheck_927_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_928_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_928_, 0, v_z_907_);
                        return v___x_928_;
                    }
                }
            }
            3 => {
                if v_isShared_913_ == 0 {
                    v___x_915_ = v___x_912_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_917_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_917_, 0, v_key_909_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_917_, 1, v_val_910_);
                    v___x_915_ = v_reuseFailAlloc_917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_916_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_916_, 0, v_z_907_);
                crate::leanh::lean_ctor_set(v___x_916_, 1, v___x_915_);
                return v___x_916_;
            }
            5 => {
                v___x_923_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_919_, v_z_907_);
                if v_isShared_922_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_921_, 0, v___x_923_);
                    v___x_925_ = v___x_921_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
                    v___x_925_ = v_reuseFailAlloc_926_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_925_;
            }
            7 => {
                v_start_937_ = crate::leanh::lean_ctor_get(v_vals_931_, 1);
                v_stop_938_ = crate::leanh::lean_ctor_get(v_vals_931_, 2);
                v___x_939_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_940_ = lean_nat_sub(v_stop_938_, v_start_937_);
                v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_940_);
                crate::leanh::lean_dec(v___x_940_);
                if v___x_941_ == 0 {
                    crate::leanh::lean_del_object(v___x_935_);
                    crate::leanh::lean_dec_ref(v_keys_932_);
                    crate::leanh::lean_dec_ref(v_vals_931_);
                    v___x_942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_942_, 0, v_a_933_);
                    return v___x_942_;
                } else {
                    v___x_943_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_keys_932_);
                    v___x_944_ = l_Subarray_drop___redArg(v_keys_932_, v___x_943_);
                    crate::leanh::lean_inc_ref(v_vals_931_);
                    v___x_945_ = l_Subarray_drop___redArg(v_vals_931_, v___x_943_);
                    if v_isShared_936_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_935_, 1, v___x_945_);
                        crate::leanh::lean_ctor_set(v___x_935_, 0, v___x_944_);
                        v___x_947_ = v___x_935_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_952_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_944_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_945_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_952_, 2, v_a_933_);
                        v___x_947_ = v_reuseFailAlloc_952_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_948_ = l_Subarray_get___redArg(v_keys_932_, v___x_939_);
                crate::leanh::lean_dec_ref(v_keys_932_);
                v___x_949_ = l_Subarray_get___redArg(v_vals_931_, v___x_939_);
                crate::leanh::lean_dec_ref(v_vals_931_);
                v___x_950_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_948_);
                crate::leanh::lean_ctor_set(v___x_950_, 1, v___x_949_);
                v___x_951_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_951_, 0, v___x_947_);
                crate::leanh::lean_ctor_set(v___x_951_, 1, v___x_950_);
                return v___x_951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIterator(
    mut v_00_u03b1_955_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_957_ = l_Lean_PersistentHashMap_instIterator___closed__0;
    return v___f_957_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(
    mut v_es_958_: *mut crate::leanh::LeanObject,
    mut v_i_959_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_966_ = lean_array_get_size(v_es_958_);
                v___x_967_ = lean_nat_dec_lt(v_i_959_, v___x_966_);
                if v___x_967_ == 0 {
                    v___x_968_ = crate::leanh::lean_unsigned_to_nat(0);
                    return v___x_968_;
                } else {
                    v___x_969_ = lean_array_fget_borrowed(v_es_958_, v_i_959_);
                    if crate::leanh::lean_obj_tag(v___x_969_) == 1 {
                        v_node_970_ = crate::leanh::lean_ctor_get(v___x_969_, 0);
                        v___x_971_ = crate::leanh::lean_unsigned_to_nat(2);
                        v___x_972_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_970_);
                        v___x_973_ = lean_nat_add(v___x_971_, v___x_972_);
                        crate::leanh::lean_dec(v___x_972_);
                        v___y_961_ = v___x_973_;
                        state = 1;
                        continue;
                    } else {
                        v___x_974_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___y_961_ = v___x_974_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_962_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_963_ = lean_nat_add(v_i_959_, v___x_962_);
                v___x_964_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_958_, v___x_963_);
                crate::leanh::lean_dec(v___x_963_);
                v___x_965_ = lean_nat_add(v___y_961_, v___x_964_);
                crate::leanh::lean_dec(v___x_964_);
                crate::leanh::lean_dec(v___y_961_);
                return v___x_965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___redArg(
    mut v_node_975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_node_975_) == 0 {
        let mut v_es_976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_es_976_ = crate::leanh::lean_ctor_get(v_node_975_, 0);
        v___x_977_ = crate::leanh::lean_unsigned_to_nat(0);
        v___x_978_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_976_, v___x_977_);
        return v___x_978_;
    } else {
        let mut v_vs_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_vs_979_ = crate::leanh::lean_ctor_get(v_node_975_, 1);
        v___x_980_ = lean_array_get_size(v_vs_979_);
        return v___x_980_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___redArg___boxed(
    mut v_node_981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_981_);
    crate::leanh::lean_dec_ref(v_node_981_);
    return v_res_982_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(
    mut v_es_983_: *mut crate::leanh::LeanObject,
    mut v_i_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_983_, v_i_984_);
    crate::leanh::lean_dec(v_i_984_);
    crate::leanh::lean_dec_ref(v_es_983_);
    return v_res_985_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(
    mut v_00_u03b1_986_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_987_: *mut crate::leanh::LeanObject,
    mut v_es_988_: *mut crate::leanh::LeanObject,
    mut v_i_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_988_, v_i_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(
    mut v_00_u03b1_991_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_992_: *mut crate::leanh::LeanObject,
    mut v_es_993_: *mut crate::leanh::LeanObject,
    mut v_i_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_991_, v_00_u03b2_992_, v_es_993_, v_i_994_);
    crate::leanh::lean_dec(v_i_994_);
    crate::leanh::lean_dec_ref(v_es_993_);
    return v_res_995_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure(
    mut v_00_u03b1_996_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_997_: *mut crate::leanh::LeanObject,
    mut v_node_998_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___boxed(
    mut v_00_u03b1_1000_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1001_: *mut crate::leanh::LeanObject,
    mut v_node_1002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1003_ =
        l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_1000_, v_00_u03b2_1001_, v_node_1002_);
    crate::leanh::lean_dec_ref(v_node_1002_);
    return v_res_1003_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(
    mut v_x_1004_: *mut crate::leanh::LeanObject,
    mut v_h__1_1005_: *mut crate::leanh::LeanObject,
    mut v_h__2_1006_: *mut crate::leanh::LeanObject,
    mut v_h__3_1007_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1004_) {
        0 => {
            let mut v_key_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1007_);
            crate::leanh::lean_dec(v_h__1_1005_);
            v_key_1008_ = crate::leanh::lean_ctor_get(v_x_1004_, 0);
            crate::leanh::lean_inc(v_key_1008_);
            v_val_1009_ = crate::leanh::lean_ctor_get(v_x_1004_, 1);
            crate::leanh::lean_inc(v_val_1009_);
            crate::leanh::lean_dec_ref_known(v_x_1004_, 2);
            v___x_1010_ = crate::leanh::lean_apply_3(
                v_h__2_1006_,
                v_key_1008_,
                v_val_1009_,
                crate::leanh::lean_box(0),
            );
            return v___x_1010_;
        }
        1 => {
            let mut v_node_1011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1006_);
            crate::leanh::lean_dec(v_h__1_1005_);
            v_node_1011_ = crate::leanh::lean_ctor_get(v_x_1004_, 0);
            crate::leanh::lean_inc(v_node_1011_);
            crate::leanh::lean_dec_ref_known(v_x_1004_, 1);
            v___x_1012_ =
                crate::leanh::lean_apply_2(v_h__3_1007_, v_node_1011_, crate::leanh::lean_box(0));
            return v___x_1012_;
        }
        _ => {
            let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1007_);
            crate::leanh::lean_dec(v_h__2_1006_);
            v___x_1013_ = crate::leanh::lean_apply_1(v_h__1_1005_, crate::leanh::lean_box(0));
            return v___x_1013_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(
    mut v_00_u03b1_1014_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1015_: *mut crate::leanh::LeanObject,
    mut v_motive_1016_: *mut crate::leanh::LeanObject,
    mut v_x_1017_: *mut crate::leanh::LeanObject,
    mut v_h__1_1018_: *mut crate::leanh::LeanObject,
    mut v_h__2_1019_: *mut crate::leanh::LeanObject,
    mut v_h__3_1020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1017_) {
        0 => {
            let mut v_key_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1020_);
            crate::leanh::lean_dec(v_h__1_1018_);
            v_key_1021_ = crate::leanh::lean_ctor_get(v_x_1017_, 0);
            crate::leanh::lean_inc(v_key_1021_);
            v_val_1022_ = crate::leanh::lean_ctor_get(v_x_1017_, 1);
            crate::leanh::lean_inc(v_val_1022_);
            crate::leanh::lean_dec_ref_known(v_x_1017_, 2);
            v___x_1023_ = crate::leanh::lean_apply_3(
                v_h__2_1019_,
                v_key_1021_,
                v_val_1022_,
                crate::leanh::lean_box(0),
            );
            return v___x_1023_;
        }
        1 => {
            let mut v_node_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1019_);
            crate::leanh::lean_dec(v_h__1_1018_);
            v_node_1024_ = crate::leanh::lean_ctor_get(v_x_1017_, 0);
            crate::leanh::lean_inc(v_node_1024_);
            crate::leanh::lean_dec_ref_known(v_x_1017_, 1);
            v___x_1025_ =
                crate::leanh::lean_apply_2(v_h__3_1020_, v_node_1024_, crate::leanh::lean_box(0));
            return v___x_1025_;
        }
        _ => {
            let mut v___x_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1020_);
            crate::leanh::lean_dec(v_h__2_1019_);
            v___x_1026_ = crate::leanh::lean_apply_1(v_h__1_1018_, crate::leanh::lean_box(0));
            return v___x_1026_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(
    mut v_node_1027_: *mut crate::leanh::LeanObject,
    mut v_h__1_1028_: *mut crate::leanh::LeanObject,
    mut v_h__2_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_node_1027_) == 0 {
        let mut v_es_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1029_);
        v_es_1030_ = crate::leanh::lean_ctor_get(v_node_1027_, 0);
        crate::leanh::lean_inc_ref(v_es_1030_);
        crate::leanh::lean_dec_ref_known(v_node_1027_, 1);
        v___x_1031_ = crate::leanh::lean_apply_1(v_h__1_1028_, v_es_1030_);
        return v___x_1031_;
    } else {
        let mut v_ks_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1028_);
        v_ks_1032_ = crate::leanh::lean_ctor_get(v_node_1027_, 0);
        crate::leanh::lean_inc_ref(v_ks_1032_);
        v_vs_1033_ = crate::leanh::lean_ctor_get(v_node_1027_, 1);
        crate::leanh::lean_inc_ref(v_vs_1033_);
        crate::leanh::lean_dec_ref_known(v_node_1027_, 2);
        v___x_1034_ = crate::leanh::lean_apply_3(
            v_h__2_1029_,
            v_ks_1032_,
            v_vs_1033_,
            crate::leanh::lean_box(0),
        );
        return v___x_1034_;
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(
    mut v_00_u03b1_1035_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1036_: *mut crate::leanh::LeanObject,
    mut v_motive_1037_: *mut crate::leanh::LeanObject,
    mut v_node_1038_: *mut crate::leanh::LeanObject,
    mut v_h__1_1039_: *mut crate::leanh::LeanObject,
    mut v_h__2_1040_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_node_1038_) == 0 {
        let mut v_es_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_1040_);
        v_es_1041_ = crate::leanh::lean_ctor_get(v_node_1038_, 0);
        crate::leanh::lean_inc_ref(v_es_1041_);
        crate::leanh::lean_dec_ref_known(v_node_1038_, 1);
        v___x_1042_ = crate::leanh::lean_apply_1(v_h__1_1039_, v_es_1041_);
        return v___x_1042_;
    } else {
        let mut v_ks_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_1039_);
        v_ks_1043_ = crate::leanh::lean_ctor_get(v_node_1038_, 0);
        crate::leanh::lean_inc_ref(v_ks_1043_);
        v_vs_1044_ = crate::leanh::lean_ctor_get(v_node_1038_, 1);
        crate::leanh::lean_inc_ref(v_vs_1044_);
        crate::leanh::lean_dec_ref_known(v_node_1038_, 2);
        v___x_1045_ = crate::leanh::lean_apply_3(
            v_h__2_1040_,
            v_ks_1043_,
            v_vs_1044_,
            crate::leanh::lean_box(0),
        );
        return v___x_1045_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___redArg(
    mut v_entry_1046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_entry_1046_) == 1 {
        let mut v_node_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_node_1047_ = crate::leanh::lean_ctor_get(v_entry_1046_, 0);
        v___x_1048_ = crate::leanh::lean_unsigned_to_nat(2);
        v___x_1049_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_1047_);
        v___x_1050_ = lean_nat_add(v___x_1048_, v___x_1049_);
        crate::leanh::lean_dec(v___x_1049_);
        return v___x_1050_;
    } else {
        let mut v___x_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1051_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_1051_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(
    mut v_entry_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_1052_);
    crate::leanh::lean_dec(v_entry_1052_);
    return v_res_1053_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure(
    mut v_00_u03b1_1054_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1055_: *mut crate::leanh::LeanObject,
    mut v_entry_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___boxed(
    mut v_00_u03b1_1058_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1059_: *mut crate::leanh::LeanObject,
    mut v_entry_1060_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1061_ =
        l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_1058_, v_00_u03b2_1059_, v_entry_1060_);
    crate::leanh::lean_dec(v_entry_1060_);
    return v_res_1061_;
}
pub unsafe fn l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(
    mut v_init_1062_: *mut crate::leanh::LeanObject,
    mut v_x_1063_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_1063_) == 0 {
        crate::leanh::lean_inc(v_init_1062_);
        return v_init_1062_;
    } else {
        let mut v_head_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_head_1064_ = crate::leanh::lean_ctor_get(v_x_1063_, 0);
        v_tail_1065_ = crate::leanh::lean_ctor_get(v_x_1063_, 1);
        v___x_1066_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_1062_, v_tail_1065_);
        v___x_1067_ = lean_nat_add(v_head_1064_, v___x_1066_);
        crate::leanh::lean_dec(v___x_1066_);
        return v___x_1067_;
    }
}
pub unsafe fn l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(
    mut v_init_1068_: *mut crate::leanh::LeanObject,
    mut v_x_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_1068_, v_x_1069_);
    crate::leanh::lean_dec(v_x_1069_);
    crate::leanh::lean_dec(v_init_1068_);
    return v_res_1070_;
}
pub unsafe fn l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(
    mut v_l_1071_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1072_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1073_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_1072_, v_l_1071_);
    return v___x_1073_;
}
pub unsafe fn l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(
    mut v_l_1074_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_1074_);
    crate::leanh::lean_dec(v_l_1074_);
    return v_res_1075_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
    mut v_a_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_1079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1083_: u8 = 0;
    let mut v___x_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_1076_) == 0 {
                    v___x_1078_ = l_List_reverse___redArg(v_a_1077_);
                    return v___x_1078_;
                } else {
                    v_head_1079_ = crate::leanh::lean_ctor_get(v_a_1076_, 0);
                    v_tail_1080_ = crate::leanh::lean_ctor_get(v_a_1076_, 1);
                    v_isSharedCheck_1089_ = (!crate::leanh::lean_is_exclusive(v_a_1076_)) as u8;
                    if v_isSharedCheck_1089_ == 0 {
                        v___x_1082_ = v_a_1076_;
                        v_isShared_1083_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_1080_);
                        crate::leanh::lean_inc(v_head_1079_);
                        crate::leanh::lean_dec(v_a_1076_);
                        v___x_1082_ = crate::leanh::lean_box(0);
                        v_isShared_1083_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1084_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_1079_);
                crate::leanh::lean_dec(v_head_1079_);
                if v_isShared_1083_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1082_, 1, v_a_1077_);
                    crate::leanh::lean_ctor_set(v___x_1082_, 0, v___x_1084_);
                    v___x_1086_ = v___x_1082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1077_);
                    v___x_1086_ = v_reuseFailAlloc_1088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_1076_ = v_tail_1080_;
                v_a_1077_ = v___x_1086_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(
    mut v_a_1090_: *mut crate::leanh::LeanObject,
    mut v_b_1091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1092_ = crate::leanh::lean_ctor_get(v_a_1090_, 0);
                v_start_1093_ = crate::leanh::lean_ctor_get(v_a_1090_, 1);
                v_stop_1094_ = crate::leanh::lean_ctor_get(v_a_1090_, 2);
                v_isSharedCheck_1107_ = (!crate::leanh::lean_is_exclusive(v_a_1090_)) as u8;
                if v_isSharedCheck_1107_ == 0 {
                    v___x_1096_ = v_a_1090_;
                    v_isShared_1097_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_1094_);
                    crate::leanh::lean_inc(v_start_1093_);
                    crate::leanh::lean_inc(v_array_1092_);
                    crate::leanh::lean_dec(v_a_1090_);
                    v___x_1096_ = crate::leanh::lean_box(0);
                    v_isShared_1097_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1098_ = lean_nat_dec_lt(v_start_1093_, v_stop_1094_);
                if v___x_1098_ == 0 {
                    crate::leanh::lean_del_object(v___x_1096_);
                    crate::leanh::lean_dec(v_stop_1094_);
                    crate::leanh::lean_dec(v_start_1093_);
                    crate::leanh::lean_dec_ref(v_array_1092_);
                    return v_b_1091_;
                } else {
                    v___x_1099_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1100_ = lean_nat_add(v_start_1093_, v___x_1099_);
                    crate::leanh::lean_inc_ref(v_array_1092_);
                    if v_isShared_1097_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1096_, 1, v___x_1100_);
                        v___x_1102_ = v___x_1096_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_array_1092_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_stop_1094_);
                        v___x_1102_ = v_reuseFailAlloc_1106_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1103_ = lean_array_fget(v_array_1092_, v_start_1093_);
                crate::leanh::lean_dec(v_start_1093_);
                crate::leanh::lean_dec_ref(v_array_1092_);
                v___x_1104_ = lean_array_push(v_b_1091_, v___x_1103_);
                v_a_1090_ = v___x_1102_;
                v_b_1091_ = v___x_1104_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_subarrayMeasure___redArg(
    mut v_es_1110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0;
    v___x_1112_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_1110_, v___x_1111_);
    v___x_1113_ = lean_array_to_list(v___x_1112_);
    v___x_1114_ = crate::leanh::lean_box(0);
    v___x_1115_ =
        l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
            v___x_1113_,
            v___x_1114_,
        );
    v___x_1116_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_1115_);
    crate::leanh::lean_dec(v___x_1115_);
    return v___x_1116_;
}
pub unsafe fn l_Lean_PersistentHashMap_subarrayMeasure(
    mut v_00_u03b1_1117_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1118_: *mut crate::leanh::LeanObject,
    mut v_es_1119_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_1119_);
    return v___x_1120_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(
    mut v_00_u03b1_1121_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_R_1124_: *mut crate::leanh::LeanObject,
    mut v_a_1125_: *mut crate::leanh::LeanObject,
    mut v_b_1126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1127_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_1125_, v_b_1126_);
    return v___x_1127_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(
    mut v_00_u03b1_1128_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1129_: *mut crate::leanh::LeanObject,
    mut v_a_1130_: *mut crate::leanh::LeanObject,
    mut v_a_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1132_ =
        l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
            v_a_1130_, v_a_1131_,
        );
    return v___x_1132_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_measure___redArg(
    mut v_x_1133_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1133_) {
        0 => {
            let mut v___x_1134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1134_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_1134_;
        }
        1 => {
            let mut v_a_1135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_a_1135_ = crate::leanh::lean_ctor_get(v_x_1133_, 0);
            crate::leanh::lean_inc_ref(v_a_1135_);
            v_a_1136_ = crate::leanh::lean_ctor_get(v_x_1133_, 1);
            crate::leanh::lean_inc(v_a_1136_);
            crate::leanh::lean_dec_ref_known(v_x_1133_, 2);
            v___x_1137_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_1135_);
            v___x_1138_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_1136_);
            v___x_1139_ = lean_nat_add(v___x_1137_, v___x_1138_);
            crate::leanh::lean_dec(v___x_1138_);
            crate::leanh::lean_dec(v___x_1137_);
            v___x_1140_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1141_ = lean_nat_add(v___x_1139_, v___x_1140_);
            crate::leanh::lean_dec(v___x_1139_);
            return v___x_1141_;
        }
        _ => {
            let mut v_vals_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_start_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_stop_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_vals_1142_ = crate::leanh::lean_ctor_get(v_x_1133_, 1);
            crate::leanh::lean_inc_ref(v_vals_1142_);
            v_a_1143_ = crate::leanh::lean_ctor_get(v_x_1133_, 2);
            crate::leanh::lean_inc(v_a_1143_);
            crate::leanh::lean_dec_ref_known(v_x_1133_, 3);
            v_start_1144_ = crate::leanh::lean_ctor_get(v_vals_1142_, 1);
            crate::leanh::lean_inc(v_start_1144_);
            v_stop_1145_ = crate::leanh::lean_ctor_get(v_vals_1142_, 2);
            crate::leanh::lean_inc(v_stop_1145_);
            crate::leanh::lean_dec_ref(v_vals_1142_);
            v___x_1146_ = lean_nat_sub(v_stop_1145_, v_start_1144_);
            crate::leanh::lean_dec(v_start_1144_);
            crate::leanh::lean_dec(v_stop_1145_);
            v___x_1147_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_1143_);
            v___x_1148_ = lean_nat_add(v___x_1146_, v___x_1147_);
            crate::leanh::lean_dec(v___x_1147_);
            crate::leanh::lean_dec(v___x_1146_);
            v___x_1149_ = crate::leanh::lean_unsigned_to_nat(1);
            v___x_1150_ = lean_nat_add(v___x_1148_, v___x_1149_);
            crate::leanh::lean_dec(v___x_1148_);
            return v___x_1150_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_measure(
    mut v_00_u03b1_1151_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1152_: *mut crate::leanh::LeanObject,
    mut v_x_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_1153_);
    return v___x_1154_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(
    mut v_x_1155_: *mut crate::leanh::LeanObject,
    mut v_h__1_1156_: *mut crate::leanh::LeanObject,
    mut v_h__2_1157_: *mut crate::leanh::LeanObject,
    mut v_h__3_1158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1155_) {
        0 => {
            let mut v_key_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1158_);
            crate::leanh::lean_dec(v_h__1_1156_);
            v_key_1159_ = crate::leanh::lean_ctor_get(v_x_1155_, 0);
            crate::leanh::lean_inc(v_key_1159_);
            v_val_1160_ = crate::leanh::lean_ctor_get(v_x_1155_, 1);
            crate::leanh::lean_inc(v_val_1160_);
            crate::leanh::lean_dec_ref_known(v_x_1155_, 2);
            v___x_1161_ = crate::leanh::lean_apply_2(v_h__2_1157_, v_key_1159_, v_val_1160_);
            return v___x_1161_;
        }
        1 => {
            let mut v_node_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1157_);
            crate::leanh::lean_dec(v_h__1_1156_);
            v_node_1162_ = crate::leanh::lean_ctor_get(v_x_1155_, 0);
            crate::leanh::lean_inc(v_node_1162_);
            crate::leanh::lean_dec_ref_known(v_x_1155_, 1);
            v___x_1163_ = crate::leanh::lean_apply_1(v_h__3_1158_, v_node_1162_);
            return v___x_1163_;
        }
        _ => {
            let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1158_);
            crate::leanh::lean_dec(v_h__2_1157_);
            v___x_1164_ = crate::leanh::lean_box(0);
            v___x_1165_ = crate::leanh::lean_apply_1(v_h__1_1156_, v___x_1164_);
            return v___x_1165_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(
    mut v_00_u03b1_1166_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1167_: *mut crate::leanh::LeanObject,
    mut v_motive_1168_: *mut crate::leanh::LeanObject,
    mut v_x_1169_: *mut crate::leanh::LeanObject,
    mut v_h__1_1170_: *mut crate::leanh::LeanObject,
    mut v_h__2_1171_: *mut crate::leanh::LeanObject,
    mut v_h__3_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1169_) {
        0 => {
            let mut v_key_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1172_);
            crate::leanh::lean_dec(v_h__1_1170_);
            v_key_1173_ = crate::leanh::lean_ctor_get(v_x_1169_, 0);
            crate::leanh::lean_inc(v_key_1173_);
            v_val_1174_ = crate::leanh::lean_ctor_get(v_x_1169_, 1);
            crate::leanh::lean_inc(v_val_1174_);
            crate::leanh::lean_dec_ref_known(v_x_1169_, 2);
            v___x_1175_ = crate::leanh::lean_apply_2(v_h__2_1171_, v_key_1173_, v_val_1174_);
            return v___x_1175_;
        }
        1 => {
            let mut v_node_1176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1171_);
            crate::leanh::lean_dec(v_h__1_1170_);
            v_node_1176_ = crate::leanh::lean_ctor_get(v_x_1169_, 0);
            crate::leanh::lean_inc(v_node_1176_);
            crate::leanh::lean_dec_ref_known(v_x_1169_, 1);
            v___x_1177_ = crate::leanh::lean_apply_1(v_h__3_1172_, v_node_1176_);
            return v___x_1177_;
        }
        _ => {
            let mut v___x_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1172_);
            crate::leanh::lean_dec(v_h__2_1171_);
            v___x_1178_ = crate::leanh::lean_box(0);
            v___x_1179_ = crate::leanh::lean_apply_1(v_h__1_1170_, v___x_1178_);
            return v___x_1179_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(
    mut v_x_1180_: *mut crate::leanh::LeanObject,
    mut v_h__1_1181_: *mut crate::leanh::LeanObject,
    mut v_h__2_1182_: *mut crate::leanh::LeanObject,
    mut v_h__3_1183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1180_) {
        0 => {
            let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1183_);
            crate::leanh::lean_dec(v_h__2_1182_);
            v___x_1184_ = crate::leanh::lean_box(0);
            v___x_1185_ = crate::leanh::lean_apply_1(v_h__1_1181_, v___x_1184_);
            return v___x_1185_;
        }
        1 => {
            let mut v_a_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1183_);
            crate::leanh::lean_dec(v_h__1_1181_);
            v_a_1186_ = crate::leanh::lean_ctor_get(v_x_1180_, 0);
            crate::leanh::lean_inc_ref(v_a_1186_);
            v_a_1187_ = crate::leanh::lean_ctor_get(v_x_1180_, 1);
            crate::leanh::lean_inc(v_a_1187_);
            crate::leanh::lean_dec_ref_known(v_x_1180_, 2);
            v___x_1188_ = crate::leanh::lean_apply_2(v_h__2_1182_, v_a_1186_, v_a_1187_);
            return v___x_1188_;
        }
        _ => {
            let mut v_keys_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_vals_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1182_);
            crate::leanh::lean_dec(v_h__1_1181_);
            v_keys_1189_ = crate::leanh::lean_ctor_get(v_x_1180_, 0);
            crate::leanh::lean_inc_ref(v_keys_1189_);
            v_vals_1190_ = crate::leanh::lean_ctor_get(v_x_1180_, 1);
            crate::leanh::lean_inc_ref(v_vals_1190_);
            v_a_1191_ = crate::leanh::lean_ctor_get(v_x_1180_, 2);
            crate::leanh::lean_inc(v_a_1191_);
            crate::leanh::lean_dec_ref_known(v_x_1180_, 3);
            v___x_1192_ = crate::leanh::lean_apply_4(
                v_h__3_1183_,
                v_keys_1189_,
                v_vals_1190_,
                crate::leanh::lean_box(0),
                v_a_1191_,
            );
            return v___x_1192_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(
    mut v_00_u03b1_1193_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1194_: *mut crate::leanh::LeanObject,
    mut v_motive_1195_: *mut crate::leanh::LeanObject,
    mut v_x_1196_: *mut crate::leanh::LeanObject,
    mut v_h__1_1197_: *mut crate::leanh::LeanObject,
    mut v_h__2_1198_: *mut crate::leanh::LeanObject,
    mut v_h__3_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1196_) {
        0 => {
            let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1199_);
            crate::leanh::lean_dec(v_h__2_1198_);
            v___x_1200_ = crate::leanh::lean_box(0);
            v___x_1201_ = crate::leanh::lean_apply_1(v_h__1_1197_, v___x_1200_);
            return v___x_1201_;
        }
        1 => {
            let mut v_a_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1199_);
            crate::leanh::lean_dec(v_h__1_1197_);
            v_a_1202_ = crate::leanh::lean_ctor_get(v_x_1196_, 0);
            crate::leanh::lean_inc_ref(v_a_1202_);
            v_a_1203_ = crate::leanh::lean_ctor_get(v_x_1196_, 1);
            crate::leanh::lean_inc(v_a_1203_);
            crate::leanh::lean_dec_ref_known(v_x_1196_, 2);
            v___x_1204_ = crate::leanh::lean_apply_2(v_h__2_1198_, v_a_1202_, v_a_1203_);
            return v___x_1204_;
        }
        _ => {
            let mut v_keys_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_vals_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_a_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1198_);
            crate::leanh::lean_dec(v_h__1_1197_);
            v_keys_1205_ = crate::leanh::lean_ctor_get(v_x_1196_, 0);
            crate::leanh::lean_inc_ref(v_keys_1205_);
            v_vals_1206_ = crate::leanh::lean_ctor_get(v_x_1196_, 1);
            crate::leanh::lean_inc_ref(v_vals_1206_);
            v_a_1207_ = crate::leanh::lean_ctor_get(v_x_1196_, 2);
            crate::leanh::lean_inc(v_a_1207_);
            crate::leanh::lean_dec_ref_known(v_x_1196_, 3);
            v___x_1208_ = crate::leanh::lean_apply_4(
                v_h__3_1199_,
                v_keys_1205_,
                v_vals_1206_,
                crate::leanh::lean_box(0),
                v_a_1207_,
            );
            return v___x_1208_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(
    mut v_00_u03b1_1209_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1211_ = crate::leanh::lean_box(0);
    return v___x_1211_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(
    mut v_toPure_1212_: *mut crate::leanh::LeanObject,
    mut v_recur_1213_: *mut crate::leanh::LeanObject,
    mut v_it_1214_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1215_) == 0 {
        let mut v_a_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_1214_);
        crate::leanh::lean_dec(v_recur_1213_);
        v_a_1216_ = crate::leanh::lean_ctor_get(v_____do__lift_1215_, 0);
        crate::leanh::lean_inc(v_a_1216_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1215_, 1);
        v___x_1217_ =
            crate::leanh::lean_apply_2(v_toPure_1212_, crate::leanh::lean_box(0), v_a_1216_);
        return v___x_1217_;
    } else {
        let mut v_a_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1212_);
        v_a_1218_ = crate::leanh::lean_ctor_get(v_____do__lift_1215_, 0);
        crate::leanh::lean_inc(v_a_1218_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1215_, 1);
        v___x_1219_ = crate::leanh::lean_apply_4(
            v_recur_1213_,
            v_it_1214_,
            v_a_1218_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1219_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(
    mut v_toPure_1220_: *mut crate::leanh::LeanObject,
    mut v_recur_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v_acc_1223_: *mut crate::leanh::LeanObject,
    mut v_toBind_1224_: *mut crate::leanh::LeanObject,
    mut v_s_1225_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1225_) {
        0 => {
            let mut v_it_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1226_ = crate::leanh::lean_ctor_get(v_s_1225_, 0);
            crate::leanh::lean_inc(v_it_1226_);
            v_out_1227_ = crate::leanh::lean_ctor_get(v_s_1225_, 1);
            crate::leanh::lean_inc(v_out_1227_);
            crate::leanh::lean_dec_ref_known(v_s_1225_, 2);
            v___f_1228_ = crate::leanh::lean_alloc_closure(
                l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_1228_, 0, v_toPure_1220_);
            crate::leanh::lean_closure_set(v___f_1228_, 1, v_recur_1221_);
            crate::leanh::lean_closure_set(v___f_1228_, 2, v_it_1226_);
            v___x_1229_ = crate::leanh::lean_apply_3(
                v___y_1222_,
                v_out_1227_,
                crate::leanh::lean_box(0),
                v_acc_1223_,
            );
            v___x_1230_ = crate::leanh::lean_apply_4(
                v_toBind_1224_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1229_,
                v___f_1228_,
            );
            return v___x_1230_;
        }
        1 => {
            let mut v_it_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1224_);
            crate::leanh::lean_dec(v___y_1222_);
            crate::leanh::lean_dec(v_toPure_1220_);
            v_it_1231_ = crate::leanh::lean_ctor_get(v_s_1225_, 0);
            crate::leanh::lean_inc(v_it_1231_);
            crate::leanh::lean_dec_ref_known(v_s_1225_, 1);
            v___x_1232_ = crate::leanh::lean_apply_4(
                v_recur_1221_,
                v_it_1231_,
                v_acc_1223_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1232_;
        }
        _ => {
            let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1224_);
            crate::leanh::lean_dec(v___y_1222_);
            crate::leanh::lean_dec(v_recur_1221_);
            v___x_1233_ =
                crate::leanh::lean_apply_2(v_toPure_1220_, crate::leanh::lean_box(0), v_acc_1223_);
            return v___x_1233_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(
    mut v_toPure_1234_: *mut crate::leanh::LeanObject,
    mut v___y_1235_: *mut crate::leanh::LeanObject,
    mut v_toBind_1236_: *mut crate::leanh::LeanObject,
    mut v_lift_1237_: *mut crate::leanh::LeanObject,
    mut v_it_1238_: *mut crate::leanh::LeanObject,
    mut v_acc_1239_: *mut crate::leanh::LeanObject,
    mut v_hP_1240_: *mut crate::leanh::LeanObject,
    mut v_recur_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1249_: u8 = 0;
    let mut v_start_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_z_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_node_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v_vals_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v_start_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1242_ = crate::leanh::lean_alloc_closure(
                    l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1242_, 0, v_toPure_1234_);
                crate::leanh::lean_closure_set(v___f_1242_, 1, v_recur_1241_);
                crate::leanh::lean_closure_set(v___f_1242_, 2, v___y_1235_);
                crate::leanh::lean_closure_set(v___f_1242_, 3, v_acc_1239_);
                crate::leanh::lean_closure_set(v___f_1242_, 4, v_toBind_1236_);
                match crate::leanh::lean_obj_tag(v_it_1238_) {
                    0 => {
                        v___x_1243_ = crate::leanh::lean_box(2);
                        v___x_1244_ = crate::leanh::lean_apply_4(
                            v_lift_1237_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_1242_,
                            v___x_1243_,
                        );
                        return v___x_1244_;
                    }
                    1 => {
                        v_a_1245_ = crate::leanh::lean_ctor_get(v_it_1238_, 0);
                        v_a_1246_ = crate::leanh::lean_ctor_get(v_it_1238_, 1);
                        v_isSharedCheck_1286_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1238_)) as u8;
                        if v_isSharedCheck_1286_ == 0 {
                            v___x_1248_ = v_it_1238_;
                            v_isShared_1249_ = v_isSharedCheck_1286_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1246_);
                            crate::leanh::lean_inc(v_a_1245_);
                            crate::leanh::lean_dec(v_it_1238_);
                            v___x_1248_ = crate::leanh::lean_box(0);
                            v_isShared_1249_ = v_isSharedCheck_1286_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        v_vals_1287_ = crate::leanh::lean_ctor_get(v_it_1238_, 1);
                        v_keys_1288_ = crate::leanh::lean_ctor_get(v_it_1238_, 0);
                        v_a_1289_ = crate::leanh::lean_ctor_get(v_it_1238_, 2);
                        v_isSharedCheck_1311_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1238_)) as u8;
                        if v_isSharedCheck_1311_ == 0 {
                            v___x_1291_ = v_it_1238_;
                            v_isShared_1292_ = v_isSharedCheck_1311_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1289_);
                            crate::leanh::lean_inc(v_vals_1287_);
                            crate::leanh::lean_inc(v_keys_1288_);
                            crate::leanh::lean_dec(v_it_1238_);
                            v___x_1291_ = crate::leanh::lean_box(0);
                            v_isShared_1292_ = v_isSharedCheck_1311_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_start_1250_ = crate::leanh::lean_ctor_get(v_a_1245_, 1);
                v_stop_1251_ = crate::leanh::lean_ctor_get(v_a_1245_, 2);
                v___x_1252_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1253_ = lean_nat_sub(v_stop_1251_, v_start_1250_);
                v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
                crate::leanh::lean_dec(v___x_1253_);
                if v___x_1254_ == 0 {
                    crate::leanh::lean_del_object(v___x_1248_);
                    crate::leanh::lean_dec_ref(v_a_1245_);
                    v___x_1255_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1255_, 0, v_a_1246_);
                    v___x_1256_ = crate::leanh::lean_apply_4(
                        v_lift_1237_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1242_,
                        v___x_1255_,
                    );
                    return v___x_1256_;
                } else {
                    v___x_1257_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_a_1245_);
                    v___x_1258_ = l_Subarray_drop___redArg(v_a_1245_, v___x_1257_);
                    if v_isShared_1249_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1248_, 0, v___x_1258_);
                        v_z_1260_ = v___x_1248_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1285_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1258_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_a_1246_);
                        v_z_1260_ = v_reuseFailAlloc_1285_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1261_ = l_Subarray_get___redArg(v_a_1245_, v___x_1252_);
                crate::leanh::lean_dec_ref(v_a_1245_);
                match crate::leanh::lean_obj_tag(v___x_1261_) {
                    0 => {
                        v_key_1262_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
                        v_val_1263_ = crate::leanh::lean_ctor_get(v___x_1261_, 1);
                        v_isSharedCheck_1272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1261_)) as u8;
                        if v_isSharedCheck_1272_ == 0 {
                            v___x_1265_ = v___x_1261_;
                            v_isShared_1266_ = v_isSharedCheck_1272_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_1263_);
                            crate::leanh::lean_inc(v_key_1262_);
                            crate::leanh::lean_dec(v___x_1261_);
                            v___x_1265_ = crate::leanh::lean_box(0);
                            v_isShared_1266_ = v_isSharedCheck_1272_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1273_ = crate::leanh::lean_ctor_get(v___x_1261_, 0);
                        v_isSharedCheck_1282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1261_)) as u8;
                        if v_isSharedCheck_1282_ == 0 {
                            v___x_1275_ = v___x_1261_;
                            v_isShared_1276_ = v_isSharedCheck_1282_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_1273_);
                            crate::leanh::lean_dec(v___x_1261_);
                            v___x_1275_ = crate::leanh::lean_box(0);
                            v_isShared_1276_ = v_isSharedCheck_1282_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1283_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1283_, 0, v_z_1260_);
                        v___x_1284_ = crate::leanh::lean_apply_4(
                            v_lift_1237_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_1242_,
                            v___x_1283_,
                        );
                        return v___x_1284_;
                    }
                }
            }
            3 => {
                if v_isShared_1266_ == 0 {
                    v___x_1268_ = v___x_1265_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1271_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_key_1262_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_val_1263_);
                    v___x_1268_ = v_reuseFailAlloc_1271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1269_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1269_, 0, v_z_1260_);
                crate::leanh::lean_ctor_set(v___x_1269_, 1, v___x_1268_);
                v___x_1270_ = crate::leanh::lean_apply_4(
                    v_lift_1237_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1242_,
                    v___x_1269_,
                );
                return v___x_1270_;
            }
            5 => {
                v___x_1277_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1273_, v_z_1260_);
                if v_isShared_1276_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1275_, 0, v___x_1277_);
                    v___x_1279_ = v___x_1275_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1277_);
                    v___x_1279_ = v_reuseFailAlloc_1281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1280_ = crate::leanh::lean_apply_4(
                    v_lift_1237_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1242_,
                    v___x_1279_,
                );
                return v___x_1280_;
            }
            7 => {
                v_start_1293_ = crate::leanh::lean_ctor_get(v_vals_1287_, 1);
                v_stop_1294_ = crate::leanh::lean_ctor_get(v_vals_1287_, 2);
                v___x_1295_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1296_ = lean_nat_sub(v_stop_1294_, v_start_1293_);
                v___x_1297_ = lean_nat_dec_lt(v___x_1295_, v___x_1296_);
                crate::leanh::lean_dec(v___x_1296_);
                if v___x_1297_ == 0 {
                    crate::leanh::lean_del_object(v___x_1291_);
                    crate::leanh::lean_dec_ref(v_keys_1288_);
                    crate::leanh::lean_dec_ref(v_vals_1287_);
                    v___x_1298_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1298_, 0, v_a_1289_);
                    v___x_1299_ = crate::leanh::lean_apply_4(
                        v_lift_1237_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1242_,
                        v___x_1298_,
                    );
                    return v___x_1299_;
                } else {
                    v___x_1300_ = crate::leanh::lean_unsigned_to_nat(1);
                    crate::leanh::lean_inc_ref(v_keys_1288_);
                    v___x_1301_ = l_Subarray_drop___redArg(v_keys_1288_, v___x_1300_);
                    crate::leanh::lean_inc_ref(v_vals_1287_);
                    v___x_1302_ = l_Subarray_drop___redArg(v_vals_1287_, v___x_1300_);
                    if v_isShared_1292_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1291_, 1, v___x_1302_);
                        crate::leanh::lean_ctor_set(v___x_1291_, 0, v___x_1301_);
                        v___x_1304_ = v___x_1291_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = crate::leanh::lean_alloc_ctor(2, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1301_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1302_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_a_1289_);
                        v___x_1304_ = v_reuseFailAlloc_1310_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1305_ = l_Subarray_get___redArg(v_keys_1288_, v___x_1295_);
                crate::leanh::lean_dec_ref(v_keys_1288_);
                v___x_1306_ = l_Subarray_get___redArg(v_vals_1287_, v___x_1295_);
                crate::leanh::lean_dec_ref(v_vals_1287_);
                v___x_1307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1307_, 0, v___x_1305_);
                crate::leanh::lean_ctor_set(v___x_1307_, 1, v___x_1306_);
                v___x_1308_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1308_, 0, v___x_1304_);
                crate::leanh::lean_ctor_set(v___x_1308_, 1, v___x_1307_);
                v___x_1309_ = crate::leanh::lean_apply_4(
                    v_lift_1237_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1242_,
                    v___x_1308_,
                );
                return v___x_1309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3(
    mut v_inst_1312_: *mut crate::leanh::LeanObject,
    mut v_lift_1313_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1314_: *mut crate::leanh::LeanObject,
    mut v_Pl_1315_: *mut crate::leanh::LeanObject,
    mut v_it_1316_: *mut crate::leanh::LeanObject,
    mut v_init_1317_: *mut crate::leanh::LeanObject,
    mut v___y_1318_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1319_ = crate::leanh::lean_ctor_get(v_inst_1312_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1319_);
    v_toBind_1320_ = crate::leanh::lean_ctor_get(v_inst_1312_, 1);
    crate::leanh::lean_inc(v_toBind_1320_);
    crate::leanh::lean_dec_ref(v_inst_1312_);
    v_toPure_1321_ = crate::leanh::lean_ctor_get(v_toApplicative_1319_, 1);
    crate::leanh::lean_inc(v_toPure_1321_);
    crate::leanh::lean_dec_ref(v_toApplicative_1319_);
    v___f_1322_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1322_, 0, v_toPure_1321_);
    crate::leanh::lean_closure_set(v___f_1322_, 1, v___y_1318_);
    crate::leanh::lean_closure_set(v___f_1322_, 2, v_toBind_1320_);
    crate::leanh::lean_closure_set(v___f_1322_, 3, v_lift_1313_);
    v___x_1323_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1322_,
        v_it_1316_,
        v_init_1317_,
        crate::leanh::lean_box(0),
    );
    return v___x_1323_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg(
    mut v_inst_1324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1325_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1325_, 0, v_inst_1324_);
    return v___f_1325_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop(
    mut v_00_u03b1_1326_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1327_: *mut crate::leanh::LeanObject,
    mut v_n_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1330_ = crate::leanh::lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1330_, 0, v_inst_1329_);
    return v___f_1330_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter___redArg(
    mut v_map_1331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1332_ = crate::leanh::lean_box(0);
    v___x_1333_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_1331_, v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter(
    mut v_00_u03b1_1334_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1335_: *mut crate::leanh::LeanObject,
    mut v_inst_1336_: *mut crate::leanh::LeanObject,
    mut v_inst_1337_: *mut crate::leanh::LeanObject,
    mut v_map_1338_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1339_ = crate::leanh::lean_box(0);
    v___x_1340_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_1338_, v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter___boxed(
    mut v_00_u03b1_1341_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1342_: *mut crate::leanh::LeanObject,
    mut v_inst_1343_: *mut crate::leanh::LeanObject,
    mut v_inst_1344_: *mut crate::leanh::LeanObject,
    mut v_map_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_PersistentHashMap_iter(
        v_00_u03b1_1341_,
        v_00_u03b2_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_map_1345_,
    );
    crate::leanh::lean_dec_ref(v_inst_1344_);
    crate::leanh::lean_dec_ref(v_inst_1343_);
    return v_res_1346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
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
pub unsafe fn initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray_Split(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Mem(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
}

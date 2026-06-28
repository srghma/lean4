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
    lean_array_to_list, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_lt,
    lean_nat_sub,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
    lean_unsigned_to_nat,
};
pub static l_Lean_PersistentHashMap_instIterator___closed__0_value: LeanClosureObject<0> =
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
        m_fun: l_Lean_PersistentHashMap_instIterator___lam__0 as *const core::ffi::c_void,
        m_arity: 1,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_PersistentHashMap_instIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_instIterator___closed__0_value) as *mut LeanObject;
pub static l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value: LeanArrayObject<0> =
    LeanArrayObject {
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
static mut l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(
    mut v_x_674_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_674_) {
        0 => {
            let mut v___x_675_: *mut LeanObject = core::ptr::null_mut();
            v___x_675_ = lean_unsigned_to_nat(0);
            return v___x_675_;
        }
        1 => {
            let mut v___x_676_: *mut LeanObject = core::ptr::null_mut();
            v___x_676_ = lean_unsigned_to_nat(1);
            return v___x_676_;
        }
        _ => {
            let mut v___x_677_: *mut LeanObject = core::ptr::null_mut();
            v___x_677_ = lean_unsigned_to_nat(2);
            return v___x_677_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg___boxed(
    mut v_x_678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_679_: *mut LeanObject = core::ptr::null_mut();
    v_res_679_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_678_);
    lean_dec(v_x_678_);
    return v_res_679_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx(
    mut v_00_u03b1_680_: *mut LeanObject,
    mut v_00_u03b2_681_: *mut LeanObject,
    mut v_x_682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_683_: *mut LeanObject = core::ptr::null_mut();
    v___x_683_ = l_Lean_PersistentHashMap_Zipper_ctorIdx___redArg(v_x_682_);
    return v___x_683_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorIdx___boxed(
    mut v_00_u03b1_684_: *mut LeanObject,
    mut v_00_u03b2_685_: *mut LeanObject,
    mut v_x_686_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_687_: *mut LeanObject = core::ptr::null_mut();
    v_res_687_ =
        l_Lean_PersistentHashMap_Zipper_ctorIdx(v_00_u03b1_684_, v_00_u03b2_685_, v_x_686_);
    lean_dec(v_x_686_);
    return v_res_687_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(
    mut v_t_688_: *mut LeanObject,
    mut v_k_689_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_t_688_) {
        0 => {
            return v_k_689_;
        }
        1 => {
            let mut v_a_690_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_691_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_692_: *mut LeanObject = core::ptr::null_mut();
            v_a_690_ = lean_ctor_get(v_t_688_, 0);
            lean_inc_ref(v_a_690_);
            v_a_691_ = lean_ctor_get(v_t_688_, 1);
            lean_inc(v_a_691_);
            lean_dec_ref_known(v_t_688_, 2);
            v___x_692_ = lean_apply_2(v_k_689_, v_a_690_, v_a_691_);
            return v___x_692_;
        }
        _ => {
            let mut v_keys_693_: *mut LeanObject = core::ptr::null_mut();
            let mut v_vals_694_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_695_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_696_: *mut LeanObject = core::ptr::null_mut();
            v_keys_693_ = lean_ctor_get(v_t_688_, 0);
            lean_inc_ref(v_keys_693_);
            v_vals_694_ = lean_ctor_get(v_t_688_, 1);
            lean_inc_ref(v_vals_694_);
            v_a_695_ = lean_ctor_get(v_t_688_, 2);
            lean_inc(v_a_695_);
            lean_dec_ref_known(v_t_688_, 3);
            v___x_696_ = lean_apply_4(v_k_689_, v_keys_693_, v_vals_694_, lean_box(0), v_a_695_);
            return v___x_696_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim(
    mut v_00_u03b1_697_: *mut LeanObject,
    mut v_00_u03b2_698_: *mut LeanObject,
    mut v_motive_699_: *mut LeanObject,
    mut v_ctorIdx_700_: *mut LeanObject,
    mut v_t_701_: *mut LeanObject,
    mut v_h_702_: *mut LeanObject,
    mut v_k_703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_704_: *mut LeanObject = core::ptr::null_mut();
    v___x_704_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_701_, v_k_703_);
    return v___x_704_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_ctorElim___boxed(
    mut v_00_u03b1_705_: *mut LeanObject,
    mut v_00_u03b2_706_: *mut LeanObject,
    mut v_motive_707_: *mut LeanObject,
    mut v_ctorIdx_708_: *mut LeanObject,
    mut v_t_709_: *mut LeanObject,
    mut v_h_710_: *mut LeanObject,
    mut v_k_711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_712_: *mut LeanObject = core::ptr::null_mut();
    v_res_712_ = l_Lean_PersistentHashMap_Zipper_ctorElim(
        v_00_u03b1_705_,
        v_00_u03b2_706_,
        v_motive_707_,
        v_ctorIdx_708_,
        v_t_709_,
        v_h_710_,
        v_k_711_,
    );
    lean_dec(v_ctorIdx_708_);
    return v_res_712_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_done_elim___redArg(
    mut v_t_713_: *mut LeanObject,
    mut v_done_714_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_715_: *mut LeanObject = core::ptr::null_mut();
    v___x_715_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_713_, v_done_714_);
    return v___x_715_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_done_elim(
    mut v_00_u03b1_716_: *mut LeanObject,
    mut v_00_u03b2_717_: *mut LeanObject,
    mut v_motive_718_: *mut LeanObject,
    mut v_t_719_: *mut LeanObject,
    mut v_h_720_: *mut LeanObject,
    mut v_done_721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_722_: *mut LeanObject = core::ptr::null_mut();
    v___x_722_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_719_, v_done_721_);
    return v___x_722_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consEntries_elim___redArg(
    mut v_t_723_: *mut LeanObject,
    mut v_consEntries_724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_725_: *mut LeanObject = core::ptr::null_mut();
    v___x_725_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_723_, v_consEntries_724_);
    return v___x_725_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consEntries_elim(
    mut v_00_u03b1_726_: *mut LeanObject,
    mut v_00_u03b2_727_: *mut LeanObject,
    mut v_motive_728_: *mut LeanObject,
    mut v_t_729_: *mut LeanObject,
    mut v_h_730_: *mut LeanObject,
    mut v_consEntries_731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_732_: *mut LeanObject = core::ptr::null_mut();
    v___x_732_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_729_, v_consEntries_731_);
    return v___x_732_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consCollision_elim___redArg(
    mut v_t_733_: *mut LeanObject,
    mut v_consCollision_734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_735_: *mut LeanObject = core::ptr::null_mut();
    v___x_735_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_733_, v_consCollision_734_);
    return v___x_735_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_consCollision_elim(
    mut v_00_u03b1_736_: *mut LeanObject,
    mut v_00_u03b2_737_: *mut LeanObject,
    mut v_motive_738_: *mut LeanObject,
    mut v_t_739_: *mut LeanObject,
    mut v_h_740_: *mut LeanObject,
    mut v_consCollision_741_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_742_: *mut LeanObject = core::ptr::null_mut();
    v___x_742_ = l_Lean_PersistentHashMap_Zipper_ctorElim___redArg(v_t_739_, v_consCollision_741_);
    return v___x_742_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_prependNode___redArg(
    mut v_node_743_: *mut LeanObject,
    mut v_z_744_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_node_743_) == 0 {
        let mut v_es_745_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_746_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_747_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_748_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_749_: *mut LeanObject = core::ptr::null_mut();
        v_es_745_ = lean_ctor_get(v_node_743_, 0);
        lean_inc_ref(v_es_745_);
        lean_dec_ref_known(v_node_743_, 1);
        v___x_746_ = lean_unsigned_to_nat(0);
        v___x_747_ = lean_array_get_size(v_es_745_);
        v___x_748_ = l_Array_toSubarray___redArg(v_es_745_, v___x_746_, v___x_747_);
        v___x_749_ = lean_alloc_ctor(1, 2, (0) as u32);
        lean_ctor_set(v___x_749_, 0, v___x_748_);
        lean_ctor_set(v___x_749_, 1, v_z_744_);
        return v___x_749_;
    } else {
        let mut v_ks_750_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_751_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_752_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_753_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_754_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_755_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_756_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_757_: *mut LeanObject = core::ptr::null_mut();
        v_ks_750_ = lean_ctor_get(v_node_743_, 0);
        lean_inc_ref(v_ks_750_);
        v_vs_751_ = lean_ctor_get(v_node_743_, 1);
        lean_inc_ref(v_vs_751_);
        lean_dec_ref_known(v_node_743_, 2);
        v___x_752_ = lean_unsigned_to_nat(0);
        v___x_753_ = lean_array_get_size(v_ks_750_);
        v___x_754_ = l_Array_toSubarray___redArg(v_ks_750_, v___x_752_, v___x_753_);
        v___x_755_ = lean_array_get_size(v_vs_751_);
        v___x_756_ = l_Array_toSubarray___redArg(v_vs_751_, v___x_752_, v___x_755_);
        v___x_757_ = lean_alloc_ctor(2, 3, (0) as u32);
        lean_ctor_set(v___x_757_, 0, v___x_754_);
        lean_ctor_set(v___x_757_, 1, v___x_756_);
        lean_ctor_set(v___x_757_, 2, v_z_744_);
        return v___x_757_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_prependNode(
    mut v_00_u03b1_758_: *mut LeanObject,
    mut v_00_u03b2_759_: *mut LeanObject,
    mut v_node_760_: *mut LeanObject,
    mut v_z_761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_762_: *mut LeanObject = core::ptr::null_mut();
    v___x_762_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_760_, v_z_761_);
    return v___x_762_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_step___redArg(
    mut v_it_763_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_769_: u8 = 0;
    let mut v_start_770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_774_: u8 = 0;
    let mut v___x_775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_z_779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_785_: u8 = 0;
    let mut v___x_787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_790_: u8 = 0;
    let mut v_node_791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_794_: u8 = 0;
    let mut v___x_795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_799_: u8 = 0;
    let mut v___x_800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_802_: u8 = 0;
    let mut v_vals_803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_808_: u8 = 0;
    let mut v_start_809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_825_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_it_763_) {
                0 => {
                    v___x_764_ = lean_box(2);
                    return v___x_764_;
                }
                1 => {
                    v_a_765_ = lean_ctor_get(v_it_763_, 0);
                    v_a_766_ = lean_ctor_get(v_it_763_, 1);
                    v_isSharedCheck_802_ = (!lean_is_exclusive(v_it_763_)) as u8;
                    if v_isSharedCheck_802_ == 0 {
                        v___x_768_ = v_it_763_;
                        v_isShared_769_ = v_isSharedCheck_802_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_766_);
                        lean_inc(v_a_765_);
                        lean_dec(v_it_763_);
                        v___x_768_ = lean_box(0);
                        v_isShared_769_ = v_isSharedCheck_802_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_803_ = lean_ctor_get(v_it_763_, 1);
                    v_keys_804_ = lean_ctor_get(v_it_763_, 0);
                    v_a_805_ = lean_ctor_get(v_it_763_, 2);
                    v_isSharedCheck_825_ = (!lean_is_exclusive(v_it_763_)) as u8;
                    if v_isSharedCheck_825_ == 0 {
                        v___x_807_ = v_it_763_;
                        v_isShared_808_ = v_isSharedCheck_825_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_805_);
                        lean_inc(v_vals_803_);
                        lean_inc(v_keys_804_);
                        lean_dec(v_it_763_);
                        v___x_807_ = lean_box(0);
                        v_isShared_808_ = v_isSharedCheck_825_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_770_ = lean_ctor_get(v_a_765_, 1);
                v_stop_771_ = lean_ctor_get(v_a_765_, 2);
                v___x_772_ = lean_unsigned_to_nat(0);
                v___x_773_ = lean_nat_sub(v_stop_771_, v_start_770_);
                v___x_774_ = lean_nat_dec_lt(v___x_772_, v___x_773_);
                lean_dec(v___x_773_);
                if v___x_774_ == 0 {
                    lean_del_object(v___x_768_);
                    lean_dec_ref(v_a_765_);
                    v___x_775_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_775_, 0, v_a_766_);
                    return v___x_775_;
                } else {
                    v___x_776_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_a_765_);
                    v___x_777_ = l_Subarray_drop___redArg(v_a_765_, v___x_776_);
                    if v_isShared_769_ == 0 {
                        lean_ctor_set(v___x_768_, 0, v___x_777_);
                        v_z_779_ = v___x_768_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_801_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_801_, 0, v___x_777_);
                        lean_ctor_set(v_reuseFailAlloc_801_, 1, v_a_766_);
                        v_z_779_ = v_reuseFailAlloc_801_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_780_ = l_Subarray_get___redArg(v_a_765_, v___x_772_);
                lean_dec_ref(v_a_765_);
                match lean_obj_tag(v___x_780_) {
                    0 => {
                        v_key_781_ = lean_ctor_get(v___x_780_, 0);
                        v_val_782_ = lean_ctor_get(v___x_780_, 1);
                        v_isSharedCheck_790_ = (!lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_790_ == 0 {
                            v___x_784_ = v___x_780_;
                            v_isShared_785_ = v_isSharedCheck_790_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_782_);
                            lean_inc(v_key_781_);
                            lean_dec(v___x_780_);
                            v___x_784_ = lean_box(0);
                            v_isShared_785_ = v_isSharedCheck_790_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_791_ = lean_ctor_get(v___x_780_, 0);
                        v_isSharedCheck_799_ = (!lean_is_exclusive(v___x_780_)) as u8;
                        if v_isSharedCheck_799_ == 0 {
                            v___x_793_ = v___x_780_;
                            v_isShared_794_ = v_isSharedCheck_799_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_node_791_);
                            lean_dec(v___x_780_);
                            v___x_793_ = lean_box(0);
                            v_isShared_794_ = v_isSharedCheck_799_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_800_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_800_, 0, v_z_779_);
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
                    v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_789_, 0, v_key_781_);
                    lean_ctor_set(v_reuseFailAlloc_789_, 1, v_val_782_);
                    v___x_787_ = v_reuseFailAlloc_789_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_788_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_788_, 0, v_z_779_);
                lean_ctor_set(v___x_788_, 1, v___x_787_);
                return v___x_788_;
            }
            5 => {
                v___x_795_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_791_, v_z_779_);
                if v_isShared_794_ == 0 {
                    lean_ctor_set(v___x_793_, 0, v___x_795_);
                    v___x_797_ = v___x_793_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_798_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_798_, 0, v___x_795_);
                    v___x_797_ = v_reuseFailAlloc_798_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_797_;
            }
            7 => {
                v_start_809_ = lean_ctor_get(v_vals_803_, 1);
                v_stop_810_ = lean_ctor_get(v_vals_803_, 2);
                v___x_811_ = lean_unsigned_to_nat(0);
                v___x_812_ = lean_nat_sub(v_stop_810_, v_start_809_);
                v___x_813_ = lean_nat_dec_lt(v___x_811_, v___x_812_);
                lean_dec(v___x_812_);
                if v___x_813_ == 0 {
                    lean_del_object(v___x_807_);
                    lean_dec_ref(v_keys_804_);
                    lean_dec_ref(v_vals_803_);
                    v___x_814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_814_, 0, v_a_805_);
                    return v___x_814_;
                } else {
                    v___x_815_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_keys_804_);
                    v___x_816_ = l_Subarray_drop___redArg(v_keys_804_, v___x_815_);
                    lean_inc_ref(v_vals_803_);
                    v___x_817_ = l_Subarray_drop___redArg(v_vals_803_, v___x_815_);
                    if v_isShared_808_ == 0 {
                        lean_ctor_set(v___x_807_, 1, v___x_817_);
                        lean_ctor_set(v___x_807_, 0, v___x_816_);
                        v___x_819_ = v___x_807_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_824_ = lean_alloc_ctor(2, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_824_, 0, v___x_816_);
                        lean_ctor_set(v_reuseFailAlloc_824_, 1, v___x_817_);
                        lean_ctor_set(v_reuseFailAlloc_824_, 2, v_a_805_);
                        v___x_819_ = v_reuseFailAlloc_824_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_820_ = l_Subarray_get___redArg(v_keys_804_, v___x_811_);
                lean_dec_ref(v_keys_804_);
                v___x_821_ = l_Subarray_get___redArg(v_vals_803_, v___x_811_);
                lean_dec_ref(v_vals_803_);
                v___x_822_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_822_, 0, v___x_820_);
                lean_ctor_set(v___x_822_, 1, v___x_821_);
                v___x_823_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_823_, 0, v___x_819_);
                lean_ctor_set(v___x_823_, 1, v___x_822_);
                return v___x_823_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_step(
    mut v_00_u03b1_826_: *mut LeanObject,
    mut v_00_u03b2_827_: *mut LeanObject,
    mut v_it_828_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_834_: u8 = 0;
    let mut v_start_835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_839_: u8 = 0;
    let mut v___x_840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_z_844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_850_: u8 = 0;
    let mut v___x_852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_855_: u8 = 0;
    let mut v_node_856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_859_: u8 = 0;
    let mut v___x_860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_862_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_864_: u8 = 0;
    let mut v___x_865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_867_: u8 = 0;
    let mut v_vals_868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_873_: u8 = 0;
    let mut v_start_874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_878_: u8 = 0;
    let mut v___x_879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_890_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_it_828_) {
                0 => {
                    v___x_829_ = lean_box(2);
                    return v___x_829_;
                }
                1 => {
                    v_a_830_ = lean_ctor_get(v_it_828_, 0);
                    v_a_831_ = lean_ctor_get(v_it_828_, 1);
                    v_isSharedCheck_867_ = (!lean_is_exclusive(v_it_828_)) as u8;
                    if v_isSharedCheck_867_ == 0 {
                        v___x_833_ = v_it_828_;
                        v_isShared_834_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_831_);
                        lean_inc(v_a_830_);
                        lean_dec(v_it_828_);
                        v___x_833_ = lean_box(0);
                        v_isShared_834_ = v_isSharedCheck_867_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_868_ = lean_ctor_get(v_it_828_, 1);
                    v_keys_869_ = lean_ctor_get(v_it_828_, 0);
                    v_a_870_ = lean_ctor_get(v_it_828_, 2);
                    v_isSharedCheck_890_ = (!lean_is_exclusive(v_it_828_)) as u8;
                    if v_isSharedCheck_890_ == 0 {
                        v___x_872_ = v_it_828_;
                        v_isShared_873_ = v_isSharedCheck_890_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_870_);
                        lean_inc(v_vals_868_);
                        lean_inc(v_keys_869_);
                        lean_dec(v_it_828_);
                        v___x_872_ = lean_box(0);
                        v_isShared_873_ = v_isSharedCheck_890_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_835_ = lean_ctor_get(v_a_830_, 1);
                v_stop_836_ = lean_ctor_get(v_a_830_, 2);
                v___x_837_ = lean_unsigned_to_nat(0);
                v___x_838_ = lean_nat_sub(v_stop_836_, v_start_835_);
                v___x_839_ = lean_nat_dec_lt(v___x_837_, v___x_838_);
                lean_dec(v___x_838_);
                if v___x_839_ == 0 {
                    lean_del_object(v___x_833_);
                    lean_dec_ref(v_a_830_);
                    v___x_840_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_840_, 0, v_a_831_);
                    return v___x_840_;
                } else {
                    v___x_841_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_a_830_);
                    v___x_842_ = l_Subarray_drop___redArg(v_a_830_, v___x_841_);
                    if v_isShared_834_ == 0 {
                        lean_ctor_set(v___x_833_, 0, v___x_842_);
                        v_z_844_ = v___x_833_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_866_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_866_, 0, v___x_842_);
                        lean_ctor_set(v_reuseFailAlloc_866_, 1, v_a_831_);
                        v_z_844_ = v_reuseFailAlloc_866_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_845_ = l_Subarray_get___redArg(v_a_830_, v___x_837_);
                lean_dec_ref(v_a_830_);
                match lean_obj_tag(v___x_845_) {
                    0 => {
                        v_key_846_ = lean_ctor_get(v___x_845_, 0);
                        v_val_847_ = lean_ctor_get(v___x_845_, 1);
                        v_isSharedCheck_855_ = (!lean_is_exclusive(v___x_845_)) as u8;
                        if v_isSharedCheck_855_ == 0 {
                            v___x_849_ = v___x_845_;
                            v_isShared_850_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_847_);
                            lean_inc(v_key_846_);
                            lean_dec(v___x_845_);
                            v___x_849_ = lean_box(0);
                            v_isShared_850_ = v_isSharedCheck_855_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_856_ = lean_ctor_get(v___x_845_, 0);
                        v_isSharedCheck_864_ = (!lean_is_exclusive(v___x_845_)) as u8;
                        if v_isSharedCheck_864_ == 0 {
                            v___x_858_ = v___x_845_;
                            v_isShared_859_ = v_isSharedCheck_864_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_node_856_);
                            lean_dec(v___x_845_);
                            v___x_858_ = lean_box(0);
                            v_isShared_859_ = v_isSharedCheck_864_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_865_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_865_, 0, v_z_844_);
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
                    v_reuseFailAlloc_854_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_854_, 0, v_key_846_);
                    lean_ctor_set(v_reuseFailAlloc_854_, 1, v_val_847_);
                    v___x_852_ = v_reuseFailAlloc_854_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_853_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_853_, 0, v_z_844_);
                lean_ctor_set(v___x_853_, 1, v___x_852_);
                return v___x_853_;
            }
            5 => {
                v___x_860_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_856_, v_z_844_);
                if v_isShared_859_ == 0 {
                    lean_ctor_set(v___x_858_, 0, v___x_860_);
                    v___x_862_ = v___x_858_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_863_, 0, v___x_860_);
                    v___x_862_ = v_reuseFailAlloc_863_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_862_;
            }
            7 => {
                v_start_874_ = lean_ctor_get(v_vals_868_, 1);
                v_stop_875_ = lean_ctor_get(v_vals_868_, 2);
                v___x_876_ = lean_unsigned_to_nat(0);
                v___x_877_ = lean_nat_sub(v_stop_875_, v_start_874_);
                v___x_878_ = lean_nat_dec_lt(v___x_876_, v___x_877_);
                lean_dec(v___x_877_);
                if v___x_878_ == 0 {
                    lean_del_object(v___x_872_);
                    lean_dec_ref(v_keys_869_);
                    lean_dec_ref(v_vals_868_);
                    v___x_879_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_879_, 0, v_a_870_);
                    return v___x_879_;
                } else {
                    v___x_880_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_keys_869_);
                    v___x_881_ = l_Subarray_drop___redArg(v_keys_869_, v___x_880_);
                    lean_inc_ref(v_vals_868_);
                    v___x_882_ = l_Subarray_drop___redArg(v_vals_868_, v___x_880_);
                    if v_isShared_873_ == 0 {
                        lean_ctor_set(v___x_872_, 1, v___x_882_);
                        lean_ctor_set(v___x_872_, 0, v___x_881_);
                        v___x_884_ = v___x_872_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_889_ = lean_alloc_ctor(2, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_889_, 0, v___x_881_);
                        lean_ctor_set(v_reuseFailAlloc_889_, 1, v___x_882_);
                        lean_ctor_set(v_reuseFailAlloc_889_, 2, v_a_870_);
                        v___x_884_ = v_reuseFailAlloc_889_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_885_ = l_Subarray_get___redArg(v_keys_869_, v___x_876_);
                lean_dec_ref(v_keys_869_);
                v___x_886_ = l_Subarray_get___redArg(v_vals_868_, v___x_876_);
                lean_dec_ref(v_vals_868_);
                v___x_887_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_887_, 0, v___x_885_);
                lean_ctor_set(v___x_887_, 1, v___x_886_);
                v___x_888_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_888_, 0, v___x_884_);
                lean_ctor_set(v___x_888_, 1, v___x_887_);
                return v___x_888_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIterator___lam__0(
    mut v_it_891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v_start_898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_902_: u8 = 0;
    let mut v___x_903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_z_907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_913_: u8 = 0;
    let mut v___x_915_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_918_: u8 = 0;
    let mut v_node_919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_922_: u8 = 0;
    let mut v___x_923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_927_: u8 = 0;
    let mut v___x_928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_930_: u8 = 0;
    let mut v_vals_931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_936_: u8 = 0;
    let mut v_start_937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_941_: u8 = 0;
    let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_953_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_it_891_) {
                0 => {
                    v___x_892_ = lean_box(2);
                    return v___x_892_;
                }
                1 => {
                    v_a_893_ = lean_ctor_get(v_it_891_, 0);
                    v_a_894_ = lean_ctor_get(v_it_891_, 1);
                    v_isSharedCheck_930_ = (!lean_is_exclusive(v_it_891_)) as u8;
                    if v_isSharedCheck_930_ == 0 {
                        v___x_896_ = v_it_891_;
                        v_isShared_897_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_894_);
                        lean_inc(v_a_893_);
                        lean_dec(v_it_891_);
                        v___x_896_ = lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_930_;
                        state = 1;
                        continue;
                    }
                }
                _ => {
                    v_vals_931_ = lean_ctor_get(v_it_891_, 1);
                    v_keys_932_ = lean_ctor_get(v_it_891_, 0);
                    v_a_933_ = lean_ctor_get(v_it_891_, 2);
                    v_isSharedCheck_953_ = (!lean_is_exclusive(v_it_891_)) as u8;
                    if v_isSharedCheck_953_ == 0 {
                        v___x_935_ = v_it_891_;
                        v_isShared_936_ = v_isSharedCheck_953_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_933_);
                        lean_inc(v_vals_931_);
                        lean_inc(v_keys_932_);
                        lean_dec(v_it_891_);
                        v___x_935_ = lean_box(0);
                        v_isShared_936_ = v_isSharedCheck_953_;
                        state = 7;
                        continue;
                    }
                }
            },
            1 => {
                v_start_898_ = lean_ctor_get(v_a_893_, 1);
                v_stop_899_ = lean_ctor_get(v_a_893_, 2);
                v___x_900_ = lean_unsigned_to_nat(0);
                v___x_901_ = lean_nat_sub(v_stop_899_, v_start_898_);
                v___x_902_ = lean_nat_dec_lt(v___x_900_, v___x_901_);
                lean_dec(v___x_901_);
                if v___x_902_ == 0 {
                    lean_del_object(v___x_896_);
                    lean_dec_ref(v_a_893_);
                    v___x_903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_903_, 0, v_a_894_);
                    return v___x_903_;
                } else {
                    v___x_904_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_a_893_);
                    v___x_905_ = l_Subarray_drop___redArg(v_a_893_, v___x_904_);
                    if v_isShared_897_ == 0 {
                        lean_ctor_set(v___x_896_, 0, v___x_905_);
                        v_z_907_ = v___x_896_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_929_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_929_, 0, v___x_905_);
                        lean_ctor_set(v_reuseFailAlloc_929_, 1, v_a_894_);
                        v_z_907_ = v_reuseFailAlloc_929_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_908_ = l_Subarray_get___redArg(v_a_893_, v___x_900_);
                lean_dec_ref(v_a_893_);
                match lean_obj_tag(v___x_908_) {
                    0 => {
                        v_key_909_ = lean_ctor_get(v___x_908_, 0);
                        v_val_910_ = lean_ctor_get(v___x_908_, 1);
                        v_isSharedCheck_918_ = (!lean_is_exclusive(v___x_908_)) as u8;
                        if v_isSharedCheck_918_ == 0 {
                            v___x_912_ = v___x_908_;
                            v_isShared_913_ = v_isSharedCheck_918_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_910_);
                            lean_inc(v_key_909_);
                            lean_dec(v___x_908_);
                            v___x_912_ = lean_box(0);
                            v_isShared_913_ = v_isSharedCheck_918_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_919_ = lean_ctor_get(v___x_908_, 0);
                        v_isSharedCheck_927_ = (!lean_is_exclusive(v___x_908_)) as u8;
                        if v_isSharedCheck_927_ == 0 {
                            v___x_921_ = v___x_908_;
                            v_isShared_922_ = v_isSharedCheck_927_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_node_919_);
                            lean_dec(v___x_908_);
                            v___x_921_ = lean_box(0);
                            v_isShared_922_ = v_isSharedCheck_927_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_928_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_928_, 0, v_z_907_);
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
                    v_reuseFailAlloc_917_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_917_, 0, v_key_909_);
                    lean_ctor_set(v_reuseFailAlloc_917_, 1, v_val_910_);
                    v___x_915_ = v_reuseFailAlloc_917_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_916_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_916_, 0, v_z_907_);
                lean_ctor_set(v___x_916_, 1, v___x_915_);
                return v___x_916_;
            }
            5 => {
                v___x_923_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_919_, v_z_907_);
                if v_isShared_922_ == 0 {
                    lean_ctor_set(v___x_921_, 0, v___x_923_);
                    v___x_925_ = v___x_921_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_926_, 0, v___x_923_);
                    v___x_925_ = v_reuseFailAlloc_926_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_925_;
            }
            7 => {
                v_start_937_ = lean_ctor_get(v_vals_931_, 1);
                v_stop_938_ = lean_ctor_get(v_vals_931_, 2);
                v___x_939_ = lean_unsigned_to_nat(0);
                v___x_940_ = lean_nat_sub(v_stop_938_, v_start_937_);
                v___x_941_ = lean_nat_dec_lt(v___x_939_, v___x_940_);
                lean_dec(v___x_940_);
                if v___x_941_ == 0 {
                    lean_del_object(v___x_935_);
                    lean_dec_ref(v_keys_932_);
                    lean_dec_ref(v_vals_931_);
                    v___x_942_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_942_, 0, v_a_933_);
                    return v___x_942_;
                } else {
                    v___x_943_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_keys_932_);
                    v___x_944_ = l_Subarray_drop___redArg(v_keys_932_, v___x_943_);
                    lean_inc_ref(v_vals_931_);
                    v___x_945_ = l_Subarray_drop___redArg(v_vals_931_, v___x_943_);
                    if v_isShared_936_ == 0 {
                        lean_ctor_set(v___x_935_, 1, v___x_945_);
                        lean_ctor_set(v___x_935_, 0, v___x_944_);
                        v___x_947_ = v___x_935_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_952_ = lean_alloc_ctor(2, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_944_);
                        lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_945_);
                        lean_ctor_set(v_reuseFailAlloc_952_, 2, v_a_933_);
                        v___x_947_ = v_reuseFailAlloc_952_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_948_ = l_Subarray_get___redArg(v_keys_932_, v___x_939_);
                lean_dec_ref(v_keys_932_);
                v___x_949_ = l_Subarray_get___redArg(v_vals_931_, v___x_939_);
                lean_dec_ref(v_vals_931_);
                v___x_950_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_950_, 0, v___x_948_);
                lean_ctor_set(v___x_950_, 1, v___x_949_);
                v___x_951_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_951_, 0, v___x_947_);
                lean_ctor_set(v___x_951_, 1, v___x_950_);
                return v___x_951_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIterator(
    mut v_00_u03b1_955_: *mut LeanObject,
    mut v_00_u03b2_956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_957_: *mut LeanObject = core::ptr::null_mut();
    v___f_957_ = l_Lean_PersistentHashMap_instIterator___closed__0;
    return v___f_957_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(
    mut v_es_958_: *mut LeanObject,
    mut v_i_959_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_967_: u8 = 0;
    let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_970_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_974_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_966_ = lean_array_get_size(v_es_958_);
                v___x_967_ = lean_nat_dec_lt(v_i_959_, v___x_966_);
                if v___x_967_ == 0 {
                    v___x_968_ = lean_unsigned_to_nat(0);
                    return v___x_968_;
                } else {
                    v___x_969_ = lean_array_fget_borrowed(v_es_958_, v_i_959_);
                    if lean_obj_tag(v___x_969_) == 1 {
                        v_node_970_ = lean_ctor_get(v___x_969_, 0);
                        v___x_971_ = lean_unsigned_to_nat(2);
                        v___x_972_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_970_);
                        v___x_973_ = lean_nat_add(v___x_971_, v___x_972_);
                        lean_dec(v___x_972_);
                        v___y_961_ = v___x_973_;
                        state = 1;
                        continue;
                    } else {
                        v___x_974_ = lean_unsigned_to_nat(1);
                        v___y_961_ = v___x_974_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_962_ = lean_unsigned_to_nat(1);
                v___x_963_ = lean_nat_add(v_i_959_, v___x_962_);
                v___x_964_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_958_, v___x_963_);
                lean_dec(v___x_963_);
                v___x_965_ = lean_nat_add(v___y_961_, v___x_964_);
                lean_dec(v___x_964_);
                lean_dec(v___y_961_);
                return v___x_965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___redArg(
    mut v_node_975_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_node_975_) == 0 {
        let mut v_es_976_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_977_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_978_: *mut LeanObject = core::ptr::null_mut();
        v_es_976_ = lean_ctor_get(v_node_975_, 0);
        v___x_977_ = lean_unsigned_to_nat(0);
        v___x_978_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_976_, v___x_977_);
        return v___x_978_;
    } else {
        let mut v_vs_979_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
        v_vs_979_ = lean_ctor_get(v_node_975_, 1);
        v___x_980_ = lean_array_get_size(v_vs_979_);
        return v___x_980_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___redArg___boxed(
    mut v_node_981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_982_: *mut LeanObject = core::ptr::null_mut();
    v_res_982_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_981_);
    lean_dec_ref(v_node_981_);
    return v_res_982_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg___boxed(
    mut v_es_983_: *mut LeanObject,
    mut v_i_984_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_985_: *mut LeanObject = core::ptr::null_mut();
    v_res_985_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_983_, v_i_984_);
    lean_dec(v_i_984_);
    lean_dec_ref(v_es_983_);
    return v_res_985_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(
    mut v_00_u03b1_986_: *mut LeanObject,
    mut v_00_u03b2_987_: *mut LeanObject,
    mut v_es_988_: *mut LeanObject,
    mut v_i_989_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_990_: *mut LeanObject = core::ptr::null_mut();
    v___x_990_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___redArg(v_es_988_, v_i_989_);
    return v___x_990_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries___boxed(
    mut v_00_u03b1_991_: *mut LeanObject,
    mut v_00_u03b2_992_: *mut LeanObject,
    mut v_es_993_: *mut LeanObject,
    mut v_i_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_995_: *mut LeanObject = core::ptr::null_mut();
    v_res_995_ = l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_measureEntries(v_00_u03b1_991_, v_00_u03b2_992_, v_es_993_, v_i_994_);
    lean_dec(v_i_994_);
    lean_dec_ref(v_es_993_);
    return v_res_995_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure(
    mut v_00_u03b1_996_: *mut LeanObject,
    mut v_00_u03b2_997_: *mut LeanObject,
    mut v_node_998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    v___x_999_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_998_);
    return v___x_999_;
}
pub unsafe fn l_Lean_PersistentHashMap_Node_measure___boxed(
    mut v_00_u03b1_1000_: *mut LeanObject,
    mut v_00_u03b2_1001_: *mut LeanObject,
    mut v_node_1002_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1003_: *mut LeanObject = core::ptr::null_mut();
    v_res_1003_ =
        l_Lean_PersistentHashMap_Node_measure(v_00_u03b1_1000_, v_00_u03b2_1001_, v_node_1002_);
    lean_dec_ref(v_node_1002_);
    return v_res_1003_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter___redArg(
    mut v_x_1004_: *mut LeanObject,
    mut v_h__1_1005_: *mut LeanObject,
    mut v_h__2_1006_: *mut LeanObject,
    mut v_h__3_1007_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1004_) {
        0 => {
            let mut v_key_1008_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1009_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1010_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1007_);
            lean_dec(v_h__1_1005_);
            v_key_1008_ = lean_ctor_get(v_x_1004_, 0);
            lean_inc(v_key_1008_);
            v_val_1009_ = lean_ctor_get(v_x_1004_, 1);
            lean_inc(v_val_1009_);
            lean_dec_ref_known(v_x_1004_, 2);
            v___x_1010_ = lean_apply_3(v_h__2_1006_, v_key_1008_, v_val_1009_, lean_box(0));
            return v___x_1010_;
        }
        1 => {
            let mut v_node_1011_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1012_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1006_);
            lean_dec(v_h__1_1005_);
            v_node_1011_ = lean_ctor_get(v_x_1004_, 0);
            lean_inc(v_node_1011_);
            lean_dec_ref_known(v_x_1004_, 1);
            v___x_1012_ = lean_apply_2(v_h__3_1007_, v_node_1011_, lean_box(0));
            return v___x_1012_;
        }
        _ => {
            let mut v___x_1013_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1007_);
            lean_dec(v_h__2_1006_);
            v___x_1013_ = lean_apply_1(v_h__1_1005_, lean_box(0));
            return v___x_1013_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Node_measure_match__1_splitter(
    mut v_00_u03b1_1014_: *mut LeanObject,
    mut v_00_u03b2_1015_: *mut LeanObject,
    mut v_motive_1016_: *mut LeanObject,
    mut v_x_1017_: *mut LeanObject,
    mut v_h__1_1018_: *mut LeanObject,
    mut v_h__2_1019_: *mut LeanObject,
    mut v_h__3_1020_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1017_) {
        0 => {
            let mut v_key_1021_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1022_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1023_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1020_);
            lean_dec(v_h__1_1018_);
            v_key_1021_ = lean_ctor_get(v_x_1017_, 0);
            lean_inc(v_key_1021_);
            v_val_1022_ = lean_ctor_get(v_x_1017_, 1);
            lean_inc(v_val_1022_);
            lean_dec_ref_known(v_x_1017_, 2);
            v___x_1023_ = lean_apply_3(v_h__2_1019_, v_key_1021_, v_val_1022_, lean_box(0));
            return v___x_1023_;
        }
        1 => {
            let mut v_node_1024_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1025_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1019_);
            lean_dec(v_h__1_1018_);
            v_node_1024_ = lean_ctor_get(v_x_1017_, 0);
            lean_inc(v_node_1024_);
            lean_dec_ref_known(v_x_1017_, 1);
            v___x_1025_ = lean_apply_2(v_h__3_1020_, v_node_1024_, lean_box(0));
            return v___x_1025_;
        }
        _ => {
            let mut v___x_1026_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1020_);
            lean_dec(v_h__2_1019_);
            v___x_1026_ = lean_apply_1(v_h__1_1018_, lean_box(0));
            return v___x_1026_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter___redArg(
    mut v_node_1027_: *mut LeanObject,
    mut v_h__1_1028_: *mut LeanObject,
    mut v_h__2_1029_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_node_1027_) == 0 {
        let mut v_es_1030_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1031_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1029_);
        v_es_1030_ = lean_ctor_get(v_node_1027_, 0);
        lean_inc_ref(v_es_1030_);
        lean_dec_ref_known(v_node_1027_, 1);
        v___x_1031_ = lean_apply_1(v_h__1_1028_, v_es_1030_);
        return v___x_1031_;
    } else {
        let mut v_ks_1032_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_1033_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1028_);
        v_ks_1032_ = lean_ctor_get(v_node_1027_, 0);
        lean_inc_ref(v_ks_1032_);
        v_vs_1033_ = lean_ctor_get(v_node_1027_, 1);
        lean_inc_ref(v_vs_1033_);
        lean_dec_ref_known(v_node_1027_, 2);
        v___x_1034_ = lean_apply_3(v_h__2_1029_, v_ks_1032_, v_vs_1033_, lean_box(0));
        return v___x_1034_;
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_prependNode_match__1_splitter(
    mut v_00_u03b1_1035_: *mut LeanObject,
    mut v_00_u03b2_1036_: *mut LeanObject,
    mut v_motive_1037_: *mut LeanObject,
    mut v_node_1038_: *mut LeanObject,
    mut v_h__1_1039_: *mut LeanObject,
    mut v_h__2_1040_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_node_1038_) == 0 {
        let mut v_es_1041_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1042_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_1040_);
        v_es_1041_ = lean_ctor_get(v_node_1038_, 0);
        lean_inc_ref(v_es_1041_);
        lean_dec_ref_known(v_node_1038_, 1);
        v___x_1042_ = lean_apply_1(v_h__1_1039_, v_es_1041_);
        return v___x_1042_;
    } else {
        let mut v_ks_1043_: *mut LeanObject = core::ptr::null_mut();
        let mut v_vs_1044_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1045_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_1039_);
        v_ks_1043_ = lean_ctor_get(v_node_1038_, 0);
        lean_inc_ref(v_ks_1043_);
        v_vs_1044_ = lean_ctor_get(v_node_1038_, 1);
        lean_inc_ref(v_vs_1044_);
        lean_dec_ref_known(v_node_1038_, 2);
        v___x_1045_ = lean_apply_3(v_h__2_1040_, v_ks_1043_, v_vs_1044_, lean_box(0));
        return v___x_1045_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___redArg(
    mut v_entry_1046_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_entry_1046_) == 1 {
        let mut v_node_1047_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1049_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1050_: *mut LeanObject = core::ptr::null_mut();
        v_node_1047_ = lean_ctor_get(v_entry_1046_, 0);
        v___x_1048_ = lean_unsigned_to_nat(2);
        v___x_1049_ = l_Lean_PersistentHashMap_Node_measure___redArg(v_node_1047_);
        v___x_1050_ = lean_nat_add(v___x_1048_, v___x_1049_);
        lean_dec(v___x_1049_);
        return v___x_1050_;
    } else {
        let mut v___x_1051_: *mut LeanObject = core::ptr::null_mut();
        v___x_1051_ = lean_unsigned_to_nat(1);
        return v___x_1051_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___redArg___boxed(
    mut v_entry_1052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1053_: *mut LeanObject = core::ptr::null_mut();
    v_res_1053_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_1052_);
    lean_dec(v_entry_1052_);
    return v_res_1053_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure(
    mut v_00_u03b1_1054_: *mut LeanObject,
    mut v_00_u03b2_1055_: *mut LeanObject,
    mut v_entry_1056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    v___x_1057_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_entry_1056_);
    return v___x_1057_;
}
pub unsafe fn l_Lean_PersistentHashMap_Entry_measure___boxed(
    mut v_00_u03b1_1058_: *mut LeanObject,
    mut v_00_u03b2_1059_: *mut LeanObject,
    mut v_entry_1060_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1061_: *mut LeanObject = core::ptr::null_mut();
    v_res_1061_ =
        l_Lean_PersistentHashMap_Entry_measure(v_00_u03b1_1058_, v_00_u03b2_1059_, v_entry_1060_);
    lean_dec(v_entry_1060_);
    return v_res_1061_;
}
pub unsafe fn l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(
    mut v_init_1062_: *mut LeanObject,
    mut v_x_1063_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_1063_) == 0 {
        lean_inc(v_init_1062_);
        return v_init_1062_;
    } else {
        let mut v_head_1064_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_1065_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1066_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1067_: *mut LeanObject = core::ptr::null_mut();
        v_head_1064_ = lean_ctor_get(v_x_1063_, 0);
        v_tail_1065_ = lean_ctor_get(v_x_1063_, 1);
        v___x_1066_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_1062_, v_tail_1065_);
        v___x_1067_ = lean_nat_add(v_head_1064_, v___x_1066_);
        lean_dec(v___x_1066_);
        return v___x_1067_;
    }
}
pub unsafe fn l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2___boxed(
    mut v_init_1068_: *mut LeanObject,
    mut v_x_1069_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1070_: *mut LeanObject = core::ptr::null_mut();
    v_res_1070_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v_init_1068_, v_x_1069_);
    lean_dec(v_x_1069_);
    lean_dec(v_init_1068_);
    return v_res_1070_;
}
pub unsafe fn l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(
    mut v_l_1071_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut LeanObject = core::ptr::null_mut();
    v___x_1072_ = lean_unsigned_to_nat(0);
    v___x_1073_ = l_List_foldr___at___00List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2_spec__2(v___x_1072_, v_l_1071_);
    return v___x_1073_;
}
pub unsafe fn l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2___boxed(
    mut v_l_1074_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1075_: *mut LeanObject = core::ptr::null_mut();
    v_res_1075_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v_l_1074_);
    lean_dec(v_l_1074_);
    return v_res_1075_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
    mut v_a_1076_: *mut LeanObject,
    mut v_a_1077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_1079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_1080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1083_: u8 = 0;
    let mut v___x_1084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_1076_) == 0 {
                    v___x_1078_ = l_List_reverse___redArg(v_a_1077_);
                    return v___x_1078_;
                } else {
                    v_head_1079_ = lean_ctor_get(v_a_1076_, 0);
                    v_tail_1080_ = lean_ctor_get(v_a_1076_, 1);
                    v_isSharedCheck_1089_ = (!lean_is_exclusive(v_a_1076_)) as u8;
                    if v_isSharedCheck_1089_ == 0 {
                        v___x_1082_ = v_a_1076_;
                        v_isShared_1083_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_1080_);
                        lean_inc(v_head_1079_);
                        lean_dec(v_a_1076_);
                        v___x_1082_ = lean_box(0);
                        v_isShared_1083_ = v_isSharedCheck_1089_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1084_ = l_Lean_PersistentHashMap_Entry_measure___redArg(v_head_1079_);
                lean_dec(v_head_1079_);
                if v_isShared_1083_ == 0 {
                    lean_ctor_set(v___x_1082_, 1, v_a_1077_);
                    lean_ctor_set(v___x_1082_, 0, v___x_1084_);
                    v___x_1086_ = v___x_1082_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1088_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1088_, 0, v___x_1084_);
                    lean_ctor_set(v_reuseFailAlloc_1088_, 1, v_a_1077_);
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
    mut v_a_1090_: *mut LeanObject,
    mut v_b_1091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_1092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_1093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1097_: u8 = 0;
    let mut v___x_1098_: u8 = 0;
    let mut v___x_1099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1107_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_1092_ = lean_ctor_get(v_a_1090_, 0);
                v_start_1093_ = lean_ctor_get(v_a_1090_, 1);
                v_stop_1094_ = lean_ctor_get(v_a_1090_, 2);
                v_isSharedCheck_1107_ = (!lean_is_exclusive(v_a_1090_)) as u8;
                if v_isSharedCheck_1107_ == 0 {
                    v___x_1096_ = v_a_1090_;
                    v_isShared_1097_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_1094_);
                    lean_inc(v_start_1093_);
                    lean_inc(v_array_1092_);
                    lean_dec(v_a_1090_);
                    v___x_1096_ = lean_box(0);
                    v_isShared_1097_ = v_isSharedCheck_1107_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1098_ = lean_nat_dec_lt(v_start_1093_, v_stop_1094_);
                if v___x_1098_ == 0 {
                    lean_del_object(v___x_1096_);
                    lean_dec(v_stop_1094_);
                    lean_dec(v_start_1093_);
                    lean_dec_ref(v_array_1092_);
                    return v_b_1091_;
                } else {
                    v___x_1099_ = lean_unsigned_to_nat(1);
                    v___x_1100_ = lean_nat_add(v_start_1093_, v___x_1099_);
                    lean_inc_ref(v_array_1092_);
                    if v_isShared_1097_ == 0 {
                        lean_ctor_set(v___x_1096_, 1, v___x_1100_);
                        v___x_1102_ = v___x_1096_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1106_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1106_, 0, v_array_1092_);
                        lean_ctor_set(v_reuseFailAlloc_1106_, 1, v___x_1100_);
                        lean_ctor_set(v_reuseFailAlloc_1106_, 2, v_stop_1094_);
                        v___x_1102_ = v_reuseFailAlloc_1106_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1103_ = lean_array_fget(v_array_1092_, v_start_1093_);
                lean_dec(v_start_1093_);
                lean_dec_ref(v_array_1092_);
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
    mut v_es_1110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
    v___x_1111_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg___closed__0;
    v___x_1112_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_es_1110_, v___x_1111_);
    v___x_1113_ = lean_array_to_list(v___x_1112_);
    v___x_1114_ = lean_box(0);
    v___x_1115_ =
        l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
            v___x_1113_,
            v___x_1114_,
        );
    v___x_1116_ = l_List_sum___at___00Lean_PersistentHashMap_subarrayMeasure_spec__2(v___x_1115_);
    lean_dec(v___x_1115_);
    return v___x_1116_;
}
pub unsafe fn l_Lean_PersistentHashMap_subarrayMeasure(
    mut v_00_u03b1_1117_: *mut LeanObject,
    mut v_00_u03b2_1118_: *mut LeanObject,
    mut v_es_1119_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
    v___x_1120_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_es_1119_);
    return v___x_1120_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0(
    mut v_00_u03b1_1121_: *mut LeanObject,
    mut v_00_u03b2_1122_: *mut LeanObject,
    mut v_inst_1123_: *mut LeanObject,
    mut v_R_1124_: *mut LeanObject,
    mut v_a_1125_: *mut LeanObject,
    mut v_b_1126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1127_: *mut LeanObject = core::ptr::null_mut();
    v___x_1127_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_PersistentHashMap_subarrayMeasure_spec__0___redArg(v_a_1125_, v_b_1126_);
    return v___x_1127_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1(
    mut v_00_u03b1_1128_: *mut LeanObject,
    mut v_00_u03b2_1129_: *mut LeanObject,
    mut v_a_1130_: *mut LeanObject,
    mut v_a_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1132_: *mut LeanObject = core::ptr::null_mut();
    v___x_1132_ =
        l_List_mapTR_loop___at___00Lean_PersistentHashMap_subarrayMeasure_spec__1___redArg(
            v_a_1130_, v_a_1131_,
        );
    return v___x_1132_;
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_measure___redArg(
    mut v_x_1133_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1133_) {
        0 => {
            let mut v___x_1134_: *mut LeanObject = core::ptr::null_mut();
            v___x_1134_ = lean_unsigned_to_nat(0);
            return v___x_1134_;
        }
        1 => {
            let mut v_a_1135_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1136_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1137_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1138_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1139_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1140_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1141_: *mut LeanObject = core::ptr::null_mut();
            v_a_1135_ = lean_ctor_get(v_x_1133_, 0);
            lean_inc_ref(v_a_1135_);
            v_a_1136_ = lean_ctor_get(v_x_1133_, 1);
            lean_inc(v_a_1136_);
            lean_dec_ref_known(v_x_1133_, 2);
            v___x_1137_ = l_Lean_PersistentHashMap_subarrayMeasure___redArg(v_a_1135_);
            v___x_1138_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_1136_);
            v___x_1139_ = lean_nat_add(v___x_1137_, v___x_1138_);
            lean_dec(v___x_1138_);
            lean_dec(v___x_1137_);
            v___x_1140_ = lean_unsigned_to_nat(1);
            v___x_1141_ = lean_nat_add(v___x_1139_, v___x_1140_);
            lean_dec(v___x_1139_);
            return v___x_1141_;
        }
        _ => {
            let mut v_vals_1142_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1143_: *mut LeanObject = core::ptr::null_mut();
            let mut v_start_1144_: *mut LeanObject = core::ptr::null_mut();
            let mut v_stop_1145_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1146_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1147_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1148_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1149_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1150_: *mut LeanObject = core::ptr::null_mut();
            v_vals_1142_ = lean_ctor_get(v_x_1133_, 1);
            lean_inc_ref(v_vals_1142_);
            v_a_1143_ = lean_ctor_get(v_x_1133_, 2);
            lean_inc(v_a_1143_);
            lean_dec_ref_known(v_x_1133_, 3);
            v_start_1144_ = lean_ctor_get(v_vals_1142_, 1);
            lean_inc(v_start_1144_);
            v_stop_1145_ = lean_ctor_get(v_vals_1142_, 2);
            lean_inc(v_stop_1145_);
            lean_dec_ref(v_vals_1142_);
            v___x_1146_ = lean_nat_sub(v_stop_1145_, v_start_1144_);
            lean_dec(v_start_1144_);
            lean_dec(v_stop_1145_);
            v___x_1147_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_a_1143_);
            v___x_1148_ = lean_nat_add(v___x_1146_, v___x_1147_);
            lean_dec(v___x_1147_);
            lean_dec(v___x_1146_);
            v___x_1149_ = lean_unsigned_to_nat(1);
            v___x_1150_ = lean_nat_add(v___x_1148_, v___x_1149_);
            lean_dec(v___x_1148_);
            return v___x_1150_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_Zipper_measure(
    mut v_00_u03b1_1151_: *mut LeanObject,
    mut v_00_u03b2_1152_: *mut LeanObject,
    mut v_x_1153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
    v___x_1154_ = l_Lean_PersistentHashMap_Zipper_measure___redArg(v_x_1153_);
    return v___x_1154_;
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter___redArg(
    mut v_x_1155_: *mut LeanObject,
    mut v_h__1_1156_: *mut LeanObject,
    mut v_h__2_1157_: *mut LeanObject,
    mut v_h__3_1158_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1155_) {
        0 => {
            let mut v_key_1159_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1160_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1158_);
            lean_dec(v_h__1_1156_);
            v_key_1159_ = lean_ctor_get(v_x_1155_, 0);
            lean_inc(v_key_1159_);
            v_val_1160_ = lean_ctor_get(v_x_1155_, 1);
            lean_inc(v_val_1160_);
            lean_dec_ref_known(v_x_1155_, 2);
            v___x_1161_ = lean_apply_2(v_h__2_1157_, v_key_1159_, v_val_1160_);
            return v___x_1161_;
        }
        1 => {
            let mut v_node_1162_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1163_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1157_);
            lean_dec(v_h__1_1156_);
            v_node_1162_ = lean_ctor_get(v_x_1155_, 0);
            lean_inc(v_node_1162_);
            lean_dec_ref_known(v_x_1155_, 1);
            v___x_1163_ = lean_apply_1(v_h__3_1158_, v_node_1162_);
            return v___x_1163_;
        }
        _ => {
            let mut v___x_1164_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1165_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1158_);
            lean_dec(v_h__2_1157_);
            v___x_1164_ = lean_box(0);
            v___x_1165_ = lean_apply_1(v_h__1_1156_, v___x_1164_);
            return v___x_1165_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__1_splitter(
    mut v_00_u03b1_1166_: *mut LeanObject,
    mut v_00_u03b2_1167_: *mut LeanObject,
    mut v_motive_1168_: *mut LeanObject,
    mut v_x_1169_: *mut LeanObject,
    mut v_h__1_1170_: *mut LeanObject,
    mut v_h__2_1171_: *mut LeanObject,
    mut v_h__3_1172_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1169_) {
        0 => {
            let mut v_key_1173_: *mut LeanObject = core::ptr::null_mut();
            let mut v_val_1174_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1175_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1172_);
            lean_dec(v_h__1_1170_);
            v_key_1173_ = lean_ctor_get(v_x_1169_, 0);
            lean_inc(v_key_1173_);
            v_val_1174_ = lean_ctor_get(v_x_1169_, 1);
            lean_inc(v_val_1174_);
            lean_dec_ref_known(v_x_1169_, 2);
            v___x_1175_ = lean_apply_2(v_h__2_1171_, v_key_1173_, v_val_1174_);
            return v___x_1175_;
        }
        1 => {
            let mut v_node_1176_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1177_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1171_);
            lean_dec(v_h__1_1170_);
            v_node_1176_ = lean_ctor_get(v_x_1169_, 0);
            lean_inc(v_node_1176_);
            lean_dec_ref_known(v_x_1169_, 1);
            v___x_1177_ = lean_apply_1(v_h__3_1172_, v_node_1176_);
            return v___x_1177_;
        }
        _ => {
            let mut v___x_1178_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1179_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1172_);
            lean_dec(v_h__2_1171_);
            v___x_1178_ = lean_box(0);
            v___x_1179_ = lean_apply_1(v_h__1_1170_, v___x_1178_);
            return v___x_1179_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter___redArg(
    mut v_x_1180_: *mut LeanObject,
    mut v_h__1_1181_: *mut LeanObject,
    mut v_h__2_1182_: *mut LeanObject,
    mut v_h__3_1183_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1180_) {
        0 => {
            let mut v___x_1184_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1185_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1183_);
            lean_dec(v_h__2_1182_);
            v___x_1184_ = lean_box(0);
            v___x_1185_ = lean_apply_1(v_h__1_1181_, v___x_1184_);
            return v___x_1185_;
        }
        1 => {
            let mut v_a_1186_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1187_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1188_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1183_);
            lean_dec(v_h__1_1181_);
            v_a_1186_ = lean_ctor_get(v_x_1180_, 0);
            lean_inc_ref(v_a_1186_);
            v_a_1187_ = lean_ctor_get(v_x_1180_, 1);
            lean_inc(v_a_1187_);
            lean_dec_ref_known(v_x_1180_, 2);
            v___x_1188_ = lean_apply_2(v_h__2_1182_, v_a_1186_, v_a_1187_);
            return v___x_1188_;
        }
        _ => {
            let mut v_keys_1189_: *mut LeanObject = core::ptr::null_mut();
            let mut v_vals_1190_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1191_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1192_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1182_);
            lean_dec(v_h__1_1181_);
            v_keys_1189_ = lean_ctor_get(v_x_1180_, 0);
            lean_inc_ref(v_keys_1189_);
            v_vals_1190_ = lean_ctor_get(v_x_1180_, 1);
            lean_inc_ref(v_vals_1190_);
            v_a_1191_ = lean_ctor_get(v_x_1180_, 2);
            lean_inc(v_a_1191_);
            lean_dec_ref_known(v_x_1180_, 3);
            v___x_1192_ = lean_apply_4(
                v_h__3_1183_,
                v_keys_1189_,
                v_vals_1190_,
                lean_box(0),
                v_a_1191_,
            );
            return v___x_1192_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_Zipper_step_match__3_splitter(
    mut v_00_u03b1_1193_: *mut LeanObject,
    mut v_00_u03b2_1194_: *mut LeanObject,
    mut v_motive_1195_: *mut LeanObject,
    mut v_x_1196_: *mut LeanObject,
    mut v_h__1_1197_: *mut LeanObject,
    mut v_h__2_1198_: *mut LeanObject,
    mut v_h__3_1199_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_x_1196_) {
        0 => {
            let mut v___x_1200_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1199_);
            lean_dec(v_h__2_1198_);
            v___x_1200_ = lean_box(0);
            v___x_1201_ = lean_apply_1(v_h__1_1197_, v___x_1200_);
            return v___x_1201_;
        }
        1 => {
            let mut v_a_1202_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1203_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1204_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__3_1199_);
            lean_dec(v_h__1_1197_);
            v_a_1202_ = lean_ctor_get(v_x_1196_, 0);
            lean_inc_ref(v_a_1202_);
            v_a_1203_ = lean_ctor_get(v_x_1196_, 1);
            lean_inc(v_a_1203_);
            lean_dec_ref_known(v_x_1196_, 2);
            v___x_1204_ = lean_apply_2(v_h__2_1198_, v_a_1202_, v_a_1203_);
            return v___x_1204_;
        }
        _ => {
            let mut v_keys_1205_: *mut LeanObject = core::ptr::null_mut();
            let mut v_vals_1206_: *mut LeanObject = core::ptr::null_mut();
            let mut v_a_1207_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1208_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_h__2_1198_);
            lean_dec(v_h__1_1197_);
            v_keys_1205_ = lean_ctor_get(v_x_1196_, 0);
            lean_inc_ref(v_keys_1205_);
            v_vals_1206_ = lean_ctor_get(v_x_1196_, 1);
            lean_inc_ref(v_vals_1206_);
            v_a_1207_ = lean_ctor_get(v_x_1196_, 2);
            lean_inc(v_a_1207_);
            lean_dec_ref_known(v_x_1196_, 3);
            v___x_1208_ = lean_apply_4(
                v_h__3_1199_,
                v_keys_1205_,
                v_vals_1206_,
                lean_box(0),
                v_a_1207_,
            );
            return v___x_1208_;
        }
    }
}
pub unsafe fn l___private_Lean_Data_Iterators_Producers_PersistentHashMap_0__Lean_PersistentHashMap_instFinitenessRelation(
    mut v_00_u03b1_1209_: *mut LeanObject,
    mut v_00_u03b2_1210_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1211_: *mut LeanObject = core::ptr::null_mut();
    v___x_1211_ = lean_box(0);
    return v___x_1211_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0(
    mut v_toPure_1212_: *mut LeanObject,
    mut v_recur_1213_: *mut LeanObject,
    mut v_it_1214_: *mut LeanObject,
    mut v_____do__lift_1215_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1215_) == 0 {
        let mut v_a_1216_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1217_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_1214_);
        lean_dec(v_recur_1213_);
        v_a_1216_ = lean_ctor_get(v_____do__lift_1215_, 0);
        lean_inc(v_a_1216_);
        lean_dec_ref_known(v_____do__lift_1215_, 1);
        v___x_1217_ = lean_apply_2(v_toPure_1212_, lean_box(0), v_a_1216_);
        return v___x_1217_;
    } else {
        let mut v_a_1218_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1219_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1212_);
        v_a_1218_ = lean_ctor_get(v_____do__lift_1215_, 0);
        lean_inc(v_a_1218_);
        lean_dec_ref_known(v_____do__lift_1215_, 1);
        v___x_1219_ = lean_apply_4(
            v_recur_1213_,
            v_it_1214_,
            v_a_1218_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1219_;
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1(
    mut v_toPure_1220_: *mut LeanObject,
    mut v_recur_1221_: *mut LeanObject,
    mut v___y_1222_: *mut LeanObject,
    mut v_acc_1223_: *mut LeanObject,
    mut v_toBind_1224_: *mut LeanObject,
    mut v_s_1225_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_1225_) {
        0 => {
            let mut v_it_1226_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1227_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1228_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
            v_it_1226_ = lean_ctor_get(v_s_1225_, 0);
            lean_inc(v_it_1226_);
            v_out_1227_ = lean_ctor_get(v_s_1225_, 1);
            lean_inc(v_out_1227_);
            lean_dec_ref_known(v_s_1225_, 2);
            v___f_1228_ = lean_alloc_closure(
                l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_1228_, 0, v_toPure_1220_);
            lean_closure_set(v___f_1228_, 1, v_recur_1221_);
            lean_closure_set(v___f_1228_, 2, v_it_1226_);
            v___x_1229_ = lean_apply_3(v___y_1222_, v_out_1227_, lean_box(0), v_acc_1223_);
            v___x_1230_ = lean_apply_4(
                v_toBind_1224_,
                lean_box(0),
                lean_box(0),
                v___x_1229_,
                v___f_1228_,
            );
            return v___x_1230_;
        }
        1 => {
            let mut v_it_1231_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1232_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1224_);
            lean_dec(v___y_1222_);
            lean_dec(v_toPure_1220_);
            v_it_1231_ = lean_ctor_get(v_s_1225_, 0);
            lean_inc(v_it_1231_);
            lean_dec_ref_known(v_s_1225_, 1);
            v___x_1232_ = lean_apply_4(
                v_recur_1221_,
                v_it_1231_,
                v_acc_1223_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1232_;
        }
        _ => {
            let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1224_);
            lean_dec(v___y_1222_);
            lean_dec(v_recur_1221_);
            v___x_1233_ = lean_apply_2(v_toPure_1220_, lean_box(0), v_acc_1223_);
            return v___x_1233_;
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2(
    mut v_toPure_1234_: *mut LeanObject,
    mut v___y_1235_: *mut LeanObject,
    mut v_toBind_1236_: *mut LeanObject,
    mut v_lift_1237_: *mut LeanObject,
    mut v_it_1238_: *mut LeanObject,
    mut v_acc_1239_: *mut LeanObject,
    mut v_hP_1240_: *mut LeanObject,
    mut v_recur_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1249_: u8 = 0;
    let mut v_start_1250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1254_: u8 = 0;
    let mut v___x_1255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_z_1260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1262_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1266_: u8 = 0;
    let mut v___x_1268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1272_: u8 = 0;
    let mut v_node_1273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1276_: u8 = 0;
    let mut v___x_1277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1282_: u8 = 0;
    let mut v___x_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1286_: u8 = 0;
    let mut v_vals_1287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_keys_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v_start_1293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: u8 = 0;
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1311_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1242_ = lean_alloc_closure(
                    l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___f_1242_, 0, v_toPure_1234_);
                lean_closure_set(v___f_1242_, 1, v_recur_1241_);
                lean_closure_set(v___f_1242_, 2, v___y_1235_);
                lean_closure_set(v___f_1242_, 3, v_acc_1239_);
                lean_closure_set(v___f_1242_, 4, v_toBind_1236_);
                match lean_obj_tag(v_it_1238_) {
                    0 => {
                        v___x_1243_ = lean_box(2);
                        v___x_1244_ = lean_apply_4(
                            v_lift_1237_,
                            lean_box(0),
                            lean_box(0),
                            v___f_1242_,
                            v___x_1243_,
                        );
                        return v___x_1244_;
                    }
                    1 => {
                        v_a_1245_ = lean_ctor_get(v_it_1238_, 0);
                        v_a_1246_ = lean_ctor_get(v_it_1238_, 1);
                        v_isSharedCheck_1286_ = (!lean_is_exclusive(v_it_1238_)) as u8;
                        if v_isSharedCheck_1286_ == 0 {
                            v___x_1248_ = v_it_1238_;
                            v_isShared_1249_ = v_isSharedCheck_1286_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_1246_);
                            lean_inc(v_a_1245_);
                            lean_dec(v_it_1238_);
                            v___x_1248_ = lean_box(0);
                            v_isShared_1249_ = v_isSharedCheck_1286_;
                            state = 1;
                            continue;
                        }
                    }
                    _ => {
                        v_vals_1287_ = lean_ctor_get(v_it_1238_, 1);
                        v_keys_1288_ = lean_ctor_get(v_it_1238_, 0);
                        v_a_1289_ = lean_ctor_get(v_it_1238_, 2);
                        v_isSharedCheck_1311_ = (!lean_is_exclusive(v_it_1238_)) as u8;
                        if v_isSharedCheck_1311_ == 0 {
                            v___x_1291_ = v_it_1238_;
                            v_isShared_1292_ = v_isSharedCheck_1311_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_1289_);
                            lean_inc(v_vals_1287_);
                            lean_inc(v_keys_1288_);
                            lean_dec(v_it_1238_);
                            v___x_1291_ = lean_box(0);
                            v_isShared_1292_ = v_isSharedCheck_1311_;
                            state = 7;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_start_1250_ = lean_ctor_get(v_a_1245_, 1);
                v_stop_1251_ = lean_ctor_get(v_a_1245_, 2);
                v___x_1252_ = lean_unsigned_to_nat(0);
                v___x_1253_ = lean_nat_sub(v_stop_1251_, v_start_1250_);
                v___x_1254_ = lean_nat_dec_lt(v___x_1252_, v___x_1253_);
                lean_dec(v___x_1253_);
                if v___x_1254_ == 0 {
                    lean_del_object(v___x_1248_);
                    lean_dec_ref(v_a_1245_);
                    v___x_1255_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1255_, 0, v_a_1246_);
                    v___x_1256_ = lean_apply_4(
                        v_lift_1237_,
                        lean_box(0),
                        lean_box(0),
                        v___f_1242_,
                        v___x_1255_,
                    );
                    return v___x_1256_;
                } else {
                    v___x_1257_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_a_1245_);
                    v___x_1258_ = l_Subarray_drop___redArg(v_a_1245_, v___x_1257_);
                    if v_isShared_1249_ == 0 {
                        lean_ctor_set(v___x_1248_, 0, v___x_1258_);
                        v_z_1260_ = v___x_1248_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1285_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1285_, 0, v___x_1258_);
                        lean_ctor_set(v_reuseFailAlloc_1285_, 1, v_a_1246_);
                        v_z_1260_ = v_reuseFailAlloc_1285_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1261_ = l_Subarray_get___redArg(v_a_1245_, v___x_1252_);
                lean_dec_ref(v_a_1245_);
                match lean_obj_tag(v___x_1261_) {
                    0 => {
                        v_key_1262_ = lean_ctor_get(v___x_1261_, 0);
                        v_val_1263_ = lean_ctor_get(v___x_1261_, 1);
                        v_isSharedCheck_1272_ = (!lean_is_exclusive(v___x_1261_)) as u8;
                        if v_isSharedCheck_1272_ == 0 {
                            v___x_1265_ = v___x_1261_;
                            v_isShared_1266_ = v_isSharedCheck_1272_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_val_1263_);
                            lean_inc(v_key_1262_);
                            lean_dec(v___x_1261_);
                            v___x_1265_ = lean_box(0);
                            v_isShared_1266_ = v_isSharedCheck_1272_;
                            state = 3;
                            continue;
                        }
                    }
                    1 => {
                        v_node_1273_ = lean_ctor_get(v___x_1261_, 0);
                        v_isSharedCheck_1282_ = (!lean_is_exclusive(v___x_1261_)) as u8;
                        if v_isSharedCheck_1282_ == 0 {
                            v___x_1275_ = v___x_1261_;
                            v_isShared_1276_ = v_isSharedCheck_1282_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_node_1273_);
                            lean_dec(v___x_1261_);
                            v___x_1275_ = lean_box(0);
                            v_isShared_1276_ = v_isSharedCheck_1282_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1283_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_1283_, 0, v_z_1260_);
                        v___x_1284_ = lean_apply_4(
                            v_lift_1237_,
                            lean_box(0),
                            lean_box(0),
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
                    v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_key_1262_);
                    lean_ctor_set(v_reuseFailAlloc_1271_, 1, v_val_1263_);
                    v___x_1268_ = v_reuseFailAlloc_1271_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1269_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1269_, 0, v_z_1260_);
                lean_ctor_set(v___x_1269_, 1, v___x_1268_);
                v___x_1270_ = lean_apply_4(
                    v_lift_1237_,
                    lean_box(0),
                    lean_box(0),
                    v___f_1242_,
                    v___x_1269_,
                );
                return v___x_1270_;
            }
            5 => {
                v___x_1277_ =
                    l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_node_1273_, v_z_1260_);
                if v_isShared_1276_ == 0 {
                    lean_ctor_set(v___x_1275_, 0, v___x_1277_);
                    v___x_1279_ = v___x_1275_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1281_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1281_, 0, v___x_1277_);
                    v___x_1279_ = v_reuseFailAlloc_1281_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_1280_ = lean_apply_4(
                    v_lift_1237_,
                    lean_box(0),
                    lean_box(0),
                    v___f_1242_,
                    v___x_1279_,
                );
                return v___x_1280_;
            }
            7 => {
                v_start_1293_ = lean_ctor_get(v_vals_1287_, 1);
                v_stop_1294_ = lean_ctor_get(v_vals_1287_, 2);
                v___x_1295_ = lean_unsigned_to_nat(0);
                v___x_1296_ = lean_nat_sub(v_stop_1294_, v_start_1293_);
                v___x_1297_ = lean_nat_dec_lt(v___x_1295_, v___x_1296_);
                lean_dec(v___x_1296_);
                if v___x_1297_ == 0 {
                    lean_del_object(v___x_1291_);
                    lean_dec_ref(v_keys_1288_);
                    lean_dec_ref(v_vals_1287_);
                    v___x_1298_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1298_, 0, v_a_1289_);
                    v___x_1299_ = lean_apply_4(
                        v_lift_1237_,
                        lean_box(0),
                        lean_box(0),
                        v___f_1242_,
                        v___x_1298_,
                    );
                    return v___x_1299_;
                } else {
                    v___x_1300_ = lean_unsigned_to_nat(1);
                    lean_inc_ref(v_keys_1288_);
                    v___x_1301_ = l_Subarray_drop___redArg(v_keys_1288_, v___x_1300_);
                    lean_inc_ref(v_vals_1287_);
                    v___x_1302_ = l_Subarray_drop___redArg(v_vals_1287_, v___x_1300_);
                    if v_isShared_1292_ == 0 {
                        lean_ctor_set(v___x_1291_, 1, v___x_1302_);
                        lean_ctor_set(v___x_1291_, 0, v___x_1301_);
                        v___x_1304_ = v___x_1291_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_1310_ = lean_alloc_ctor(2, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1310_, 0, v___x_1301_);
                        lean_ctor_set(v_reuseFailAlloc_1310_, 1, v___x_1302_);
                        lean_ctor_set(v_reuseFailAlloc_1310_, 2, v_a_1289_);
                        v___x_1304_ = v_reuseFailAlloc_1310_;
                        state = 8;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1305_ = l_Subarray_get___redArg(v_keys_1288_, v___x_1295_);
                lean_dec_ref(v_keys_1288_);
                v___x_1306_ = l_Subarray_get___redArg(v_vals_1287_, v___x_1295_);
                lean_dec_ref(v_vals_1287_);
                v___x_1307_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1307_, 0, v___x_1305_);
                lean_ctor_set(v___x_1307_, 1, v___x_1306_);
                v___x_1308_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1308_, 0, v___x_1304_);
                lean_ctor_set(v___x_1308_, 1, v___x_1307_);
                v___x_1309_ = lean_apply_4(
                    v_lift_1237_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1312_: *mut LeanObject,
    mut v_lift_1313_: *mut LeanObject,
    mut v_00_u03b3_1314_: *mut LeanObject,
    mut v_Pl_1315_: *mut LeanObject,
    mut v_it_1316_: *mut LeanObject,
    mut v_init_1317_: *mut LeanObject,
    mut v___y_1318_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1319_ = lean_ctor_get(v_inst_1312_, 0);
    lean_inc_ref(v_toApplicative_1319_);
    v_toBind_1320_ = lean_ctor_get(v_inst_1312_, 1);
    lean_inc(v_toBind_1320_);
    lean_dec_ref(v_inst_1312_);
    v_toPure_1321_ = lean_ctor_get(v_toApplicative_1319_, 1);
    lean_inc(v_toPure_1321_);
    lean_dec_ref(v_toApplicative_1319_);
    v___f_1322_ = lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__2 as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_1322_, 0, v_toPure_1321_);
    lean_closure_set(v___f_1322_, 1, v___y_1318_);
    lean_closure_set(v___f_1322_, 2, v_toBind_1320_);
    lean_closure_set(v___f_1322_, 3, v_lift_1313_);
    v___x_1323_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1322_, v_it_1316_, v_init_1317_, lean_box(0));
    return v___x_1323_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop___redArg(
    mut v_inst_1324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1325_: *mut LeanObject = core::ptr::null_mut();
    v___f_1325_ = lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_1325_, 0, v_inst_1324_);
    return v___f_1325_;
}
pub unsafe fn l_Lean_PersistentHashMap_instIteratorLoop(
    mut v_00_u03b1_1326_: *mut LeanObject,
    mut v_00_u03b2_1327_: *mut LeanObject,
    mut v_n_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1330_: *mut LeanObject = core::ptr::null_mut();
    v___f_1330_ = lean_alloc_closure(
        l_Lean_PersistentHashMap_instIteratorLoop___redArg___lam__3 as *mut core::ffi::c_void,
        7,
        1,
    );
    lean_closure_set(v___f_1330_, 0, v_inst_1329_);
    return v___f_1330_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter___redArg(
    mut v_map_1331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut LeanObject = core::ptr::null_mut();
    v___x_1332_ = lean_box(0);
    v___x_1333_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_1331_, v___x_1332_);
    return v___x_1333_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter(
    mut v_00_u03b1_1334_: *mut LeanObject,
    mut v_00_u03b2_1335_: *mut LeanObject,
    mut v_inst_1336_: *mut LeanObject,
    mut v_inst_1337_: *mut LeanObject,
    mut v_map_1338_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1340_: *mut LeanObject = core::ptr::null_mut();
    v___x_1339_ = lean_box(0);
    v___x_1340_ = l_Lean_PersistentHashMap_Zipper_prependNode___redArg(v_map_1338_, v___x_1339_);
    return v___x_1340_;
}
pub unsafe fn l_Lean_PersistentHashMap_iter___boxed(
    mut v_00_u03b1_1341_: *mut LeanObject,
    mut v_00_u03b2_1342_: *mut LeanObject,
    mut v_inst_1343_: *mut LeanObject,
    mut v_inst_1344_: *mut LeanObject,
    mut v_map_1345_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1346_: *mut LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_Lean_PersistentHashMap_iter(
        v_00_u03b1_1341_,
        v_00_u03b2_1342_,
        v_inst_1343_,
        v_inst_1344_,
        v_map_1345_,
    );
    lean_dec_ref(v_inst_1344_);
    lean_dec_ref(v_inst_1343_);
    return v_res_1346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Subarray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Subarray_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Mem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
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
pub unsafe fn initialize_Lean_Data_Iterators_Producers_PersistentHashMap(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Subarray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Subarray_Split(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Slice_Array_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Mem(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Data_Iterators_Producers_PersistentHashMap(builtin);
}

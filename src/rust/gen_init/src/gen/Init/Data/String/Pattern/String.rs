// Lean compiler output
// Module: Init.Data.String.Pattern.String
// Imports: Init.Data.String.Pattern.Basic Init.Data.Vector.Basic Init.Data.String.FindPos Init.Data.String.Termination Init.Data.String.Lemmas.FindPos Init.ByCases Init.Data.Array.Lemmas Init.Data.Option.Lemmas Init.Omega
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_get_byte_fast, lean_string_memcmp,
    lean_string_utf8_byte_size, lean_string_utf8_next_fast, lean_uint8_dec_eq,
};
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Lemmas::{
    initialize_Init_Data_Array_Lemmas, runtime_initialize_Init_Data_Array_Lemmas,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::String::Basic::l_String_Slice_pos_x21;
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, l_String_Slice_posGE___redArg,
    runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Pattern::Basic::{
    initialize_Init_Data_String_Pattern_Basic, runtime_initialize_Init_Data_String_Pattern_Basic,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, l_String_Slice_Pos_remainingBytes,
    runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Data::Vector::Basic::{
    initialize_Init_Data_Vector_Basic, runtime_initialize_Init_Data_Vector_Basic,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value:
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
static mut l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value
) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(
    mut v_pat_803_: *mut leanh::LeanObject,
    mut v_patByte_804_: u8,
    mut v_table_805_: *mut leanh::LeanObject,
    mut v_guess_806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_807_ = leanh::lean_ctor_get(v_pat_803_, 0);
                v_startInclusive_808_ = leanh::lean_ctor_get(v_pat_803_, 1);
                v___x_809_ = lean_nat_add(v_startInclusive_808_, v_guess_806_);
                v___x_810_ = lean_string_get_byte_fast(v_str_807_, v___x_809_);
                v___x_811_ = lean_uint8_dec_eq(v___x_810_, v_patByte_804_);
                if v___x_811_ == 0 {
                    v___x_812_ = leanh::lean_unsigned_to_nat(0);
                    v___x_813_ = lean_nat_dec_eq(v_guess_806_, v___x_812_);
                    if v___x_813_ == 0 {
                        v___x_814_ = leanh::lean_unsigned_to_nat(1);
                        v___x_815_ = lean_nat_sub(v_guess_806_, v___x_814_);
                        v___x_816_ = lean_array_fget_borrowed(v_table_805_, v___x_815_);
                        leanh::lean_dec(v___x_815_);
                        v_guess_806_ = v___x_816_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_812_;
                    }
                } else {
                    v___x_818_ = leanh::lean_unsigned_to_nat(1);
                    v___x_819_ = lean_nat_add(v_guess_806_, v___x_818_);
                    return v___x_819_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(
    mut v_pat_820_: *mut leanh::LeanObject,
    mut v_patByte_821_: *mut leanh::LeanObject,
    mut v_table_822_: *mut leanh::LeanObject,
    mut v_guess_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_patByte_boxed_824_: u8 = 0;
    let mut v_res_825_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_patByte_boxed_824_ = (leanh::lean_unbox(v_patByte_821_) as u8);
    v_res_825_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_820_, v_patByte_boxed_824_, v_table_822_, v_guess_823_);
    leanh::lean_dec(v_guess_823_);
    leanh::lean_dec_ref(v_table_822_);
    leanh::lean_dec_ref(v_pat_820_);
    return v_res_825_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(
    mut v_pat_826_: *mut leanh::LeanObject,
    mut v_patByte_827_: u8,
    mut v_table_828_: *mut leanh::LeanObject,
    mut v_ht_829_: *mut leanh::LeanObject,
    mut v_h_830_: *mut leanh::LeanObject,
    mut v_guess_831_: *mut leanh::LeanObject,
    mut v_hg_832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_833_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_833_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_826_, v_patByte_827_, v_table_828_, v_guess_831_);
    return v___x_833_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(
    mut v_pat_834_: *mut leanh::LeanObject,
    mut v_patByte_835_: *mut leanh::LeanObject,
    mut v_table_836_: *mut leanh::LeanObject,
    mut v_ht_837_: *mut leanh::LeanObject,
    mut v_h_838_: *mut leanh::LeanObject,
    mut v_guess_839_: *mut leanh::LeanObject,
    mut v_hg_840_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_patByte_boxed_841_: u8 = 0;
    let mut v_res_842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_patByte_boxed_841_ = (leanh::lean_unbox(v_patByte_835_) as u8);
    v_res_842_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(v_pat_834_, v_patByte_boxed_841_, v_table_836_, v_ht_837_, v_h_838_, v_guess_839_, v_hg_840_);
    leanh::lean_dec(v_guess_839_);
    leanh::lean_dec_ref(v_table_836_);
    leanh::lean_dec_ref(v_pat_834_);
    return v_res_842_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(
    mut v_pat_843_: *mut leanh::LeanObject,
    mut v_table_844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_852_: u8 = 0;
    let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dist_856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_845_ = leanh::lean_ctor_get(v_pat_843_, 0);
                v_startInclusive_846_ = leanh::lean_ctor_get(v_pat_843_, 1);
                v_endExclusive_847_ = leanh::lean_ctor_get(v_pat_843_, 2);
                v___x_848_ = lean_array_get_size(v_table_844_);
                v___x_849_ = lean_nat_sub(v_endExclusive_847_, v_startInclusive_846_);
                v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
                leanh::lean_dec(v___x_849_);
                if v___x_850_ == 0 {
                    return v_table_844_;
                } else {
                    v___x_851_ = lean_nat_add(v_startInclusive_846_, v___x_848_);
                    v_patByte_852_ = lean_string_get_byte_fast(v_str_845_, v___x_851_);
                    v___x_853_ = leanh::lean_unsigned_to_nat(1);
                    v___x_854_ = lean_nat_sub(v___x_848_, v___x_853_);
                    v___x_855_ = lean_array_fget_borrowed(v_table_844_, v___x_854_);
                    leanh::lean_dec(v___x_854_);
                    v_dist_856_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_843_, v_patByte_852_, v_table_844_, v___x_855_);
                    v___x_857_ = lean_array_push(v_table_844_, v_dist_856_);
                    v_table_844_ = v___x_857_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg___boxed(
    mut v_pat_859_: *mut leanh::LeanObject,
    mut v_table_860_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_859_, v_table_860_);
    leanh::lean_dec_ref(v_pat_859_);
    return v_res_861_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(
    mut v_pat_862_: *mut leanh::LeanObject,
    mut v_table_863_: *mut leanh::LeanObject,
    mut v_ht_u2080_864_: *mut leanh::LeanObject,
    mut v_ht_865_: *mut leanh::LeanObject,
    mut v_h_866_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_867_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_862_, v_table_863_);
    return v___x_867_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(
    mut v_pat_868_: *mut leanh::LeanObject,
    mut v_table_869_: *mut leanh::LeanObject,
    mut v_ht_u2080_870_: *mut leanh::LeanObject,
    mut v_ht_871_: *mut leanh::LeanObject,
    mut v_h_872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(v_pat_868_, v_table_869_, v_ht_u2080_870_, v_ht_871_, v_h_872_);
    leanh::lean_dec_ref(v_pat_868_);
    return v_res_873_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(
    mut v_pat_876_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    v_startInclusive_877_ = leanh::lean_ctor_get(v_pat_876_, 1);
    v_endExclusive_878_ = leanh::lean_ctor_get(v_pat_876_, 2);
    v___x_879_ = lean_nat_sub(v_endExclusive_878_, v_startInclusive_877_);
    v___x_880_ = leanh::lean_unsigned_to_nat(0);
    v___x_881_ = lean_nat_dec_eq(v___x_879_, v___x_880_);
    if v___x_881_ == 0 {
        let mut v_arr_882_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_arr_x27_883_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_arr_882_ = lean_mk_empty_array_with_capacity(v___x_879_);
        leanh::lean_dec(v___x_879_);
        v_arr_x27_883_ = lean_array_push(v_arr_882_, v___x_880_);
        v___x_884_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_876_, v_arr_x27_883_);
        return v___x_884_;
    } else {
        let mut v___x_885_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_879_);
        v___x_885_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0;
        return v___x_885_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(
    mut v_pat_886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_886_);
    leanh::lean_dec_ref(v_pat_886_);
    return v_res_887_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(
    mut v_x_888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_888_) {
        0 => {
            let mut v___x_889_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_889_ = leanh::lean_unsigned_to_nat(0);
            return v___x_889_;
        }
        1 => {
            let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_890_ = leanh::lean_unsigned_to_nat(1);
            return v___x_890_;
        }
        2 => {
            let mut v___x_891_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_891_ = leanh::lean_unsigned_to_nat(2);
            return v___x_891_;
        }
        _ => {
            let mut v___x_892_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_892_ = leanh::lean_unsigned_to_nat(3);
            return v___x_892_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(
    mut v_x_893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_893_);
    leanh::lean_dec(v_x_893_);
    return v_res_894_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(
    mut v_s_895_: *mut leanh::LeanObject,
    mut v_x_896_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_896_);
    return v___x_897_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(
    mut v_s_898_: *mut leanh::LeanObject,
    mut v_x_899_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(v_s_898_, v_x_899_);
    leanh::lean_dec(v_x_899_);
    leanh::lean_dec_ref(v_s_898_);
    return v_res_900_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(
    mut v_t_901_: *mut leanh::LeanObject,
    mut v_k_902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_t_901_) {
        0 => {
            let mut v_pos_903_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_904_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pos_903_ = leanh::lean_ctor_get(v_t_901_, 0);
            leanh::lean_inc(v_pos_903_);
            leanh::lean_dec_ref_known(v_t_901_, 1);
            v___x_904_ = leanh::lean_apply_1(v_k_902_, v_pos_903_);
            return v___x_904_;
        }
        1 => {
            let mut v_pos_905_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_906_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_pos_905_ = leanh::lean_ctor_get(v_t_901_, 0);
            leanh::lean_inc(v_pos_905_);
            leanh::lean_dec_ref_known(v_t_901_, 1);
            v___x_906_ =
                leanh::lean_apply_2(v_k_902_, v_pos_905_, leanh::lean_box(0));
            return v___x_906_;
        }
        2 => {
            let mut v_needle_907_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_908_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_909_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_910_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_911_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_needle_907_ = leanh::lean_ctor_get(v_t_901_, 0);
            leanh::lean_inc_ref(v_needle_907_);
            v_table_908_ = leanh::lean_ctor_get(v_t_901_, 1);
            leanh::lean_inc_ref(v_table_908_);
            v_stackPos_909_ = leanh::lean_ctor_get(v_t_901_, 2);
            leanh::lean_inc(v_stackPos_909_);
            v_needlePos_910_ = leanh::lean_ctor_get(v_t_901_, 3);
            leanh::lean_inc(v_needlePos_910_);
            leanh::lean_dec_ref_known(v_t_901_, 4);
            v___x_911_ = leanh::lean_apply_6(
                v_k_902_,
                v_needle_907_,
                v_table_908_,
                leanh::lean_box(0),
                v_stackPos_909_,
                v_needlePos_910_,
                leanh::lean_box(0),
            );
            return v___x_911_;
        }
        _ => {
            return v_k_902_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(
    mut v_s_912_: *mut leanh::LeanObject,
    mut v_motive_913_: *mut leanh::LeanObject,
    mut v_ctorIdx_914_: *mut leanh::LeanObject,
    mut v_t_915_: *mut leanh::LeanObject,
    mut v_h_916_: *mut leanh::LeanObject,
    mut v_k_917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_918_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_915_, v_k_917_);
    return v___x_918_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(
    mut v_s_919_: *mut leanh::LeanObject,
    mut v_motive_920_: *mut leanh::LeanObject,
    mut v_ctorIdx_921_: *mut leanh::LeanObject,
    mut v_t_922_: *mut leanh::LeanObject,
    mut v_h_923_: *mut leanh::LeanObject,
    mut v_k_924_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_925_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(
        v_s_919_,
        v_motive_920_,
        v_ctorIdx_921_,
        v_t_922_,
        v_h_923_,
        v_k_924_,
    );
    leanh::lean_dec(v_ctorIdx_921_);
    leanh::lean_dec_ref(v_s_919_);
    return v_res_925_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(
    mut v_t_926_: *mut leanh::LeanObject,
    mut v_emptyBefore_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_926_, v_emptyBefore_927_);
    return v___x_928_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(
    mut v_s_929_: *mut leanh::LeanObject,
    mut v_motive_930_: *mut leanh::LeanObject,
    mut v_t_931_: *mut leanh::LeanObject,
    mut v_h_932_: *mut leanh::LeanObject,
    mut v_emptyBefore_933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_934_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_931_, v_emptyBefore_933_);
    return v___x_934_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(
    mut v_s_935_: *mut leanh::LeanObject,
    mut v_motive_936_: *mut leanh::LeanObject,
    mut v_t_937_: *mut leanh::LeanObject,
    mut v_h_938_: *mut leanh::LeanObject,
    mut v_emptyBefore_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_940_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(
        v_s_935_,
        v_motive_936_,
        v_t_937_,
        v_h_938_,
        v_emptyBefore_939_,
    );
    leanh::lean_dec_ref(v_s_935_);
    return v_res_940_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(
    mut v_t_941_: *mut leanh::LeanObject,
    mut v_emptyAt_942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_943_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_941_, v_emptyAt_942_);
    return v___x_943_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(
    mut v_s_944_: *mut leanh::LeanObject,
    mut v_motive_945_: *mut leanh::LeanObject,
    mut v_t_946_: *mut leanh::LeanObject,
    mut v_h_947_: *mut leanh::LeanObject,
    mut v_emptyAt_948_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_946_, v_emptyAt_948_);
    return v___x_949_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(
    mut v_s_950_: *mut leanh::LeanObject,
    mut v_motive_951_: *mut leanh::LeanObject,
    mut v_t_952_: *mut leanh::LeanObject,
    mut v_h_953_: *mut leanh::LeanObject,
    mut v_emptyAt_954_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_955_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(
        v_s_950_,
        v_motive_951_,
        v_t_952_,
        v_h_953_,
        v_emptyAt_954_,
    );
    leanh::lean_dec_ref(v_s_950_);
    return v_res_955_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(
    mut v_t_956_: *mut leanh::LeanObject,
    mut v_proper_957_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_956_, v_proper_957_);
    return v___x_958_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(
    mut v_s_959_: *mut leanh::LeanObject,
    mut v_motive_960_: *mut leanh::LeanObject,
    mut v_t_961_: *mut leanh::LeanObject,
    mut v_h_962_: *mut leanh::LeanObject,
    mut v_proper_963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_961_, v_proper_963_);
    return v___x_964_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(
    mut v_s_965_: *mut leanh::LeanObject,
    mut v_motive_966_: *mut leanh::LeanObject,
    mut v_t_967_: *mut leanh::LeanObject,
    mut v_h_968_: *mut leanh::LeanObject,
    mut v_proper_969_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(
        v_s_965_,
        v_motive_966_,
        v_t_967_,
        v_h_968_,
        v_proper_969_,
    );
    leanh::lean_dec_ref(v_s_965_);
    return v_res_970_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(
    mut v_t_971_: *mut leanh::LeanObject,
    mut v_atEnd_972_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_973_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_971_, v_atEnd_972_);
    return v___x_973_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(
    mut v_s_974_: *mut leanh::LeanObject,
    mut v_motive_975_: *mut leanh::LeanObject,
    mut v_t_976_: *mut leanh::LeanObject,
    mut v_h_977_: *mut leanh::LeanObject,
    mut v_atEnd_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_976_, v_atEnd_978_);
    return v___x_979_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(
    mut v_s_980_: *mut leanh::LeanObject,
    mut v_motive_981_: *mut leanh::LeanObject,
    mut v_t_982_: *mut leanh::LeanObject,
    mut v_h_983_: *mut leanh::LeanObject,
    mut v_atEnd_984_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_985_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(
        v_s_980_,
        v_motive_981_,
        v_t_982_,
        v_h_983_,
        v_atEnd_984_,
    );
    leanh::lean_dec_ref(v_s_980_);
    return v_res_985_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(
    mut v_s_988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
    return v___x_989_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(
    mut v_s_990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_s_990_);
    leanh::lean_dec_ref(v_s_990_);
    return v_res_991_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(
    mut v_a_992_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_993_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_a_992_);
    return v___x_993_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(
    mut v_a_994_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_995_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_994_);
    leanh::lean_dec_ref(v_a_994_);
    return v_res_995_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(
    mut v_pat_996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    v_startInclusive_997_ = leanh::lean_ctor_get(v_pat_996_, 1);
    v_endExclusive_998_ = leanh::lean_ctor_get(v_pat_996_, 2);
    v___x_999_ = lean_nat_sub(v_endExclusive_998_, v_startInclusive_997_);
    v___x_1000_ = leanh::lean_unsigned_to_nat(0);
    v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
    leanh::lean_dec(v___x_999_);
    if v___x_1001_ == 0 {
        let mut v___x_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1002_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_996_);
        v___x_1003_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1003_, 0, v_pat_996_);
        leanh::lean_ctor_set(v___x_1003_, 1, v___x_1002_);
        leanh::lean_ctor_set(v___x_1003_, 2, v___x_1000_);
        leanh::lean_ctor_set(v___x_1003_, 3, v___x_1000_);
        return v___x_1003_;
    } else {
        let mut v___x_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_pat_996_);
        v___x_1004_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
        return v___x_1004_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter(
    mut v_pat_1005_: *mut leanh::LeanObject,
    mut v_s_1006_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: u8 = 0;
    v_startInclusive_1007_ = leanh::lean_ctor_get(v_pat_1005_, 1);
    v_endExclusive_1008_ = leanh::lean_ctor_get(v_pat_1005_, 2);
    v___x_1009_ = lean_nat_sub(v_endExclusive_1008_, v_startInclusive_1007_);
    v___x_1010_ = leanh::lean_unsigned_to_nat(0);
    v___x_1011_ = lean_nat_dec_eq(v___x_1009_, v___x_1010_);
    leanh::lean_dec(v___x_1009_);
    if v___x_1011_ == 0 {
        let mut v___x_1012_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1013_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1012_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_1005_);
        v___x_1013_ = leanh::lean_alloc_ctor(2, 4, (0) as u32);
        leanh::lean_ctor_set(v___x_1013_, 0, v_pat_1005_);
        leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
        leanh::lean_ctor_set(v___x_1013_, 2, v___x_1010_);
        leanh::lean_ctor_set(v___x_1013_, 3, v___x_1010_);
        return v___x_1013_;
    } else {
        let mut v___x_1014_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_pat_1005_);
        v___x_1014_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
        return v___x_1014_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(
    mut v_pat_1015_: *mut leanh::LeanObject,
    mut v_s_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_1015_, v_s_1016_);
    leanh::lean_dec_ref(v_s_1016_);
    return v_res_1017_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(
    mut v_s_1018_: *mut leanh::LeanObject,
    mut v_x_1019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v_res_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_pos_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v_str_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1050_: u8 = 0;
    let mut v_needle_1051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1057_: u8 = 0;
    let mut v_str_1058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1076_: u8 = 0;
    let mut v___x_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1078_: u8 = 0;
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: u8 = 0;
    let mut v_oldBasePos_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBasePos_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v___x_1128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1019_) {
                0 => {
                    v_pos_1020_ = leanh::lean_ctor_get(v_x_1019_, 0);
                    v_isSharedCheck_1035_ = (!leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1035_ == 0 {
                        v___x_1022_ = v_x_1019_;
                        v_isShared_1023_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1020_);
                        leanh::lean_dec(v_x_1019_);
                        v___x_1022_ = leanh::lean_box(0);
                        v_isShared_1023_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_pos_1036_ = leanh::lean_ctor_get(v_x_1019_, 0);
                    v_isSharedCheck_1050_ = (!leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1050_ == 0 {
                        v___x_1038_ = v_x_1019_;
                        v_isShared_1039_ = v_isSharedCheck_1050_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1036_);
                        leanh::lean_dec(v_x_1019_);
                        v___x_1038_ = leanh::lean_box(0);
                        v_isShared_1039_ = v_isSharedCheck_1050_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_needle_1051_ = leanh::lean_ctor_get(v_x_1019_, 0);
                    v_table_1052_ = leanh::lean_ctor_get(v_x_1019_, 1);
                    v_stackPos_1053_ = leanh::lean_ctor_get(v_x_1019_, 2);
                    v_needlePos_1054_ = leanh::lean_ctor_get(v_x_1019_, 3);
                    v_isSharedCheck_1127_ = (!leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1056_ = v_x_1019_;
                        v_isShared_1057_ = v_isSharedCheck_1127_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_needlePos_1054_);
                        leanh::lean_inc(v_stackPos_1053_);
                        leanh::lean_inc(v_table_1052_);
                        leanh::lean_inc(v_needle_1051_);
                        leanh::lean_dec(v_x_1019_);
                        v___x_1056_ = leanh::lean_box(0);
                        v_isShared_1057_ = v_isSharedCheck_1127_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_1128_ = leanh::lean_box(2);
                    return v___x_1128_;
                }
            },
            1 => {
                leanh::lean_inc_n(v_pos_1020_, 2);
                v_res_1024_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v_res_1024_, 0, v_pos_1020_);
                leanh::lean_ctor_set(v_res_1024_, 1, v_pos_1020_);
                v_startInclusive_1025_ = leanh::lean_ctor_get(v_s_1018_, 1);
                v_endExclusive_1026_ = leanh::lean_ctor_get(v_s_1018_, 2);
                v___x_1027_ = lean_nat_sub(v_endExclusive_1026_, v_startInclusive_1025_);
                v___x_1028_ = lean_nat_dec_eq(v_pos_1020_, v___x_1027_);
                leanh::lean_dec(v___x_1027_);
                if v___x_1028_ == 0 {
                    if v_isShared_1023_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1022_, 1);
                        v___x_1030_ = v___x_1022_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1032_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_pos_1020_);
                        v___x_1030_ = v_reuseFailAlloc_1032_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1022_);
                    leanh::lean_dec(v_pos_1020_);
                    v___x_1033_ = leanh::lean_box(3);
                    v___x_1034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1034_, 0, v___x_1033_);
                    leanh::lean_ctor_set(v___x_1034_, 1, v_res_1024_);
                    return v___x_1034_;
                }
            }
            2 => {
                v___x_1031_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
                leanh::lean_ctor_set(v___x_1031_, 1, v_res_1024_);
                return v___x_1031_;
            }
            3 => {
                v_str_1040_ = leanh::lean_ctor_get(v_s_1018_, 0);
                v_startInclusive_1041_ = leanh::lean_ctor_get(v_s_1018_, 1);
                v___x_1042_ = lean_nat_add(v_startInclusive_1041_, v_pos_1036_);
                v___x_1043_ = lean_string_utf8_next_fast(v_str_1040_, v___x_1042_);
                leanh::lean_dec(v___x_1042_);
                v___x_1044_ = lean_nat_sub(v___x_1043_, v_startInclusive_1041_);
                leanh::lean_inc(v___x_1044_);
                v_res_1045_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_res_1045_, 0, v_pos_1036_);
                leanh::lean_ctor_set(v_res_1045_, 1, v___x_1044_);
                if v_isShared_1039_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1038_, 0);
                    leanh::lean_ctor_set(v___x_1038_, 0, v___x_1044_);
                    v___x_1047_ = v___x_1038_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1044_);
                    v___x_1047_ = v_reuseFailAlloc_1049_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1048_, 0, v___x_1047_);
                leanh::lean_ctor_set(v___x_1048_, 1, v_res_1045_);
                return v___x_1048_;
            }
            5 => {
                v_str_1058_ = leanh::lean_ctor_get(v_needle_1051_, 0);
                v_startInclusive_1059_ = leanh::lean_ctor_get(v_needle_1051_, 1);
                v_endExclusive_1060_ = leanh::lean_ctor_get(v_needle_1051_, 2);
                v_str_1061_ = leanh::lean_ctor_get(v_s_1018_, 0);
                v_startInclusive_1062_ = leanh::lean_ctor_get(v_s_1018_, 1);
                v_endExclusive_1063_ = leanh::lean_ctor_get(v_s_1018_, 2);
                v_basePos_1064_ = lean_nat_sub(v_stackPos_1053_, v_needlePos_1054_);
                v___x_1065_ = lean_nat_sub(v_endExclusive_1060_, v_startInclusive_1059_);
                v___x_1066_ = lean_nat_add(v_basePos_1064_, v___x_1065_);
                v___x_1067_ = lean_nat_sub(v_endExclusive_1063_, v_startInclusive_1062_);
                v___x_1068_ = lean_nat_dec_le(v___x_1066_, v___x_1067_);
                leanh::lean_dec(v___x_1066_);
                if v___x_1068_ == 0 {
                    leanh::lean_dec(v___x_1065_);
                    leanh::lean_del_object(v___x_1056_);
                    leanh::lean_dec(v_needlePos_1054_);
                    leanh::lean_dec(v_stackPos_1053_);
                    leanh::lean_dec_ref(v_table_1052_);
                    leanh::lean_dec_ref(v_needle_1051_);
                    v___x_1069_ = lean_nat_dec_lt(v_basePos_1064_, v___x_1067_);
                    if v___x_1069_ == 0 {
                        leanh::lean_dec(v___x_1067_);
                        leanh::lean_dec(v_basePos_1064_);
                        v___x_1070_ = leanh::lean_box(2);
                        return v___x_1070_;
                    } else {
                        v___x_1071_ = l_String_Slice_pos_x21(v_s_1018_, v_basePos_1064_);
                        leanh::lean_dec(v_basePos_1064_);
                        v_res_1072_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_res_1072_, 0, v___x_1071_);
                        leanh::lean_ctor_set(v_res_1072_, 1, v___x_1067_);
                        v___x_1073_ = leanh::lean_box(3);
                        v___x_1074_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
                        leanh::lean_ctor_set(v___x_1074_, 1, v_res_1072_);
                        return v___x_1074_;
                    }
                } else {
                    leanh::lean_dec(v___x_1067_);
                    v___x_1075_ = lean_nat_add(v_startInclusive_1062_, v_stackPos_1053_);
                    v_stackByte_1076_ = lean_string_get_byte_fast(v_str_1061_, v___x_1075_);
                    v___x_1077_ = lean_nat_add(v_startInclusive_1059_, v_needlePos_1054_);
                    v_patByte_1078_ = lean_string_get_byte_fast(v_str_1058_, v___x_1077_);
                    v___x_1079_ = lean_uint8_dec_eq(v_stackByte_1076_, v_patByte_1078_);
                    if v___x_1079_ == 0 {
                        leanh::lean_dec(v___x_1065_);
                        v___x_1080_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1081_ = lean_nat_dec_eq(v_needlePos_1054_, v___x_1080_);
                        if v___x_1081_ == 0 {
                            v___x_1082_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1083_ = lean_nat_sub(v_needlePos_1054_, v___x_1082_);
                            leanh::lean_dec(v_needlePos_1054_);
                            v_newNeedlePos_1084_ =
                                lean_array_fget_borrowed(v_table_1052_, v___x_1083_);
                            leanh::lean_dec(v___x_1083_);
                            v___x_1085_ = lean_nat_dec_eq(v_newNeedlePos_1084_, v___x_1080_);
                            if v___x_1085_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_1084_);
                                v_oldBasePos_1086_ =
                                    l_String_Slice_pos_x21(v_s_1018_, v_basePos_1064_);
                                leanh::lean_dec(v_basePos_1064_);
                                v___x_1087_ = lean_nat_sub(v_stackPos_1053_, v_newNeedlePos_1084_);
                                v_newBasePos_1088_ = l_String_Slice_pos_x21(v_s_1018_, v___x_1087_);
                                leanh::lean_dec(v___x_1087_);
                                v_res_1089_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_res_1089_, 0, v_oldBasePos_1086_);
                                leanh::lean_ctor_set(v_res_1089_, 1, v_newBasePos_1088_);
                                if v_isShared_1057_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_1056_,
                                        3,
                                        v_newNeedlePos_1084_,
                                    );
                                    v___x_1091_ = v___x_1056_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1093_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        0,
                                        v_needle_1051_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        1,
                                        v_table_1052_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        2,
                                        v_stackPos_1053_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        3,
                                        v_newNeedlePos_1084_,
                                    );
                                    v___x_1091_ = v_reuseFailAlloc_1093_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v_basePos_1094_ =
                                    l_String_Slice_pos_x21(v_s_1018_, v_basePos_1064_);
                                leanh::lean_dec(v_basePos_1064_);
                                v_nextStackPos_1095_ =
                                    l_String_Slice_posGE___redArg(v_s_1018_, v_stackPos_1053_);
                                leanh::lean_inc(v_nextStackPos_1095_);
                                v_res_1096_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_res_1096_, 0, v_basePos_1094_);
                                leanh::lean_ctor_set(v_res_1096_, 1, v_nextStackPos_1095_);
                                if v_isShared_1057_ == 0 {
                                    leanh::lean_ctor_set(v___x_1056_, 3, v___x_1080_);
                                    leanh::lean_ctor_set(
                                        v___x_1056_,
                                        2,
                                        v_nextStackPos_1095_,
                                    );
                                    v___x_1098_ = v___x_1056_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1100_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        0,
                                        v_needle_1051_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        1,
                                        v_table_1052_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        2,
                                        v_nextStackPos_1095_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        3,
                                        v___x_1080_,
                                    );
                                    v___x_1098_ = v_reuseFailAlloc_1100_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_basePos_1064_);
                            leanh::lean_dec(v_needlePos_1054_);
                            v_basePos_1101_ = l_String_Slice_pos_x21(v_s_1018_, v_stackPos_1053_);
                            v___x_1102_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1103_ = lean_nat_add(v_stackPos_1053_, v___x_1102_);
                            leanh::lean_dec(v_stackPos_1053_);
                            v_nextStackPos_1104_ =
                                l_String_Slice_posGE___redArg(v_s_1018_, v___x_1103_);
                            leanh::lean_inc(v_nextStackPos_1104_);
                            v_res_1105_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_res_1105_, 0, v_basePos_1101_);
                            leanh::lean_ctor_set(v_res_1105_, 1, v_nextStackPos_1104_);
                            if v_isShared_1057_ == 0 {
                                leanh::lean_ctor_set(v___x_1056_, 3, v___x_1080_);
                                leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1104_);
                                v___x_1107_ = v___x_1056_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1109_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    0,
                                    v_needle_1051_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    1,
                                    v_table_1052_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    2,
                                    v_nextStackPos_1104_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 3, v___x_1080_);
                                v___x_1107_ = v_reuseFailAlloc_1109_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_basePos_1064_);
                        v___x_1110_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1111_ = lean_nat_add(v_stackPos_1053_, v___x_1110_);
                        leanh::lean_dec(v_stackPos_1053_);
                        v_nextNeedlePos_1112_ = lean_nat_add(v_needlePos_1054_, v___x_1110_);
                        leanh::lean_dec(v_needlePos_1054_);
                        v___x_1113_ = lean_nat_dec_eq(v_nextNeedlePos_1112_, v___x_1065_);
                        leanh::lean_dec(v___x_1065_);
                        if v___x_1113_ == 0 {
                            if v_isShared_1057_ == 0 {
                                leanh::lean_ctor_set(v___x_1056_, 3, v_nextNeedlePos_1112_);
                                leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1111_);
                                v___x_1115_ = v___x_1056_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1117_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    0,
                                    v_needle_1051_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    1,
                                    v_table_1052_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    2,
                                    v_nextStackPos_1111_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    3,
                                    v_nextNeedlePos_1112_,
                                );
                                v___x_1115_ = v_reuseFailAlloc_1117_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v___x_1118_ = lean_nat_sub(v_nextStackPos_1111_, v_nextNeedlePos_1112_);
                            leanh::lean_dec(v_nextNeedlePos_1112_);
                            v___x_1119_ = l_String_Slice_pos_x21(v_s_1018_, v___x_1118_);
                            leanh::lean_dec(v___x_1118_);
                            v___x_1120_ = l_String_Slice_pos_x21(v_s_1018_, v_nextStackPos_1111_);
                            v_res_1121_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_res_1121_, 0, v___x_1119_);
                            leanh::lean_ctor_set(v_res_1121_, 1, v___x_1120_);
                            v___x_1122_ = leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1057_ == 0 {
                                leanh::lean_ctor_set(v___x_1056_, 3, v___x_1122_);
                                leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1111_);
                                v___x_1124_ = v___x_1056_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1126_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    0,
                                    v_needle_1051_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    1,
                                    v_table_1052_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    2,
                                    v_nextStackPos_1111_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 3, v___x_1122_);
                                v___x_1124_ = v_reuseFailAlloc_1126_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_1092_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
                leanh::lean_ctor_set(v___x_1092_, 1, v_res_1089_);
                return v___x_1092_;
            }
            7 => {
                v___x_1099_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1099_, 0, v___x_1098_);
                leanh::lean_ctor_set(v___x_1099_, 1, v_res_1096_);
                return v___x_1099_;
            }
            8 => {
                v___x_1108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
                leanh::lean_ctor_set(v___x_1108_, 1, v_res_1105_);
                return v___x_1108_;
            }
            9 => {
                v___x_1116_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
                return v___x_1116_;
            }
            10 => {
                v___x_1125_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1125_, 0, v___x_1124_);
                leanh::lean_ctor_set(v___x_1125_, 1, v_res_1121_);
                return v___x_1125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(
    mut v_s_1129_: *mut leanh::LeanObject,
    mut v_x_1130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(
        v_s_1129_, v_x_1130_,
    );
    leanh::lean_dec_ref(v_s_1129_);
    return v_res_1131_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(
    mut v_s_1132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1133_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1133_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_1133_, 0, v_s_1132_);
    return v___f_1133_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(
    mut v_s_1134_: *mut leanh::LeanObject,
    mut v_x_1135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pos_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut v_pos_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v_stackPos_1158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match leanh::lean_obj_tag(v_x_1135_) {
                0 => {
                    v_pos_1136_ = leanh::lean_ctor_get(v_x_1135_, 0);
                    v_isSharedCheck_1146_ = (!leanh::lean_is_exclusive(v_x_1135_)) as u8;
                    if v_isSharedCheck_1146_ == 0 {
                        v___x_1138_ = v_x_1135_;
                        v_isShared_1139_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1136_);
                        leanh::lean_dec(v_x_1135_);
                        v___x_1138_ = leanh::lean_box(0);
                        v_isShared_1139_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_pos_1147_ = leanh::lean_ctor_get(v_x_1135_, 0);
                    v_isSharedCheck_1157_ = (!leanh::lean_is_exclusive(v_x_1135_)) as u8;
                    if v_isSharedCheck_1157_ == 0 {
                        v___x_1149_ = v_x_1135_;
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_pos_1147_);
                        leanh::lean_dec(v_x_1135_);
                        v___x_1149_ = leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_stackPos_1158_ = leanh::lean_ctor_get(v_x_1135_, 2);
                    leanh::lean_inc(v_stackPos_1158_);
                    v_needlePos_1159_ = leanh::lean_ctor_get(v_x_1135_, 3);
                    leanh::lean_inc(v_needlePos_1159_);
                    leanh::lean_dec_ref_known(v_x_1135_, 4);
                    v_startInclusive_1160_ = leanh::lean_ctor_get(v_s_1134_, 1);
                    v_endExclusive_1161_ = leanh::lean_ctor_get(v_s_1134_, 2);
                    v___x_1162_ = lean_nat_sub(v_endExclusive_1161_, v_startInclusive_1160_);
                    v___x_1163_ = lean_nat_sub(v___x_1162_, v_stackPos_1158_);
                    leanh::lean_dec(v_stackPos_1158_);
                    leanh::lean_dec(v___x_1162_);
                    v___x_1164_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1164_, 0, v___x_1163_);
                    leanh::lean_ctor_set(v___x_1164_, 1, v_needlePos_1159_);
                    v___x_1165_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1165_, 0, v___x_1164_);
                    return v___x_1165_;
                }
                _ => {
                    v___x_1166_ = leanh::lean_box(0);
                    return v___x_1166_;
                }
            },
            1 => {
                v___x_1140_ = l_String_Slice_Pos_remainingBytes(v_s_1134_, v_pos_1136_);
                leanh::lean_dec(v_pos_1136_);
                v___x_1141_ = leanh::lean_unsigned_to_nat(1);
                v___x_1142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1142_, 0, v___x_1140_);
                leanh::lean_ctor_set(v___x_1142_, 1, v___x_1141_);
                if v_isShared_1139_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1138_, 1);
                    leanh::lean_ctor_set(v___x_1138_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1138_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1145_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
                    v___x_1144_ = v_reuseFailAlloc_1145_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_1144_;
            }
            3 => {
                v___x_1151_ = l_String_Slice_Pos_remainingBytes(v_s_1134_, v_pos_1147_);
                leanh::lean_dec(v_pos_1147_);
                v___x_1152_ = leanh::lean_unsigned_to_nat(0);
                v___x_1153_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1153_, 0, v___x_1151_);
                leanh::lean_ctor_set(v___x_1153_, 1, v___x_1152_);
                if v_isShared_1150_ == 0 {
                    leanh::lean_ctor_set(v___x_1149_, 0, v___x_1153_);
                    v___x_1155_ = v___x_1149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
                    v___x_1155_ = v_reuseFailAlloc_1156_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption___boxed(
    mut v_s_1167_: *mut leanh::LeanObject,
    mut v_x_1168_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_1167_, v_x_1168_);
    leanh::lean_dec_ref(v_s_1167_);
    return v_res_1169_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(
    mut v_s_1170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1171_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = leanh::lean_box(0);
    return v___x_1171_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(
    mut v_s_1172_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1173_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_1172_);
    leanh::lean_dec_ref(v_s_1172_);
    return v_res_1173_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(
    mut v_x_1174_: *mut leanh::LeanObject,
    mut v_h__1_1175_: *mut leanh::LeanObject,
    mut v_h__2_1176_: *mut leanh::LeanObject,
    mut v_h__3_1177_: *mut leanh::LeanObject,
    mut v_h__4_1178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1174_) {
        0 => {
            let mut v_pos_1179_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1180_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1178_);
            leanh::lean_dec(v_h__3_1177_);
            leanh::lean_dec(v_h__2_1176_);
            v_pos_1179_ = leanh::lean_ctor_get(v_x_1174_, 0);
            leanh::lean_inc(v_pos_1179_);
            leanh::lean_dec_ref_known(v_x_1174_, 1);
            v___x_1180_ = leanh::lean_apply_1(v_h__1_1175_, v_pos_1179_);
            return v___x_1180_;
        }
        1 => {
            let mut v_pos_1181_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1178_);
            leanh::lean_dec(v_h__3_1177_);
            leanh::lean_dec(v_h__1_1175_);
            v_pos_1181_ = leanh::lean_ctor_get(v_x_1174_, 0);
            leanh::lean_inc(v_pos_1181_);
            leanh::lean_dec_ref_known(v_x_1174_, 1);
            v___x_1182_ =
                leanh::lean_apply_2(v_h__2_1176_, v_pos_1181_, leanh::lean_box(0));
            return v___x_1182_;
        }
        2 => {
            let mut v_needle_1183_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_1184_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_1185_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1187_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1178_);
            leanh::lean_dec(v_h__2_1176_);
            leanh::lean_dec(v_h__1_1175_);
            v_needle_1183_ = leanh::lean_ctor_get(v_x_1174_, 0);
            leanh::lean_inc_ref(v_needle_1183_);
            v_table_1184_ = leanh::lean_ctor_get(v_x_1174_, 1);
            leanh::lean_inc_ref(v_table_1184_);
            v_stackPos_1185_ = leanh::lean_ctor_get(v_x_1174_, 2);
            leanh::lean_inc(v_stackPos_1185_);
            v_needlePos_1186_ = leanh::lean_ctor_get(v_x_1174_, 3);
            leanh::lean_inc(v_needlePos_1186_);
            leanh::lean_dec_ref_known(v_x_1174_, 4);
            v___x_1187_ = leanh::lean_apply_6(
                v_h__3_1177_,
                v_needle_1183_,
                v_table_1184_,
                leanh::lean_box(0),
                v_stackPos_1185_,
                v_needlePos_1186_,
                leanh::lean_box(0),
            );
            return v___x_1187_;
        }
        _ => {
            let mut v___x_1188_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1189_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1177_);
            leanh::lean_dec(v_h__2_1176_);
            leanh::lean_dec(v_h__1_1175_);
            v___x_1188_ = leanh::lean_box(0);
            v___x_1189_ = leanh::lean_apply_1(v_h__4_1178_, v___x_1188_);
            return v___x_1189_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(
    mut v_s_1190_: *mut leanh::LeanObject,
    mut v_motive_1191_: *mut leanh::LeanObject,
    mut v_x_1192_: *mut leanh::LeanObject,
    mut v_h__1_1193_: *mut leanh::LeanObject,
    mut v_h__2_1194_: *mut leanh::LeanObject,
    mut v_h__3_1195_: *mut leanh::LeanObject,
    mut v_h__4_1196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1192_) {
        0 => {
            let mut v_pos_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1196_);
            leanh::lean_dec(v_h__3_1195_);
            leanh::lean_dec(v_h__2_1194_);
            v_pos_1197_ = leanh::lean_ctor_get(v_x_1192_, 0);
            leanh::lean_inc(v_pos_1197_);
            leanh::lean_dec_ref_known(v_x_1192_, 1);
            v___x_1198_ = leanh::lean_apply_1(v_h__1_1193_, v_pos_1197_);
            return v___x_1198_;
        }
        1 => {
            let mut v_pos_1199_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1196_);
            leanh::lean_dec(v_h__3_1195_);
            leanh::lean_dec(v_h__1_1193_);
            v_pos_1199_ = leanh::lean_ctor_get(v_x_1192_, 0);
            leanh::lean_inc(v_pos_1199_);
            leanh::lean_dec_ref_known(v_x_1192_, 1);
            v___x_1200_ =
                leanh::lean_apply_2(v_h__2_1194_, v_pos_1199_, leanh::lean_box(0));
            return v___x_1200_;
        }
        2 => {
            let mut v_needle_1201_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_1202_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_1203_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__4_1196_);
            leanh::lean_dec(v_h__2_1194_);
            leanh::lean_dec(v_h__1_1193_);
            v_needle_1201_ = leanh::lean_ctor_get(v_x_1192_, 0);
            leanh::lean_inc_ref(v_needle_1201_);
            v_table_1202_ = leanh::lean_ctor_get(v_x_1192_, 1);
            leanh::lean_inc_ref(v_table_1202_);
            v_stackPos_1203_ = leanh::lean_ctor_get(v_x_1192_, 2);
            leanh::lean_inc(v_stackPos_1203_);
            v_needlePos_1204_ = leanh::lean_ctor_get(v_x_1192_, 3);
            leanh::lean_inc(v_needlePos_1204_);
            leanh::lean_dec_ref_known(v_x_1192_, 4);
            v___x_1205_ = leanh::lean_apply_6(
                v_h__3_1195_,
                v_needle_1201_,
                v_table_1202_,
                leanh::lean_box(0),
                v_stackPos_1203_,
                v_needlePos_1204_,
                leanh::lean_box(0),
            );
            return v___x_1205_;
        }
        _ => {
            let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1207_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1195_);
            leanh::lean_dec(v_h__2_1194_);
            leanh::lean_dec(v_h__1_1193_);
            v___x_1206_ = leanh::lean_box(0);
            v___x_1207_ = leanh::lean_apply_1(v_h__4_1196_, v___x_1206_);
            return v___x_1207_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(
    mut v_s_1208_: *mut leanh::LeanObject,
    mut v_motive_1209_: *mut leanh::LeanObject,
    mut v_x_1210_: *mut leanh::LeanObject,
    mut v_h__1_1211_: *mut leanh::LeanObject,
    mut v_h__2_1212_: *mut leanh::LeanObject,
    mut v_h__3_1213_: *mut leanh::LeanObject,
    mut v_h__4_1214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_1208_, v_motive_1209_, v_x_1210_, v_h__1_1211_, v_h__2_1212_, v_h__3_1213_, v_h__4_1214_);
    leanh::lean_dec_ref(v_s_1208_);
    return v_res_1215_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(
    mut v_x_1216_: *mut leanh::LeanObject,
    mut v_h__1_1217_: *mut leanh::LeanObject,
    mut v_h__2_1218_: *mut leanh::LeanObject,
    mut v_h__3_1219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1216_) {
        0 => {
            let mut v_it_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1219_);
            leanh::lean_dec(v_h__2_1218_);
            v_it_1220_ = leanh::lean_ctor_get(v_x_1216_, 0);
            leanh::lean_inc(v_it_1220_);
            v_out_1221_ = leanh::lean_ctor_get(v_x_1216_, 1);
            leanh::lean_inc(v_out_1221_);
            leanh::lean_dec_ref_known(v_x_1216_, 2);
            v___x_1222_ = leanh::lean_apply_2(v_h__1_1217_, v_it_1220_, v_out_1221_);
            return v___x_1222_;
        }
        1 => {
            let mut v_it_1223_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1219_);
            leanh::lean_dec(v_h__1_1217_);
            v_it_1223_ = leanh::lean_ctor_get(v_x_1216_, 0);
            leanh::lean_inc(v_it_1223_);
            leanh::lean_dec_ref_known(v_x_1216_, 1);
            v___x_1224_ = leanh::lean_apply_1(v_h__2_1218_, v_it_1223_);
            return v___x_1224_;
        }
        _ => {
            let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1218_);
            leanh::lean_dec(v_h__1_1217_);
            v___x_1225_ = leanh::lean_box(0);
            v___x_1226_ = leanh::lean_apply_1(v_h__3_1219_, v___x_1225_);
            return v___x_1226_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(
    mut v_s_1227_: *mut leanh::LeanObject,
    mut v_motive_1228_: *mut leanh::LeanObject,
    mut v_x_1229_: *mut leanh::LeanObject,
    mut v_h__1_1230_: *mut leanh::LeanObject,
    mut v_h__2_1231_: *mut leanh::LeanObject,
    mut v_h__3_1232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_x_1229_) {
        0 => {
            let mut v_it_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1235_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1232_);
            leanh::lean_dec(v_h__2_1231_);
            v_it_1233_ = leanh::lean_ctor_get(v_x_1229_, 0);
            leanh::lean_inc(v_it_1233_);
            v_out_1234_ = leanh::lean_ctor_get(v_x_1229_, 1);
            leanh::lean_inc(v_out_1234_);
            leanh::lean_dec_ref_known(v_x_1229_, 2);
            v___x_1235_ = leanh::lean_apply_2(v_h__1_1230_, v_it_1233_, v_out_1234_);
            return v___x_1235_;
        }
        1 => {
            let mut v_it_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__3_1232_);
            leanh::lean_dec(v_h__1_1230_);
            v_it_1236_ = leanh::lean_ctor_get(v_x_1229_, 0);
            leanh::lean_inc(v_it_1236_);
            leanh::lean_dec_ref_known(v_x_1229_, 1);
            v___x_1237_ = leanh::lean_apply_1(v_h__2_1231_, v_it_1236_);
            return v___x_1237_;
        }
        _ => {
            let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1239_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_h__2_1231_);
            leanh::lean_dec(v_h__1_1230_);
            v___x_1238_ = leanh::lean_box(0);
            v___x_1239_ = leanh::lean_apply_1(v_h__3_1232_, v___x_1238_);
            return v___x_1239_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(
    mut v_s_1240_: *mut leanh::LeanObject,
    mut v_motive_1241_: *mut leanh::LeanObject,
    mut v_x_1242_: *mut leanh::LeanObject,
    mut v_h__1_1243_: *mut leanh::LeanObject,
    mut v_h__2_1244_: *mut leanh::LeanObject,
    mut v_h__3_1245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_1240_, v_motive_1241_, v_x_1242_, v_h__1_1243_, v_h__2_1244_, v_h__3_1245_);
    leanh::lean_dec_ref(v_s_1240_);
    return v_res_1246_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(
    mut v_s_1247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = leanh::lean_box(0);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(
    mut v_s_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_1249_);
    leanh::lean_dec_ref(v_s_1249_);
    return v_res_1250_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(
    mut v___y_1251_: *mut leanh::LeanObject,
    mut v_acc_1252_: *mut leanh::LeanObject,
    mut v_recur_1253_: *mut leanh::LeanObject,
    mut v_s_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_1254_) {
        0 => {
            let mut v_it_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1256_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1257_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_1255_ = leanh::lean_ctor_get(v_s_1254_, 0);
            leanh::lean_inc(v_it_1255_);
            v_out_1256_ = leanh::lean_ctor_get(v_s_1254_, 1);
            leanh::lean_inc(v_out_1256_);
            leanh::lean_dec_ref_known(v_s_1254_, 2);
            v_val_1257_ = leanh::lean_apply_3(
                v___y_1251_,
                v_out_1256_,
                leanh::lean_box(0),
                v_acc_1252_,
            );
            if leanh::lean_obj_tag(v_val_1257_) == 0 {
                let mut v_a_1258_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_it_1255_);
                leanh::lean_dec(v_recur_1253_);
                v_a_1258_ = leanh::lean_ctor_get(v_val_1257_, 0);
                leanh::lean_inc(v_a_1258_);
                leanh::lean_dec_ref_known(v_val_1257_, 1);
                return v_a_1258_;
            } else {
                let mut v_a_1259_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1260_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_1259_ = leanh::lean_ctor_get(v_val_1257_, 0);
                leanh::lean_inc(v_a_1259_);
                leanh::lean_dec_ref_known(v_val_1257_, 1);
                v___x_1260_ = leanh::lean_apply_4(
                    v_recur_1253_,
                    v_it_1255_,
                    v_a_1259_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1260_;
            }
        }
        1 => {
            let mut v_it_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___y_1251_);
            v_it_1261_ = leanh::lean_ctor_get(v_s_1254_, 0);
            leanh::lean_inc(v_it_1261_);
            leanh::lean_dec_ref_known(v_s_1254_, 1);
            v___x_1262_ = leanh::lean_apply_4(
                v_recur_1253_,
                v_it_1261_,
                v_acc_1252_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1262_;
        }
        _ => {
            leanh::lean_dec(v_recur_1253_);
            leanh::lean_dec_ref(v___y_1251_);
            return v_acc_1252_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(
    mut v___y_1263_: *mut leanh::LeanObject,
    mut v_s_1264_: *mut leanh::LeanObject,
    mut v_lift_1265_: *mut leanh::LeanObject,
    mut v_it_1266_: *mut leanh::LeanObject,
    mut v_acc_1267_: *mut leanh::LeanObject,
    mut v_hP_1268_: *mut leanh::LeanObject,
    mut v_recur_1269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v_res_1275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut v_pos_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v_str_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_needle_1305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v_str_1312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1332_: u8 = 0;
    let mut v___x_1333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1334_: u8 = 0;
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v_oldBasePos_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBasePos_1344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut v___x_1389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1270_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0 as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_1270_, 0, v___y_1263_);
                leanh::lean_closure_set(v___f_1270_, 1, v_acc_1267_);
                leanh::lean_closure_set(v___f_1270_, 2, v_recur_1269_);
                match leanh::lean_obj_tag(v_it_1266_) {
                    0 => {
                        v_pos_1271_ = leanh::lean_ctor_get(v_it_1266_, 0);
                        v_isSharedCheck_1288_ =
                            (!leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1288_ == 0 {
                            v___x_1273_ = v_it_1266_;
                            v_isShared_1274_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_1271_);
                            leanh::lean_dec(v_it_1266_);
                            v___x_1273_ = leanh::lean_box(0);
                            v_isShared_1274_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_pos_1289_ = leanh::lean_ctor_get(v_it_1266_, 0);
                        v_isSharedCheck_1304_ =
                            (!leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1304_ == 0 {
                            v___x_1291_ = v_it_1266_;
                            v_isShared_1292_ = v_isSharedCheck_1304_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_pos_1289_);
                            leanh::lean_dec(v_it_1266_);
                            v___x_1291_ = leanh::lean_box(0);
                            v_isShared_1292_ = v_isSharedCheck_1304_;
                            state = 3;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_1305_ = leanh::lean_ctor_get(v_it_1266_, 0);
                        v_table_1306_ = leanh::lean_ctor_get(v_it_1266_, 1);
                        v_stackPos_1307_ = leanh::lean_ctor_get(v_it_1266_, 2);
                        v_needlePos_1308_ = leanh::lean_ctor_get(v_it_1266_, 3);
                        v_isSharedCheck_1388_ =
                            (!leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1388_ == 0 {
                            v___x_1310_ = v_it_1266_;
                            v_isShared_1311_ = v_isSharedCheck_1388_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_needlePos_1308_);
                            leanh::lean_inc(v_stackPos_1307_);
                            leanh::lean_inc(v_table_1306_);
                            leanh::lean_inc(v_needle_1305_);
                            leanh::lean_dec(v_it_1266_);
                            v___x_1310_ = leanh::lean_box(0);
                            v_isShared_1311_ = v_isSharedCheck_1388_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1389_ = leanh::lean_box(2);
                        v___x_1390_ = leanh::lean_apply_4(
                            v_lift_1265_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1389_,
                        );
                        return v___x_1390_;
                    }
                }
            }
            1 => {
                leanh::lean_inc_n(v_pos_1271_, 2);
                v_res_1275_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                leanh::lean_ctor_set(v_res_1275_, 0, v_pos_1271_);
                leanh::lean_ctor_set(v_res_1275_, 1, v_pos_1271_);
                v_startInclusive_1276_ = leanh::lean_ctor_get(v_s_1264_, 1);
                v_endExclusive_1277_ = leanh::lean_ctor_get(v_s_1264_, 2);
                v___x_1278_ = lean_nat_sub(v_endExclusive_1277_, v_startInclusive_1276_);
                v___x_1279_ = lean_nat_dec_eq(v_pos_1271_, v___x_1278_);
                leanh::lean_dec(v___x_1278_);
                if v___x_1279_ == 0 {
                    if v_isShared_1274_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_1273_, 1);
                        v___x_1281_ = v___x_1273_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1284_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_pos_1271_);
                        v___x_1281_ = v_reuseFailAlloc_1284_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1273_);
                    leanh::lean_dec(v_pos_1271_);
                    v___x_1285_ = leanh::lean_box(3);
                    v___x_1286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1286_, 0, v___x_1285_);
                    leanh::lean_ctor_set(v___x_1286_, 1, v_res_1275_);
                    v___x_1287_ = leanh::lean_apply_4(
                        v_lift_1265_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1270_,
                        v___x_1286_,
                    );
                    return v___x_1287_;
                }
            }
            2 => {
                v___x_1282_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                leanh::lean_ctor_set(v___x_1282_, 1, v_res_1275_);
                v___x_1283_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1282_,
                );
                return v___x_1283_;
            }
            3 => {
                v_str_1293_ = leanh::lean_ctor_get(v_s_1264_, 0);
                v_startInclusive_1294_ = leanh::lean_ctor_get(v_s_1264_, 1);
                v___x_1295_ = lean_nat_add(v_startInclusive_1294_, v_pos_1289_);
                v___x_1296_ = lean_string_utf8_next_fast(v_str_1293_, v___x_1295_);
                leanh::lean_dec(v___x_1295_);
                v___x_1297_ = lean_nat_sub(v___x_1296_, v_startInclusive_1294_);
                leanh::lean_inc(v___x_1297_);
                v_res_1298_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_res_1298_, 0, v_pos_1289_);
                leanh::lean_ctor_set(v_res_1298_, 1, v___x_1297_);
                if v_isShared_1292_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_1291_, 0);
                    leanh::lean_ctor_set(v___x_1291_, 0, v___x_1297_);
                    v___x_1300_ = v___x_1291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
                    v___x_1300_ = v_reuseFailAlloc_1303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1301_, 0, v___x_1300_);
                leanh::lean_ctor_set(v___x_1301_, 1, v_res_1298_);
                v___x_1302_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1301_,
                );
                return v___x_1302_;
            }
            5 => {
                v_str_1312_ = leanh::lean_ctor_get(v_needle_1305_, 0);
                v_startInclusive_1313_ = leanh::lean_ctor_get(v_needle_1305_, 1);
                v_endExclusive_1314_ = leanh::lean_ctor_get(v_needle_1305_, 2);
                v_str_1315_ = leanh::lean_ctor_get(v_s_1264_, 0);
                v_startInclusive_1316_ = leanh::lean_ctor_get(v_s_1264_, 1);
                v_endExclusive_1317_ = leanh::lean_ctor_get(v_s_1264_, 2);
                v_basePos_1318_ = lean_nat_sub(v_stackPos_1307_, v_needlePos_1308_);
                v___x_1319_ = lean_nat_sub(v_endExclusive_1314_, v_startInclusive_1313_);
                v___x_1320_ = lean_nat_add(v_basePos_1318_, v___x_1319_);
                v___x_1321_ = lean_nat_sub(v_endExclusive_1317_, v_startInclusive_1316_);
                v___x_1322_ = lean_nat_dec_le(v___x_1320_, v___x_1321_);
                leanh::lean_dec(v___x_1320_);
                if v___x_1322_ == 0 {
                    leanh::lean_dec(v___x_1319_);
                    leanh::lean_del_object(v___x_1310_);
                    leanh::lean_dec(v_needlePos_1308_);
                    leanh::lean_dec(v_stackPos_1307_);
                    leanh::lean_dec_ref(v_table_1306_);
                    leanh::lean_dec_ref(v_needle_1305_);
                    v___x_1323_ = lean_nat_dec_lt(v_basePos_1318_, v___x_1321_);
                    if v___x_1323_ == 0 {
                        leanh::lean_dec(v___x_1321_);
                        leanh::lean_dec(v_basePos_1318_);
                        v___x_1324_ = leanh::lean_box(2);
                        v___x_1325_ = leanh::lean_apply_4(
                            v_lift_1265_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1324_,
                        );
                        return v___x_1325_;
                    } else {
                        v___x_1326_ = l_String_Slice_pos_x21(v_s_1264_, v_basePos_1318_);
                        leanh::lean_dec(v_basePos_1318_);
                        v_res_1327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_res_1327_, 0, v___x_1326_);
                        leanh::lean_ctor_set(v_res_1327_, 1, v___x_1321_);
                        v___x_1328_ = leanh::lean_box(3);
                        v___x_1329_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_1329_, 0, v___x_1328_);
                        leanh::lean_ctor_set(v___x_1329_, 1, v_res_1327_);
                        v___x_1330_ = leanh::lean_apply_4(
                            v_lift_1265_,
                            leanh::lean_box(0),
                            leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1329_,
                        );
                        return v___x_1330_;
                    }
                } else {
                    leanh::lean_dec(v___x_1321_);
                    v___x_1331_ = lean_nat_add(v_startInclusive_1316_, v_stackPos_1307_);
                    v_stackByte_1332_ = lean_string_get_byte_fast(v_str_1315_, v___x_1331_);
                    v___x_1333_ = lean_nat_add(v_startInclusive_1313_, v_needlePos_1308_);
                    v_patByte_1334_ = lean_string_get_byte_fast(v_str_1312_, v___x_1333_);
                    v___x_1335_ = lean_uint8_dec_eq(v_stackByte_1332_, v_patByte_1334_);
                    if v___x_1335_ == 0 {
                        leanh::lean_dec(v___x_1319_);
                        v___x_1336_ = leanh::lean_unsigned_to_nat(0);
                        v___x_1337_ = lean_nat_dec_eq(v_needlePos_1308_, v___x_1336_);
                        if v___x_1337_ == 0 {
                            v___x_1338_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1339_ = lean_nat_sub(v_needlePos_1308_, v___x_1338_);
                            leanh::lean_dec(v_needlePos_1308_);
                            v_newNeedlePos_1340_ =
                                lean_array_fget_borrowed(v_table_1306_, v___x_1339_);
                            leanh::lean_dec(v___x_1339_);
                            v___x_1341_ = lean_nat_dec_eq(v_newNeedlePos_1340_, v___x_1336_);
                            if v___x_1341_ == 0 {
                                leanh::lean_inc(v_newNeedlePos_1340_);
                                v_oldBasePos_1342_ =
                                    l_String_Slice_pos_x21(v_s_1264_, v_basePos_1318_);
                                leanh::lean_dec(v_basePos_1318_);
                                v___x_1343_ = lean_nat_sub(v_stackPos_1307_, v_newNeedlePos_1340_);
                                v_newBasePos_1344_ = l_String_Slice_pos_x21(v_s_1264_, v___x_1343_);
                                leanh::lean_dec(v___x_1343_);
                                v_res_1345_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_res_1345_, 0, v_oldBasePos_1342_);
                                leanh::lean_ctor_set(v_res_1345_, 1, v_newBasePos_1344_);
                                if v_isShared_1311_ == 0 {
                                    leanh::lean_ctor_set(
                                        v___x_1310_,
                                        3,
                                        v_newNeedlePos_1340_,
                                    );
                                    v___x_1347_ = v___x_1310_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1350_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        0,
                                        v_needle_1305_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        1,
                                        v_table_1306_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        2,
                                        v_stackPos_1307_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        3,
                                        v_newNeedlePos_1340_,
                                    );
                                    v___x_1347_ = v_reuseFailAlloc_1350_;
                                    state = 6;
                                    continue;
                                }
                            } else {
                                v_basePos_1351_ =
                                    l_String_Slice_pos_x21(v_s_1264_, v_basePos_1318_);
                                leanh::lean_dec(v_basePos_1318_);
                                v_nextStackPos_1352_ =
                                    l_String_Slice_posGE___redArg(v_s_1264_, v_stackPos_1307_);
                                leanh::lean_inc(v_nextStackPos_1352_);
                                v_res_1353_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_res_1353_, 0, v_basePos_1351_);
                                leanh::lean_ctor_set(v_res_1353_, 1, v_nextStackPos_1352_);
                                if v_isShared_1311_ == 0 {
                                    leanh::lean_ctor_set(v___x_1310_, 3, v___x_1336_);
                                    leanh::lean_ctor_set(
                                        v___x_1310_,
                                        2,
                                        v_nextStackPos_1352_,
                                    );
                                    v___x_1355_ = v___x_1310_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1358_ =
                                        leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        0,
                                        v_needle_1305_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        1,
                                        v_table_1306_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        2,
                                        v_nextStackPos_1352_,
                                    );
                                    leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        3,
                                        v___x_1336_,
                                    );
                                    v___x_1355_ = v_reuseFailAlloc_1358_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec(v_basePos_1318_);
                            leanh::lean_dec(v_needlePos_1308_);
                            v_basePos_1359_ = l_String_Slice_pos_x21(v_s_1264_, v_stackPos_1307_);
                            v___x_1360_ = leanh::lean_unsigned_to_nat(1);
                            v___x_1361_ = lean_nat_add(v_stackPos_1307_, v___x_1360_);
                            leanh::lean_dec(v_stackPos_1307_);
                            v_nextStackPos_1362_ =
                                l_String_Slice_posGE___redArg(v_s_1264_, v___x_1361_);
                            leanh::lean_inc(v_nextStackPos_1362_);
                            v_res_1363_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_res_1363_, 0, v_basePos_1359_);
                            leanh::lean_ctor_set(v_res_1363_, 1, v_nextStackPos_1362_);
                            if v_isShared_1311_ == 0 {
                                leanh::lean_ctor_set(v___x_1310_, 3, v___x_1336_);
                                leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1362_);
                                v___x_1365_ = v___x_1310_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1368_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    0,
                                    v_needle_1305_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    1,
                                    v_table_1306_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    2,
                                    v_nextStackPos_1362_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 3, v___x_1336_);
                                v___x_1365_ = v_reuseFailAlloc_1368_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_basePos_1318_);
                        v___x_1369_ = leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1370_ = lean_nat_add(v_stackPos_1307_, v___x_1369_);
                        leanh::lean_dec(v_stackPos_1307_);
                        v_nextNeedlePos_1371_ = lean_nat_add(v_needlePos_1308_, v___x_1369_);
                        leanh::lean_dec(v_needlePos_1308_);
                        v___x_1372_ = lean_nat_dec_eq(v_nextNeedlePos_1371_, v___x_1319_);
                        leanh::lean_dec(v___x_1319_);
                        if v___x_1372_ == 0 {
                            if v_isShared_1311_ == 0 {
                                leanh::lean_ctor_set(v___x_1310_, 3, v_nextNeedlePos_1371_);
                                leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1370_);
                                v___x_1374_ = v___x_1310_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1377_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    0,
                                    v_needle_1305_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    1,
                                    v_table_1306_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    2,
                                    v_nextStackPos_1370_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    3,
                                    v_nextNeedlePos_1371_,
                                );
                                v___x_1374_ = v_reuseFailAlloc_1377_;
                                state = 9;
                                continue;
                            }
                        } else {
                            v___x_1378_ = lean_nat_sub(v_nextStackPos_1370_, v_nextNeedlePos_1371_);
                            leanh::lean_dec(v_nextNeedlePos_1371_);
                            v___x_1379_ = l_String_Slice_pos_x21(v_s_1264_, v___x_1378_);
                            leanh::lean_dec(v___x_1378_);
                            v___x_1380_ = l_String_Slice_pos_x21(v_s_1264_, v_nextStackPos_1370_);
                            v_res_1381_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_res_1381_, 0, v___x_1379_);
                            leanh::lean_ctor_set(v_res_1381_, 1, v___x_1380_);
                            v___x_1382_ = leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1311_ == 0 {
                                leanh::lean_ctor_set(v___x_1310_, 3, v___x_1382_);
                                leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1370_);
                                v___x_1384_ = v___x_1310_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1387_ =
                                    leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    0,
                                    v_needle_1305_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    1,
                                    v_table_1306_,
                                );
                                leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    2,
                                    v_nextStackPos_1370_,
                                );
                                leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 3, v___x_1382_);
                                v___x_1384_ = v_reuseFailAlloc_1387_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_1348_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1348_, 0, v___x_1347_);
                leanh::lean_ctor_set(v___x_1348_, 1, v_res_1345_);
                v___x_1349_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1348_,
                );
                return v___x_1349_;
            }
            7 => {
                v___x_1356_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1356_, 0, v___x_1355_);
                leanh::lean_ctor_set(v___x_1356_, 1, v_res_1353_);
                v___x_1357_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1356_,
                );
                return v___x_1357_;
            }
            8 => {
                v___x_1366_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1366_, 0, v___x_1365_);
                leanh::lean_ctor_set(v___x_1366_, 1, v_res_1363_);
                v___x_1367_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1366_,
                );
                return v___x_1367_;
            }
            9 => {
                v___x_1375_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
                v___x_1376_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1375_,
                );
                return v___x_1376_;
            }
            10 => {
                v___x_1385_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                leanh::lean_ctor_set(v___x_1385_, 1, v_res_1381_);
                v___x_1386_ = leanh::lean_apply_4(
                    v_lift_1265_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1385_,
                );
                return v___x_1386_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed(
    mut v___y_1391_: *mut leanh::LeanObject,
    mut v_s_1392_: *mut leanh::LeanObject,
    mut v_lift_1393_: *mut leanh::LeanObject,
    mut v_it_1394_: *mut leanh::LeanObject,
    mut v_acc_1395_: *mut leanh::LeanObject,
    mut v_hP_1396_: *mut leanh::LeanObject,
    mut v_recur_1397_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(
        v___y_1391_,
        v_s_1392_,
        v_lift_1393_,
        v_it_1394_,
        v_acc_1395_,
        v_hP_1396_,
        v_recur_1397_,
    );
    leanh::lean_dec_ref(v_s_1392_);
    return v_res_1398_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(
    mut v_s_1399_: *mut leanh::LeanObject,
    mut v_lift_1400_: *mut leanh::LeanObject,
    mut v_00_u03b3_1401_: *mut leanh::LeanObject,
    mut v_Pl_1402_: *mut leanh::LeanObject,
    mut v_it_1403_: *mut leanh::LeanObject,
    mut v_init_1404_: *mut leanh::LeanObject,
    mut v___y_1405_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1406_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed
            as *mut core::ffi::c_void,
        7,
        3,
    );
    leanh::lean_closure_set(v___f_1406_, 0, v___y_1405_);
    leanh::lean_closure_set(v___f_1406_, 1, v_s_1399_);
    leanh::lean_closure_set(v___f_1406_, 2, v_lift_1400_);
    v___x_1407_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1406_,
        v_it_1403_,
        v_init_1404_,
        leanh::lean_box(0),
    );
    return v___x_1407_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(
    mut v_s_1408_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1409_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1409_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2
            as *mut core::ffi::c_void,
        7,
        1,
    );
    leanh::lean_closure_set(v___f_1409_, 0, v_s_1408_);
    return v___f_1409_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(
    mut v_pat_1410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1411_, 0, v_pat_1410_);
    return v___x_1411_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(
    mut v_pat_1412_: *mut leanh::LeanObject,
    mut v_s_1413_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_1414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    v_str_1414_ = leanh::lean_ctor_get(v_pat_1412_, 0);
    v_startInclusive_1415_ = leanh::lean_ctor_get(v_pat_1412_, 1);
    v_endExclusive_1416_ = leanh::lean_ctor_get(v_pat_1412_, 2);
    v_str_1417_ = leanh::lean_ctor_get(v_s_1413_, 0);
    v_startInclusive_1418_ = leanh::lean_ctor_get(v_s_1413_, 1);
    v_endExclusive_1419_ = leanh::lean_ctor_get(v_s_1413_, 2);
    v___x_1420_ = lean_nat_sub(v_endExclusive_1416_, v_startInclusive_1415_);
    v___x_1421_ = lean_nat_sub(v_endExclusive_1419_, v_startInclusive_1418_);
    v___x_1422_ = lean_nat_dec_le(v___x_1420_, v___x_1421_);
    leanh::lean_dec(v___x_1421_);
    if v___x_1422_ == 0 {
        leanh::lean_dec(v___x_1420_);
        return v___x_1422_;
    } else {
        let mut v___x_1423_: u8 = 0;
        v___x_1423_ = lean_string_memcmp(
            v_str_1417_,
            v_str_1414_,
            v_startInclusive_1418_,
            v_startInclusive_1415_,
            v___x_1420_,
        );
        leanh::lean_dec(v___x_1420_);
        return v___x_1423_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(
    mut v_pat_1424_: *mut leanh::LeanObject,
    mut v_s_1425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1426_: u8 = 0;
    let mut v_r_1427_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_1424_, v_s_1425_);
    leanh::lean_dec_ref(v_s_1425_);
    leanh::lean_dec_ref(v_pat_1424_);
    v_r_1427_ = leanh::lean_box((v_res_1426_) as usize);
    return v_r_1427_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(
    mut v_pat_1428_: *mut leanh::LeanObject,
    mut v_s_1429_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    v_str_1430_ = leanh::lean_ctor_get(v_pat_1428_, 0);
    v_startInclusive_1431_ = leanh::lean_ctor_get(v_pat_1428_, 1);
    v_endExclusive_1432_ = leanh::lean_ctor_get(v_pat_1428_, 2);
    v_str_1433_ = leanh::lean_ctor_get(v_s_1429_, 0);
    v_startInclusive_1434_ = leanh::lean_ctor_get(v_s_1429_, 1);
    v_endExclusive_1435_ = leanh::lean_ctor_get(v_s_1429_, 2);
    v___x_1436_ = lean_nat_sub(v_endExclusive_1432_, v_startInclusive_1431_);
    v___x_1437_ = lean_nat_sub(v_endExclusive_1435_, v_startInclusive_1434_);
    v___x_1438_ = lean_nat_dec_le(v___x_1436_, v___x_1437_);
    leanh::lean_dec(v___x_1437_);
    if v___x_1438_ == 0 {
        let mut v___x_1439_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1436_);
        v___x_1439_ = leanh::lean_box(0);
        return v___x_1439_;
    } else {
        let mut v___x_1440_: u8 = 0;
        v___x_1440_ = lean_string_memcmp(
            v_str_1433_,
            v_str_1430_,
            v_startInclusive_1434_,
            v_startInclusive_1431_,
            v___x_1436_,
        );
        if v___x_1440_ == 0 {
            let mut v___x_1441_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1436_);
            v___x_1441_ = leanh::lean_box(0);
            return v___x_1441_;
        } else {
            let mut v___x_1442_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1443_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1442_ = l_String_Slice_pos_x21(v_s_1429_, v___x_1436_);
            leanh::lean_dec(v___x_1436_);
            v___x_1443_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
            return v___x_1443_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(
    mut v_pat_1444_: *mut leanh::LeanObject,
    mut v_s_1445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_1444_, v_s_1445_);
    leanh::lean_dec_ref(v_s_1445_);
    leanh::lean_dec_ref(v_pat_1444_);
    return v_res_1446_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(
    mut v_pat_1447_: *mut leanh::LeanObject,
    mut v_s_1448_: *mut leanh::LeanObject,
    mut v_x_1449_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    v_str_1450_ = leanh::lean_ctor_get(v_pat_1447_, 0);
    v_startInclusive_1451_ = leanh::lean_ctor_get(v_pat_1447_, 1);
    v_endExclusive_1452_ = leanh::lean_ctor_get(v_pat_1447_, 2);
    v_str_1453_ = leanh::lean_ctor_get(v_s_1448_, 0);
    v_startInclusive_1454_ = leanh::lean_ctor_get(v_s_1448_, 1);
    v_endExclusive_1455_ = leanh::lean_ctor_get(v_s_1448_, 2);
    v___x_1456_ = lean_nat_sub(v_endExclusive_1452_, v_startInclusive_1451_);
    v___x_1457_ = lean_nat_sub(v_endExclusive_1455_, v_startInclusive_1454_);
    v___x_1458_ = lean_nat_dec_le(v___x_1456_, v___x_1457_);
    leanh::lean_dec(v___x_1457_);
    if v___x_1458_ == 0 {
        let mut v___x_1459_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1456_);
        v___x_1459_ = leanh::lean_box(0);
        return v___x_1459_;
    } else {
        let mut v___x_1460_: u8 = 0;
        v___x_1460_ = lean_string_memcmp(
            v_str_1453_,
            v_str_1450_,
            v_startInclusive_1454_,
            v_startInclusive_1451_,
            v___x_1456_,
        );
        if v___x_1460_ == 0 {
            let mut v___x_1461_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1456_);
            v___x_1461_ = leanh::lean_box(0);
            return v___x_1461_;
        } else {
            let mut v___x_1462_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1463_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1462_ = l_String_Slice_pos_x21(v_s_1448_, v___x_1456_);
            leanh::lean_dec(v___x_1456_);
            v___x_1463_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1463_, 0, v___x_1462_);
            return v___x_1463_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(
    mut v_pat_1464_: *mut leanh::LeanObject,
    mut v_s_1465_: *mut leanh::LeanObject,
    mut v_x_1466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(
        v_pat_1464_,
        v_s_1465_,
        v_x_1466_,
    );
    leanh::lean_dec_ref(v_s_1465_);
    leanh::lean_dec_ref(v_pat_1464_);
    return v_res_1467_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(
    mut v_pat_1468_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_pat_1468_, 2);
    v___f_1469_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1469_, 0, v_pat_1468_);
    v___x_1470_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1470_, 0, v_pat_1468_);
    v___x_1471_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1471_, 0, v_pat_1468_);
    v___x_1472_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1472_, 0, v___x_1470_);
    leanh::lean_ctor_set(v___x_1472_, 1, v___f_1469_);
    leanh::lean_ctor_set(v___x_1472_, 2, v___x_1471_);
    return v___x_1472_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(
    mut v_pat_1473_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = leanh::lean_unsigned_to_nat(0);
    v___x_1475_ = lean_string_utf8_byte_size(v_pat_1473_);
    v___x_1476_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1476_, 0, v_pat_1473_);
    leanh::lean_ctor_set(v___x_1476_, 1, v___x_1474_);
    leanh::lean_ctor_set(v___x_1476_, 2, v___x_1475_);
    v___x_1477_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1477_, 0, v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(
    mut v___x_1478_: *mut leanh::LeanObject,
    mut v_pat_1479_: *mut leanh::LeanObject,
    mut v___x_1480_: *mut leanh::LeanObject,
    mut v_s_1481_: *mut leanh::LeanObject,
    mut v_x_1482_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    v_str_1483_ = leanh::lean_ctor_get(v_s_1481_, 0);
    v_startInclusive_1484_ = leanh::lean_ctor_get(v_s_1481_, 1);
    v_endExclusive_1485_ = leanh::lean_ctor_get(v_s_1481_, 2);
    v___x_1486_ = lean_nat_sub(v_endExclusive_1485_, v_startInclusive_1484_);
    v___x_1487_ = lean_nat_dec_le(v___x_1478_, v___x_1486_);
    leanh::lean_dec(v___x_1486_);
    if v___x_1487_ == 0 {
        let mut v___x_1488_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_1488_ = leanh::lean_box(0);
        return v___x_1488_;
    } else {
        let mut v___x_1489_: u8 = 0;
        v___x_1489_ = lean_string_memcmp(
            v_str_1483_,
            v_pat_1479_,
            v_startInclusive_1484_,
            v___x_1480_,
            v___x_1478_,
        );
        if v___x_1489_ == 0 {
            let mut v___x_1490_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1490_ = leanh::lean_box(0);
            return v___x_1490_;
        } else {
            let mut v___x_1491_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1492_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1491_ = l_String_Slice_pos_x21(v_s_1481_, v___x_1478_);
            v___x_1492_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
            return v___x_1492_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(
    mut v___x_1493_: *mut leanh::LeanObject,
    mut v_pat_1494_: *mut leanh::LeanObject,
    mut v___x_1495_: *mut leanh::LeanObject,
    mut v_s_1496_: *mut leanh::LeanObject,
    mut v_x_1497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(
        v___x_1493_,
        v_pat_1494_,
        v___x_1495_,
        v_s_1496_,
        v_x_1497_,
    );
    leanh::lean_dec_ref(v_s_1496_);
    leanh::lean_dec(v___x_1495_);
    leanh::lean_dec_ref(v_pat_1494_);
    leanh::lean_dec(v___x_1493_);
    return v_res_1498_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(
    mut v_pat_1499_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = leanh::lean_unsigned_to_nat(0);
    v___x_1501_ = lean_string_utf8_byte_size(v_pat_1499_);
    leanh::lean_inc_ref(v_pat_1499_);
    v___f_1502_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_1502_, 0, v___x_1501_);
    leanh::lean_closure_set(v___f_1502_, 1, v_pat_1499_);
    leanh::lean_closure_set(v___f_1502_, 2, v___x_1500_);
    v___x_1503_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1503_, 0, v_pat_1499_);
    leanh::lean_ctor_set(v___x_1503_, 1, v___x_1500_);
    leanh::lean_ctor_set(v___x_1503_, 2, v___x_1501_);
    leanh::lean_inc_ref(v___x_1503_);
    v___x_1504_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1504_, 0, v___x_1503_);
    v___x_1505_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1505_, 0, v___x_1503_);
    v___x_1506_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1506_, 0, v___x_1504_);
    leanh::lean_ctor_set(v___x_1506_, 1, v___f_1502_);
    leanh::lean_ctor_set(v___x_1506_, 2, v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(
    mut v_pat_1507_: *mut leanh::LeanObject,
    mut v_s_1508_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_1509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    v_str_1509_ = leanh::lean_ctor_get(v_pat_1507_, 0);
    v_startInclusive_1510_ = leanh::lean_ctor_get(v_pat_1507_, 1);
    v_endExclusive_1511_ = leanh::lean_ctor_get(v_pat_1507_, 2);
    v_str_1512_ = leanh::lean_ctor_get(v_s_1508_, 0);
    v_startInclusive_1513_ = leanh::lean_ctor_get(v_s_1508_, 1);
    v_endExclusive_1514_ = leanh::lean_ctor_get(v_s_1508_, 2);
    v___x_1515_ = lean_nat_sub(v_endExclusive_1511_, v_startInclusive_1510_);
    v___x_1516_ = lean_nat_sub(v_endExclusive_1514_, v_startInclusive_1513_);
    v___x_1517_ = lean_nat_dec_le(v___x_1515_, v___x_1516_);
    if v___x_1517_ == 0 {
        leanh::lean_dec(v___x_1516_);
        leanh::lean_dec(v___x_1515_);
        return v___x_1517_;
    } else {
        let mut v___x_1518_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: u8 = 0;
        v___x_1518_ = lean_nat_sub(v___x_1516_, v___x_1515_);
        leanh::lean_dec(v___x_1516_);
        v___x_1519_ = lean_nat_add(v_startInclusive_1513_, v___x_1518_);
        leanh::lean_dec(v___x_1518_);
        v___x_1520_ = lean_string_memcmp(
            v_str_1512_,
            v_str_1509_,
            v___x_1519_,
            v_startInclusive_1510_,
            v___x_1515_,
        );
        leanh::lean_dec(v___x_1515_);
        leanh::lean_dec(v___x_1519_);
        return v___x_1520_;
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(
    mut v_pat_1521_: *mut leanh::LeanObject,
    mut v_s_1522_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1523_: u8 = 0;
    let mut v_r_1524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_1521_, v_s_1522_);
    leanh::lean_dec_ref(v_s_1522_);
    leanh::lean_dec_ref(v_pat_1521_);
    v_r_1524_ = leanh::lean_box((v_res_1523_) as usize);
    return v_r_1524_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(
    mut v_pat_1525_: *mut leanh::LeanObject,
    mut v_s_1526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    v_str_1527_ = leanh::lean_ctor_get(v_pat_1525_, 0);
    v_startInclusive_1528_ = leanh::lean_ctor_get(v_pat_1525_, 1);
    v_endExclusive_1529_ = leanh::lean_ctor_get(v_pat_1525_, 2);
    v_str_1530_ = leanh::lean_ctor_get(v_s_1526_, 0);
    v_startInclusive_1531_ = leanh::lean_ctor_get(v_s_1526_, 1);
    v_endExclusive_1532_ = leanh::lean_ctor_get(v_s_1526_, 2);
    v___x_1533_ = lean_nat_sub(v_endExclusive_1529_, v_startInclusive_1528_);
    v___x_1534_ = lean_nat_sub(v_endExclusive_1532_, v_startInclusive_1531_);
    v___x_1535_ = lean_nat_dec_le(v___x_1533_, v___x_1534_);
    if v___x_1535_ == 0 {
        let mut v___x_1536_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1534_);
        leanh::lean_dec(v___x_1533_);
        v___x_1536_ = leanh::lean_box(0);
        return v___x_1536_;
    } else {
        let mut v___x_1537_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: u8 = 0;
        v___x_1537_ = lean_nat_sub(v___x_1534_, v___x_1533_);
        leanh::lean_dec(v___x_1534_);
        v___x_1538_ = lean_nat_add(v_startInclusive_1531_, v___x_1537_);
        v___x_1539_ = lean_string_memcmp(
            v_str_1530_,
            v_str_1527_,
            v___x_1538_,
            v_startInclusive_1528_,
            v___x_1533_,
        );
        leanh::lean_dec(v___x_1533_);
        leanh::lean_dec(v___x_1538_);
        if v___x_1539_ == 0 {
            let mut v___x_1540_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1537_);
            v___x_1540_ = leanh::lean_box(0);
            return v___x_1540_;
        } else {
            let mut v___x_1541_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1542_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1541_ = l_String_Slice_pos_x21(v_s_1526_, v___x_1537_);
            leanh::lean_dec(v___x_1537_);
            v___x_1542_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
            return v___x_1542_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(
    mut v_pat_1543_: *mut leanh::LeanObject,
    mut v_s_1544_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1545_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ =
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_1543_, v_s_1544_);
    leanh::lean_dec_ref(v_s_1544_);
    leanh::lean_dec_ref(v_pat_1543_);
    return v_res_1545_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(
    mut v_pat_1546_: *mut leanh::LeanObject,
    mut v_s_1547_: *mut leanh::LeanObject,
    mut v_x_1548_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1550_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    v_str_1549_ = leanh::lean_ctor_get(v_pat_1546_, 0);
    v_startInclusive_1550_ = leanh::lean_ctor_get(v_pat_1546_, 1);
    v_endExclusive_1551_ = leanh::lean_ctor_get(v_pat_1546_, 2);
    v_str_1552_ = leanh::lean_ctor_get(v_s_1547_, 0);
    v_startInclusive_1553_ = leanh::lean_ctor_get(v_s_1547_, 1);
    v_endExclusive_1554_ = leanh::lean_ctor_get(v_s_1547_, 2);
    v___x_1555_ = lean_nat_sub(v_endExclusive_1551_, v_startInclusive_1550_);
    v___x_1556_ = lean_nat_sub(v_endExclusive_1554_, v_startInclusive_1553_);
    v___x_1557_ = lean_nat_dec_le(v___x_1555_, v___x_1556_);
    if v___x_1557_ == 0 {
        let mut v___x_1558_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1556_);
        leanh::lean_dec(v___x_1555_);
        v___x_1558_ = leanh::lean_box(0);
        return v___x_1558_;
    } else {
        let mut v___x_1559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: u8 = 0;
        v___x_1559_ = lean_nat_sub(v___x_1556_, v___x_1555_);
        leanh::lean_dec(v___x_1556_);
        v___x_1560_ = lean_nat_add(v_startInclusive_1553_, v___x_1559_);
        v___x_1561_ = lean_string_memcmp(
            v_str_1552_,
            v_str_1549_,
            v___x_1560_,
            v_startInclusive_1550_,
            v___x_1555_,
        );
        leanh::lean_dec(v___x_1555_);
        leanh::lean_dec(v___x_1560_);
        if v___x_1561_ == 0 {
            let mut v___x_1562_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1559_);
            v___x_1562_ = leanh::lean_box(0);
            return v___x_1562_;
        } else {
            let mut v___x_1563_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1564_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1563_ = l_String_Slice_pos_x21(v_s_1547_, v___x_1559_);
            leanh::lean_dec(v___x_1559_);
            v___x_1564_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1564_, 0, v___x_1563_);
            return v___x_1564_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(
    mut v_pat_1565_: *mut leanh::LeanObject,
    mut v_s_1566_: *mut leanh::LeanObject,
    mut v_x_1567_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1568_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(
        v_pat_1565_,
        v_s_1566_,
        v_x_1567_,
    );
    leanh::lean_dec_ref(v_s_1566_);
    leanh::lean_dec_ref(v_pat_1565_);
    return v_res_1568_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(
    mut v_pat_1569_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc_ref_n(v_pat_1569_, 2);
    v___f_1570_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___f_1570_, 0, v_pat_1569_);
    v___x_1571_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1571_, 0, v_pat_1569_);
    v___x_1572_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1572_, 0, v_pat_1569_);
    v___x_1573_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1573_, 0, v___x_1571_);
    leanh::lean_ctor_set(v___x_1573_, 1, v___f_1570_);
    leanh::lean_ctor_set(v___x_1573_, 2, v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(
    mut v___x_1574_: *mut leanh::LeanObject,
    mut v_pat_1575_: *mut leanh::LeanObject,
    mut v___x_1576_: *mut leanh::LeanObject,
    mut v_s_1577_: *mut leanh::LeanObject,
    mut v_x_1578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    v_str_1579_ = leanh::lean_ctor_get(v_s_1577_, 0);
    v_startInclusive_1580_ = leanh::lean_ctor_get(v_s_1577_, 1);
    v_endExclusive_1581_ = leanh::lean_ctor_get(v_s_1577_, 2);
    v___x_1582_ = lean_nat_sub(v_endExclusive_1581_, v_startInclusive_1580_);
    v___x_1583_ = lean_nat_dec_le(v___x_1574_, v___x_1582_);
    if v___x_1583_ == 0 {
        let mut v___x_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v___x_1582_);
        v___x_1584_ = leanh::lean_box(0);
        return v___x_1584_;
    } else {
        let mut v___x_1585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: u8 = 0;
        v___x_1585_ = lean_nat_sub(v___x_1582_, v___x_1574_);
        leanh::lean_dec(v___x_1582_);
        v___x_1586_ = lean_nat_add(v_startInclusive_1580_, v___x_1585_);
        v___x_1587_ = lean_string_memcmp(
            v_str_1579_,
            v_pat_1575_,
            v___x_1586_,
            v___x_1576_,
            v___x_1574_,
        );
        leanh::lean_dec(v___x_1586_);
        if v___x_1587_ == 0 {
            let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v___x_1585_);
            v___x_1588_ = leanh::lean_box(0);
            return v___x_1588_;
        } else {
            let mut v___x_1589_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1590_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_1589_ = l_String_Slice_pos_x21(v_s_1577_, v___x_1585_);
            leanh::lean_dec(v___x_1585_);
            v___x_1590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
            leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
            return v___x_1590_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(
    mut v___x_1591_: *mut leanh::LeanObject,
    mut v_pat_1592_: *mut leanh::LeanObject,
    mut v___x_1593_: *mut leanh::LeanObject,
    mut v_s_1594_: *mut leanh::LeanObject,
    mut v_x_1595_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1596_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(
        v___x_1591_,
        v_pat_1592_,
        v___x_1593_,
        v_s_1594_,
        v_x_1595_,
    );
    leanh::lean_dec_ref(v_s_1594_);
    leanh::lean_dec(v___x_1593_);
    leanh::lean_dec_ref(v_pat_1592_);
    leanh::lean_dec(v___x_1591_);
    return v_res_1596_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(
    mut v_pat_1597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = leanh::lean_unsigned_to_nat(0);
    v___x_1599_ = lean_string_utf8_byte_size(v_pat_1597_);
    leanh::lean_inc_ref(v_pat_1597_);
    v___f_1600_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    leanh::lean_closure_set(v___f_1600_, 0, v___x_1599_);
    leanh::lean_closure_set(v___f_1600_, 1, v_pat_1597_);
    leanh::lean_closure_set(v___f_1600_, 2, v___x_1598_);
    v___x_1601_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1601_, 0, v_pat_1597_);
    leanh::lean_ctor_set(v___x_1601_, 1, v___x_1598_);
    leanh::lean_ctor_set(v___x_1601_, 2, v___x_1599_);
    leanh::lean_inc_ref(v___x_1601_);
    v___x_1602_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1602_, 0, v___x_1601_);
    v___x_1603_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___x_1603_, 0, v___x_1601_);
    v___x_1604_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
    leanh::lean_ctor_set(v___x_1604_, 1, v___f_1600_);
    leanh::lean_ctor_set(v___x_1604_, 2, v___x_1603_);
    return v___x_1604_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_String(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_String(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Pattern_String(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_String(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_String(builtin);
}
// Lean compiler output
// Module: Init.Data.String.Pattern.String
// Imports: Init.Data.String.Pattern.Basic Init.Data.Vector.Basic Init.Data.String.FindPos Init.Data.String.Termination Init.Data.String.Lemmas.FindPos Init.ByCases Init.Data.Array.Lemmas Init.Data.Option.Lemmas Init.Omega
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
use crate::lean_imports_rs::Init::Data::String::Basic::lean_string_utf8_next_fast;
use crate::lean_imports_rs::Init::Data::String::Pattern::Basic::lean_string_memcmp;
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size, lean_uint8_dec_eq,
};
pub static l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value:
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
static mut l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value:
    crate::leanh::LeanCtorObject<1> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 0,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0_value
) as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(
    mut v_pat_803_: *mut crate::leanh::LeanObject,
    mut v_patByte_804_: u8,
    mut v_table_805_: *mut crate::leanh::LeanObject,
    mut v_guess_806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: u8 = 0;
    let mut v___x_811_: u8 = 0;
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: u8 = 0;
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_807_ = crate::leanh::lean_ctor_get(v_pat_803_, 0);
                v_startInclusive_808_ = crate::leanh::lean_ctor_get(v_pat_803_, 1);
                v___x_809_ = lean_nat_add(v_startInclusive_808_, v_guess_806_);
                v___x_810_ = lean_string_get_byte_fast(v_str_807_, v___x_809_);
                v___x_811_ = lean_uint8_dec_eq(v___x_810_, v_patByte_804_);
                if v___x_811_ == 0 {
                    v___x_812_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_813_ = lean_nat_dec_eq(v_guess_806_, v___x_812_);
                    if v___x_813_ == 0 {
                        v___x_814_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_815_ = lean_nat_sub(v_guess_806_, v___x_814_);
                        v___x_816_ = lean_array_fget_borrowed(v_table_805_, v___x_815_);
                        crate::leanh::lean_dec(v___x_815_);
                        v_guess_806_ = v___x_816_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_812_;
                    }
                } else {
                    v___x_818_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_819_ = lean_nat_add(v_guess_806_, v___x_818_);
                    return v___x_819_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg___boxed(
    mut v_pat_820_: *mut crate::leanh::LeanObject,
    mut v_patByte_821_: *mut crate::leanh::LeanObject,
    mut v_table_822_: *mut crate::leanh::LeanObject,
    mut v_guess_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_patByte_boxed_824_: u8 = 0;
    let mut v_res_825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_patByte_boxed_824_ = (crate::leanh::lean_unbox(v_patByte_821_) as u8);
    v_res_825_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_820_, v_patByte_boxed_824_, v_table_822_, v_guess_823_);
    crate::leanh::lean_dec(v_guess_823_);
    crate::leanh::lean_dec_ref(v_table_822_);
    crate::leanh::lean_dec_ref(v_pat_820_);
    return v_res_825_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(
    mut v_pat_826_: *mut crate::leanh::LeanObject,
    mut v_patByte_827_: u8,
    mut v_table_828_: *mut crate::leanh::LeanObject,
    mut v_ht_829_: *mut crate::leanh::LeanObject,
    mut v_h_830_: *mut crate::leanh::LeanObject,
    mut v_guess_831_: *mut crate::leanh::LeanObject,
    mut v_hg_832_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_833_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___redArg(v_pat_826_, v_patByte_827_, v_table_828_, v_guess_831_);
    return v___x_833_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance___boxed(
    mut v_pat_834_: *mut crate::leanh::LeanObject,
    mut v_patByte_835_: *mut crate::leanh::LeanObject,
    mut v_table_836_: *mut crate::leanh::LeanObject,
    mut v_ht_837_: *mut crate::leanh::LeanObject,
    mut v_h_838_: *mut crate::leanh::LeanObject,
    mut v_guess_839_: *mut crate::leanh::LeanObject,
    mut v_hg_840_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_patByte_boxed_841_: u8 = 0;
    let mut v_res_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_patByte_boxed_841_ = (crate::leanh::lean_unbox(v_patByte_835_) as u8);
    v_res_842_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_computeDistance(v_pat_834_, v_patByte_boxed_841_, v_table_836_, v_ht_837_, v_h_838_, v_guess_839_, v_hg_840_);
    crate::leanh::lean_dec(v_guess_839_);
    crate::leanh::lean_dec_ref(v_table_836_);
    crate::leanh::lean_dec_ref(v_pat_834_);
    return v_res_842_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(
    mut v_pat_843_: *mut crate::leanh::LeanObject,
    mut v_table_844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_850_: u8 = 0;
    let mut v___x_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_852_: u8 = 0;
    let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_dist_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_845_ = crate::leanh::lean_ctor_get(v_pat_843_, 0);
                v_startInclusive_846_ = crate::leanh::lean_ctor_get(v_pat_843_, 1);
                v_endExclusive_847_ = crate::leanh::lean_ctor_get(v_pat_843_, 2);
                v___x_848_ = lean_array_get_size(v_table_844_);
                v___x_849_ = lean_nat_sub(v_endExclusive_847_, v_startInclusive_846_);
                v___x_850_ = lean_nat_dec_lt(v___x_848_, v___x_849_);
                crate::leanh::lean_dec(v___x_849_);
                if v___x_850_ == 0 {
                    return v_table_844_;
                } else {
                    v___x_851_ = lean_nat_add(v_startInclusive_846_, v___x_848_);
                    v_patByte_852_ = lean_string_get_byte_fast(v_str_845_, v___x_851_);
                    v___x_853_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_854_ = lean_nat_sub(v___x_848_, v___x_853_);
                    v___x_855_ = lean_array_fget_borrowed(v_table_844_, v___x_854_);
                    crate::leanh::lean_dec(v___x_854_);
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
    mut v_pat_859_: *mut crate::leanh::LeanObject,
    mut v_table_860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_861_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_859_, v_table_860_);
    crate::leanh::lean_dec_ref(v_pat_859_);
    return v_res_861_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(
    mut v_pat_862_: *mut crate::leanh::LeanObject,
    mut v_table_863_: *mut crate::leanh::LeanObject,
    mut v_ht_u2080_864_: *mut crate::leanh::LeanObject,
    mut v_ht_865_: *mut crate::leanh::LeanObject,
    mut v_h_866_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_867_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_862_, v_table_863_);
    return v___x_867_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___boxed(
    mut v_pat_868_: *mut crate::leanh::LeanObject,
    mut v_table_869_: *mut crate::leanh::LeanObject,
    mut v_ht_u2080_870_: *mut crate::leanh::LeanObject,
    mut v_ht_871_: *mut crate::leanh::LeanObject,
    mut v_h_872_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_873_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go(v_pat_868_, v_table_869_, v_ht_u2080_870_, v_ht_871_, v_h_872_);
    crate::leanh::lean_dec_ref(v_pat_868_);
    return v_res_873_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(
    mut v_pat_876_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_881_: u8 = 0;
    v_startInclusive_877_ = crate::leanh::lean_ctor_get(v_pat_876_, 1);
    v_endExclusive_878_ = crate::leanh::lean_ctor_get(v_pat_876_, 2);
    v___x_879_ = lean_nat_sub(v_endExclusive_878_, v_startInclusive_877_);
    v___x_880_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_881_ = lean_nat_dec_eq(v___x_879_, v___x_880_);
    if v___x_881_ == 0 {
        let mut v_arr_882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_arr_x27_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_arr_882_ = lean_mk_empty_array_with_capacity(v___x_879_);
        crate::leanh::lean_dec(v___x_879_);
        v_arr_x27_883_ = lean_array_push(v_arr_882_, v___x_880_);
        v___x_884_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_buildTable_go___redArg(v_pat_876_, v_arr_x27_883_);
        return v___x_884_;
    } else {
        let mut v___x_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_879_);
        v___x_885_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___closed__0;
        return v___x_885_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_buildTable___boxed(
    mut v_pat_886_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_887_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_886_);
    crate::leanh::lean_dec_ref(v_pat_886_);
    return v_res_887_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(
    mut v_x_888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_888_) {
        0 => {
            let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_889_ = crate::leanh::lean_unsigned_to_nat(0);
            return v___x_889_;
        }
        1 => {
            let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_890_ = crate::leanh::lean_unsigned_to_nat(1);
            return v___x_890_;
        }
        2 => {
            let mut v___x_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_891_ = crate::leanh::lean_unsigned_to_nat(2);
            return v___x_891_;
        }
        _ => {
            let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_892_ = crate::leanh::lean_unsigned_to_nat(3);
            return v___x_892_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg___boxed(
    mut v_x_893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_894_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_893_);
    crate::leanh::lean_dec(v_x_893_);
    return v_res_894_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(
    mut v_s_895_: *mut crate::leanh::LeanObject,
    mut v_x_896_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_897_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___redArg(v_x_896_);
    return v___x_897_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx___boxed(
    mut v_s_898_: *mut crate::leanh::LeanObject,
    mut v_x_899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_900_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorIdx(v_s_898_, v_x_899_);
    crate::leanh::lean_dec(v_x_899_);
    crate::leanh::lean_dec_ref(v_s_898_);
    return v_res_900_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(
    mut v_t_901_: *mut crate::leanh::LeanObject,
    mut v_k_902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_t_901_) {
        0 => {
            let mut v_pos_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pos_903_ = crate::leanh::lean_ctor_get(v_t_901_, 0);
            crate::leanh::lean_inc(v_pos_903_);
            crate::leanh::lean_dec_ref_known(v_t_901_, 1);
            v___x_904_ = crate::leanh::lean_apply_1(v_k_902_, v_pos_903_);
            return v___x_904_;
        }
        1 => {
            let mut v_pos_905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_pos_905_ = crate::leanh::lean_ctor_get(v_t_901_, 0);
            crate::leanh::lean_inc(v_pos_905_);
            crate::leanh::lean_dec_ref_known(v_t_901_, 1);
            v___x_906_ =
                crate::leanh::lean_apply_2(v_k_902_, v_pos_905_, crate::leanh::lean_box(0));
            return v___x_906_;
        }
        2 => {
            let mut v_needle_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_needle_907_ = crate::leanh::lean_ctor_get(v_t_901_, 0);
            crate::leanh::lean_inc_ref(v_needle_907_);
            v_table_908_ = crate::leanh::lean_ctor_get(v_t_901_, 1);
            crate::leanh::lean_inc_ref(v_table_908_);
            v_stackPos_909_ = crate::leanh::lean_ctor_get(v_t_901_, 2);
            crate::leanh::lean_inc(v_stackPos_909_);
            v_needlePos_910_ = crate::leanh::lean_ctor_get(v_t_901_, 3);
            crate::leanh::lean_inc(v_needlePos_910_);
            crate::leanh::lean_dec_ref_known(v_t_901_, 4);
            v___x_911_ = crate::leanh::lean_apply_6(
                v_k_902_,
                v_needle_907_,
                v_table_908_,
                crate::leanh::lean_box(0),
                v_stackPos_909_,
                v_needlePos_910_,
                crate::leanh::lean_box(0),
            );
            return v___x_911_;
        }
        _ => {
            return v_k_902_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(
    mut v_s_912_: *mut crate::leanh::LeanObject,
    mut v_motive_913_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_914_: *mut crate::leanh::LeanObject,
    mut v_t_915_: *mut crate::leanh::LeanObject,
    mut v_h_916_: *mut crate::leanh::LeanObject,
    mut v_k_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_918_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_915_, v_k_917_);
    return v___x_918_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___boxed(
    mut v_s_919_: *mut crate::leanh::LeanObject,
    mut v_motive_920_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_921_: *mut crate::leanh::LeanObject,
    mut v_t_922_: *mut crate::leanh::LeanObject,
    mut v_h_923_: *mut crate::leanh::LeanObject,
    mut v_k_924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_925_ = l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim(
        v_s_919_,
        v_motive_920_,
        v_ctorIdx_921_,
        v_t_922_,
        v_h_923_,
        v_k_924_,
    );
    crate::leanh::lean_dec(v_ctorIdx_921_);
    crate::leanh::lean_dec_ref(v_s_919_);
    return v_res_925_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___redArg(
    mut v_t_926_: *mut crate::leanh::LeanObject,
    mut v_emptyBefore_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_928_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_926_, v_emptyBefore_927_);
    return v___x_928_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(
    mut v_s_929_: *mut crate::leanh::LeanObject,
    mut v_motive_930_: *mut crate::leanh::LeanObject,
    mut v_t_931_: *mut crate::leanh::LeanObject,
    mut v_h_932_: *mut crate::leanh::LeanObject,
    mut v_emptyBefore_933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_934_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_931_, v_emptyBefore_933_);
    return v___x_934_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim___boxed(
    mut v_s_935_: *mut crate::leanh::LeanObject,
    mut v_motive_936_: *mut crate::leanh::LeanObject,
    mut v_t_937_: *mut crate::leanh::LeanObject,
    mut v_h_938_: *mut crate::leanh::LeanObject,
    mut v_emptyBefore_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_940_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyBefore_elim(
        v_s_935_,
        v_motive_936_,
        v_t_937_,
        v_h_938_,
        v_emptyBefore_939_,
    );
    crate::leanh::lean_dec_ref(v_s_935_);
    return v_res_940_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___redArg(
    mut v_t_941_: *mut crate::leanh::LeanObject,
    mut v_emptyAt_942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_943_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_941_, v_emptyAt_942_);
    return v___x_943_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(
    mut v_s_944_: *mut crate::leanh::LeanObject,
    mut v_motive_945_: *mut crate::leanh::LeanObject,
    mut v_t_946_: *mut crate::leanh::LeanObject,
    mut v_h_947_: *mut crate::leanh::LeanObject,
    mut v_emptyAt_948_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_949_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_946_, v_emptyAt_948_);
    return v___x_949_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim___boxed(
    mut v_s_950_: *mut crate::leanh::LeanObject,
    mut v_motive_951_: *mut crate::leanh::LeanObject,
    mut v_t_952_: *mut crate::leanh::LeanObject,
    mut v_h_953_: *mut crate::leanh::LeanObject,
    mut v_emptyAt_954_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_955_ = l_String_Slice_Pattern_ForwardSliceSearcher_emptyAt_elim(
        v_s_950_,
        v_motive_951_,
        v_t_952_,
        v_h_953_,
        v_emptyAt_954_,
    );
    crate::leanh::lean_dec_ref(v_s_950_);
    return v_res_955_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___redArg(
    mut v_t_956_: *mut crate::leanh::LeanObject,
    mut v_proper_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_956_, v_proper_957_);
    return v___x_958_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(
    mut v_s_959_: *mut crate::leanh::LeanObject,
    mut v_motive_960_: *mut crate::leanh::LeanObject,
    mut v_t_961_: *mut crate::leanh::LeanObject,
    mut v_h_962_: *mut crate::leanh::LeanObject,
    mut v_proper_963_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_964_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_961_, v_proper_963_);
    return v___x_964_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim___boxed(
    mut v_s_965_: *mut crate::leanh::LeanObject,
    mut v_motive_966_: *mut crate::leanh::LeanObject,
    mut v_t_967_: *mut crate::leanh::LeanObject,
    mut v_h_968_: *mut crate::leanh::LeanObject,
    mut v_proper_969_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_970_ = l_String_Slice_Pattern_ForwardSliceSearcher_proper_elim(
        v_s_965_,
        v_motive_966_,
        v_t_967_,
        v_h_968_,
        v_proper_969_,
    );
    crate::leanh::lean_dec_ref(v_s_965_);
    return v_res_970_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___redArg(
    mut v_t_971_: *mut crate::leanh::LeanObject,
    mut v_atEnd_972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_973_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_971_, v_atEnd_972_);
    return v___x_973_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(
    mut v_s_974_: *mut crate::leanh::LeanObject,
    mut v_motive_975_: *mut crate::leanh::LeanObject,
    mut v_t_976_: *mut crate::leanh::LeanObject,
    mut v_h_977_: *mut crate::leanh::LeanObject,
    mut v_atEnd_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_979_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_ctorElim___redArg(v_t_976_, v_atEnd_978_);
    return v___x_979_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim___boxed(
    mut v_s_980_: *mut crate::leanh::LeanObject,
    mut v_motive_981_: *mut crate::leanh::LeanObject,
    mut v_t_982_: *mut crate::leanh::LeanObject,
    mut v_h_983_: *mut crate::leanh::LeanObject,
    mut v_atEnd_984_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_985_ = l_String_Slice_Pattern_ForwardSliceSearcher_atEnd_elim(
        v_s_980_,
        v_motive_981_,
        v_t_982_,
        v_h_983_,
        v_atEnd_984_,
    );
    crate::leanh::lean_dec_ref(v_s_980_);
    return v_res_985_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(
    mut v_s_988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_989_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
    return v___x_989_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___boxed(
    mut v_s_990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_991_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_s_990_);
    crate::leanh::lean_dec_ref(v_s_990_);
    return v_res_991_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(
    mut v_a_992_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_993_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default(v_a_992_);
    return v___x_993_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited___boxed(
    mut v_a_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_995_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited(v_a_994_);
    crate::leanh::lean_dec_ref(v_a_994_);
    return v_res_995_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter___redArg(
    mut v_pat_996_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: u8 = 0;
    v_startInclusive_997_ = crate::leanh::lean_ctor_get(v_pat_996_, 1);
    v_endExclusive_998_ = crate::leanh::lean_ctor_get(v_pat_996_, 2);
    v___x_999_ = lean_nat_sub(v_endExclusive_998_, v_startInclusive_997_);
    v___x_1000_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1001_ = lean_nat_dec_eq(v___x_999_, v___x_1000_);
    crate::leanh::lean_dec(v___x_999_);
    if v___x_1001_ == 0 {
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1002_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_996_);
        v___x_1003_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1003_, 0, v_pat_996_);
        crate::leanh::lean_ctor_set(v___x_1003_, 1, v___x_1002_);
        crate::leanh::lean_ctor_set(v___x_1003_, 2, v___x_1000_);
        crate::leanh::lean_ctor_set(v___x_1003_, 3, v___x_1000_);
        return v___x_1003_;
    } else {
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_pat_996_);
        v___x_1004_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
        return v___x_1004_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter(
    mut v_pat_1005_: *mut crate::leanh::LeanObject,
    mut v_s_1006_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1011_: u8 = 0;
    v_startInclusive_1007_ = crate::leanh::lean_ctor_get(v_pat_1005_, 1);
    v_endExclusive_1008_ = crate::leanh::lean_ctor_get(v_pat_1005_, 2);
    v___x_1009_ = lean_nat_sub(v_endExclusive_1008_, v_startInclusive_1007_);
    v___x_1010_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1011_ = lean_nat_dec_eq(v___x_1009_, v___x_1010_);
    crate::leanh::lean_dec(v___x_1009_);
    if v___x_1011_ == 0 {
        let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1012_ = l_String_Slice_Pattern_ForwardSliceSearcher_buildTable(v_pat_1005_);
        v___x_1013_ = crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1013_, 0, v_pat_1005_);
        crate::leanh::lean_ctor_set(v___x_1013_, 1, v___x_1012_);
        crate::leanh::lean_ctor_set(v___x_1013_, 2, v___x_1010_);
        crate::leanh::lean_ctor_set(v___x_1013_, 3, v___x_1010_);
        return v___x_1013_;
    } else {
        let mut v___x_1014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_pat_1005_);
        v___x_1014_ = l_String_Slice_Pattern_ForwardSliceSearcher_instInhabited_default___closed__0;
        return v___x_1014_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed(
    mut v_pat_1015_: *mut crate::leanh::LeanObject,
    mut v_s_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1017_ = l_String_Slice_Pattern_ForwardSliceSearcher_iter(v_pat_1015_, v_s_1016_);
    crate::leanh::lean_dec_ref(v_s_1016_);
    return v_res_1017_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(
    mut v_s_1018_: *mut crate::leanh::LeanObject,
    mut v_x_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1023_: u8 = 0;
    let mut v_res_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: u8 = 0;
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1035_: u8 = 0;
    let mut v_pos_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1039_: u8 = 0;
    let mut v_str_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1050_: u8 = 0;
    let mut v_needle_1051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1057_: u8 = 0;
    let mut v_str_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: u8 = 0;
    let mut v___x_1069_: u8 = 0;
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1076_: u8 = 0;
    let mut v___x_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1078_: u8 = 0;
    let mut v___x_1079_: u8 = 0;
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1081_: u8 = 0;
    let mut v___x_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1085_: u8 = 0;
    let mut v_oldBasePos_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBasePos_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1113_: u8 = 0;
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1127_: u8 = 0;
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1019_) {
                0 => {
                    v_pos_1020_ = crate::leanh::lean_ctor_get(v_x_1019_, 0);
                    v_isSharedCheck_1035_ = (!crate::leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1035_ == 0 {
                        v___x_1022_ = v_x_1019_;
                        v_isShared_1023_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1020_);
                        crate::leanh::lean_dec(v_x_1019_);
                        v___x_1022_ = crate::leanh::lean_box(0);
                        v_isShared_1023_ = v_isSharedCheck_1035_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_pos_1036_ = crate::leanh::lean_ctor_get(v_x_1019_, 0);
                    v_isSharedCheck_1050_ = (!crate::leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1050_ == 0 {
                        v___x_1038_ = v_x_1019_;
                        v_isShared_1039_ = v_isSharedCheck_1050_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1036_);
                        crate::leanh::lean_dec(v_x_1019_);
                        v___x_1038_ = crate::leanh::lean_box(0);
                        v_isShared_1039_ = v_isSharedCheck_1050_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_needle_1051_ = crate::leanh::lean_ctor_get(v_x_1019_, 0);
                    v_table_1052_ = crate::leanh::lean_ctor_get(v_x_1019_, 1);
                    v_stackPos_1053_ = crate::leanh::lean_ctor_get(v_x_1019_, 2);
                    v_needlePos_1054_ = crate::leanh::lean_ctor_get(v_x_1019_, 3);
                    v_isSharedCheck_1127_ = (!crate::leanh::lean_is_exclusive(v_x_1019_)) as u8;
                    if v_isSharedCheck_1127_ == 0 {
                        v___x_1056_ = v_x_1019_;
                        v_isShared_1057_ = v_isSharedCheck_1127_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_needlePos_1054_);
                        crate::leanh::lean_inc(v_stackPos_1053_);
                        crate::leanh::lean_inc(v_table_1052_);
                        crate::leanh::lean_inc(v_needle_1051_);
                        crate::leanh::lean_dec(v_x_1019_);
                        v___x_1056_ = crate::leanh::lean_box(0);
                        v_isShared_1057_ = v_isSharedCheck_1127_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v___x_1128_ = crate::leanh::lean_box(2);
                    return v___x_1128_;
                }
            },
            1 => {
                crate::leanh::lean_inc_n(v_pos_1020_, 2);
                v_res_1024_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_res_1024_, 0, v_pos_1020_);
                crate::leanh::lean_ctor_set(v_res_1024_, 1, v_pos_1020_);
                v_startInclusive_1025_ = crate::leanh::lean_ctor_get(v_s_1018_, 1);
                v_endExclusive_1026_ = crate::leanh::lean_ctor_get(v_s_1018_, 2);
                v___x_1027_ = lean_nat_sub(v_endExclusive_1026_, v_startInclusive_1025_);
                v___x_1028_ = lean_nat_dec_eq(v_pos_1020_, v___x_1027_);
                crate::leanh::lean_dec(v___x_1027_);
                if v___x_1028_ == 0 {
                    if v_isShared_1023_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1022_, 1);
                        v___x_1030_ = v___x_1022_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_pos_1020_);
                        v___x_1030_ = v_reuseFailAlloc_1032_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1022_);
                    crate::leanh::lean_dec(v_pos_1020_);
                    v___x_1033_ = crate::leanh::lean_box(3);
                    v___x_1034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1034_, 0, v___x_1033_);
                    crate::leanh::lean_ctor_set(v___x_1034_, 1, v_res_1024_);
                    return v___x_1034_;
                }
            }
            2 => {
                v___x_1031_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1031_, 0, v___x_1030_);
                crate::leanh::lean_ctor_set(v___x_1031_, 1, v_res_1024_);
                return v___x_1031_;
            }
            3 => {
                v_str_1040_ = crate::leanh::lean_ctor_get(v_s_1018_, 0);
                v_startInclusive_1041_ = crate::leanh::lean_ctor_get(v_s_1018_, 1);
                v___x_1042_ = lean_nat_add(v_startInclusive_1041_, v_pos_1036_);
                v___x_1043_ = lean_string_utf8_next_fast(v_str_1040_, v___x_1042_);
                crate::leanh::lean_dec(v___x_1042_);
                v___x_1044_ = lean_nat_sub(v___x_1043_, v_startInclusive_1041_);
                crate::leanh::lean_inc(v___x_1044_);
                v_res_1045_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_res_1045_, 0, v_pos_1036_);
                crate::leanh::lean_ctor_set(v_res_1045_, 1, v___x_1044_);
                if v_isShared_1039_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1038_, 0);
                    crate::leanh::lean_ctor_set(v___x_1038_, 0, v___x_1044_);
                    v___x_1047_ = v___x_1038_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1049_, 0, v___x_1044_);
                    v___x_1047_ = v_reuseFailAlloc_1049_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1048_, 0, v___x_1047_);
                crate::leanh::lean_ctor_set(v___x_1048_, 1, v_res_1045_);
                return v___x_1048_;
            }
            5 => {
                v_str_1058_ = crate::leanh::lean_ctor_get(v_needle_1051_, 0);
                v_startInclusive_1059_ = crate::leanh::lean_ctor_get(v_needle_1051_, 1);
                v_endExclusive_1060_ = crate::leanh::lean_ctor_get(v_needle_1051_, 2);
                v_str_1061_ = crate::leanh::lean_ctor_get(v_s_1018_, 0);
                v_startInclusive_1062_ = crate::leanh::lean_ctor_get(v_s_1018_, 1);
                v_endExclusive_1063_ = crate::leanh::lean_ctor_get(v_s_1018_, 2);
                v_basePos_1064_ = lean_nat_sub(v_stackPos_1053_, v_needlePos_1054_);
                v___x_1065_ = lean_nat_sub(v_endExclusive_1060_, v_startInclusive_1059_);
                v___x_1066_ = lean_nat_add(v_basePos_1064_, v___x_1065_);
                v___x_1067_ = lean_nat_sub(v_endExclusive_1063_, v_startInclusive_1062_);
                v___x_1068_ = lean_nat_dec_le(v___x_1066_, v___x_1067_);
                crate::leanh::lean_dec(v___x_1066_);
                if v___x_1068_ == 0 {
                    crate::leanh::lean_dec(v___x_1065_);
                    crate::leanh::lean_del_object(v___x_1056_);
                    crate::leanh::lean_dec(v_needlePos_1054_);
                    crate::leanh::lean_dec(v_stackPos_1053_);
                    crate::leanh::lean_dec_ref(v_table_1052_);
                    crate::leanh::lean_dec_ref(v_needle_1051_);
                    v___x_1069_ = lean_nat_dec_lt(v_basePos_1064_, v___x_1067_);
                    if v___x_1069_ == 0 {
                        crate::leanh::lean_dec(v___x_1067_);
                        crate::leanh::lean_dec(v_basePos_1064_);
                        v___x_1070_ = crate::leanh::lean_box(2);
                        return v___x_1070_;
                    } else {
                        v___x_1071_ = l_String_Slice_pos_x21(v_s_1018_, v_basePos_1064_);
                        crate::leanh::lean_dec(v_basePos_1064_);
                        v_res_1072_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_res_1072_, 0, v___x_1071_);
                        crate::leanh::lean_ctor_set(v_res_1072_, 1, v___x_1067_);
                        v___x_1073_ = crate::leanh::lean_box(3);
                        v___x_1074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1073_);
                        crate::leanh::lean_ctor_set(v___x_1074_, 1, v_res_1072_);
                        return v___x_1074_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1067_);
                    v___x_1075_ = lean_nat_add(v_startInclusive_1062_, v_stackPos_1053_);
                    v_stackByte_1076_ = lean_string_get_byte_fast(v_str_1061_, v___x_1075_);
                    v___x_1077_ = lean_nat_add(v_startInclusive_1059_, v_needlePos_1054_);
                    v_patByte_1078_ = lean_string_get_byte_fast(v_str_1058_, v___x_1077_);
                    v___x_1079_ = lean_uint8_dec_eq(v_stackByte_1076_, v_patByte_1078_);
                    if v___x_1079_ == 0 {
                        crate::leanh::lean_dec(v___x_1065_);
                        v___x_1080_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1081_ = lean_nat_dec_eq(v_needlePos_1054_, v___x_1080_);
                        if v___x_1081_ == 0 {
                            v___x_1082_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1083_ = lean_nat_sub(v_needlePos_1054_, v___x_1082_);
                            crate::leanh::lean_dec(v_needlePos_1054_);
                            v_newNeedlePos_1084_ =
                                lean_array_fget_borrowed(v_table_1052_, v___x_1083_);
                            crate::leanh::lean_dec(v___x_1083_);
                            v___x_1085_ = lean_nat_dec_eq(v_newNeedlePos_1084_, v___x_1080_);
                            if v___x_1085_ == 0 {
                                crate::leanh::lean_inc(v_newNeedlePos_1084_);
                                v_oldBasePos_1086_ =
                                    l_String_Slice_pos_x21(v_s_1018_, v_basePos_1064_);
                                crate::leanh::lean_dec(v_basePos_1064_);
                                v___x_1087_ = lean_nat_sub(v_stackPos_1053_, v_newNeedlePos_1084_);
                                v_newBasePos_1088_ = l_String_Slice_pos_x21(v_s_1018_, v___x_1087_);
                                crate::leanh::lean_dec(v___x_1087_);
                                v_res_1089_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_res_1089_, 0, v_oldBasePos_1086_);
                                crate::leanh::lean_ctor_set(v_res_1089_, 1, v_newBasePos_1088_);
                                if v_isShared_1057_ == 0 {
                                    crate::leanh::lean_ctor_set(
                                        v___x_1056_,
                                        3,
                                        v_newNeedlePos_1084_,
                                    );
                                    v___x_1091_ = v___x_1056_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1093_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        0,
                                        v_needle_1051_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        1,
                                        v_table_1052_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1093_,
                                        2,
                                        v_stackPos_1053_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                crate::leanh::lean_dec(v_basePos_1064_);
                                v_nextStackPos_1095_ =
                                    l_String_Slice_posGE___redArg(v_s_1018_, v_stackPos_1053_);
                                crate::leanh::lean_inc(v_nextStackPos_1095_);
                                v_res_1096_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_res_1096_, 0, v_basePos_1094_);
                                crate::leanh::lean_ctor_set(v_res_1096_, 1, v_nextStackPos_1095_);
                                if v_isShared_1057_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1056_, 3, v___x_1080_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_1056_,
                                        2,
                                        v_nextStackPos_1095_,
                                    );
                                    v___x_1098_ = v___x_1056_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1100_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        0,
                                        v_needle_1051_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        1,
                                        v_table_1052_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1100_,
                                        2,
                                        v_nextStackPos_1095_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_dec(v_basePos_1064_);
                            crate::leanh::lean_dec(v_needlePos_1054_);
                            v_basePos_1101_ = l_String_Slice_pos_x21(v_s_1018_, v_stackPos_1053_);
                            v___x_1102_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1103_ = lean_nat_add(v_stackPos_1053_, v___x_1102_);
                            crate::leanh::lean_dec(v_stackPos_1053_);
                            v_nextStackPos_1104_ =
                                l_String_Slice_posGE___redArg(v_s_1018_, v___x_1103_);
                            crate::leanh::lean_inc(v_nextStackPos_1104_);
                            v_res_1105_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_res_1105_, 0, v_basePos_1101_);
                            crate::leanh::lean_ctor_set(v_res_1105_, 1, v_nextStackPos_1104_);
                            if v_isShared_1057_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1056_, 3, v___x_1080_);
                                crate::leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1104_);
                                v___x_1107_ = v___x_1056_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1109_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    0,
                                    v_needle_1051_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    1,
                                    v_table_1052_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1109_,
                                    2,
                                    v_nextStackPos_1104_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1109_, 3, v___x_1080_);
                                v___x_1107_ = v_reuseFailAlloc_1109_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_basePos_1064_);
                        v___x_1110_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1111_ = lean_nat_add(v_stackPos_1053_, v___x_1110_);
                        crate::leanh::lean_dec(v_stackPos_1053_);
                        v_nextNeedlePos_1112_ = lean_nat_add(v_needlePos_1054_, v___x_1110_);
                        crate::leanh::lean_dec(v_needlePos_1054_);
                        v___x_1113_ = lean_nat_dec_eq(v_nextNeedlePos_1112_, v___x_1065_);
                        crate::leanh::lean_dec(v___x_1065_);
                        if v___x_1113_ == 0 {
                            if v_isShared_1057_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1056_, 3, v_nextNeedlePos_1112_);
                                crate::leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1111_);
                                v___x_1115_ = v___x_1056_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1117_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    0,
                                    v_needle_1051_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    1,
                                    v_table_1052_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1117_,
                                    2,
                                    v_nextStackPos_1111_,
                                );
                                crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_dec(v_nextNeedlePos_1112_);
                            v___x_1119_ = l_String_Slice_pos_x21(v_s_1018_, v___x_1118_);
                            crate::leanh::lean_dec(v___x_1118_);
                            v___x_1120_ = l_String_Slice_pos_x21(v_s_1018_, v_nextStackPos_1111_);
                            v_res_1121_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_res_1121_, 0, v___x_1119_);
                            crate::leanh::lean_ctor_set(v_res_1121_, 1, v___x_1120_);
                            v___x_1122_ = crate::leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1057_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1056_, 3, v___x_1122_);
                                crate::leanh::lean_ctor_set(v___x_1056_, 2, v_nextStackPos_1111_);
                                v___x_1124_ = v___x_1056_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1126_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    0,
                                    v_needle_1051_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    1,
                                    v_table_1052_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1126_,
                                    2,
                                    v_nextStackPos_1111_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1126_, 3, v___x_1122_);
                                v___x_1124_ = v_reuseFailAlloc_1126_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_1092_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1092_, 0, v___x_1091_);
                crate::leanh::lean_ctor_set(v___x_1092_, 1, v_res_1089_);
                return v___x_1092_;
            }
            7 => {
                v___x_1099_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1099_, 0, v___x_1098_);
                crate::leanh::lean_ctor_set(v___x_1099_, 1, v_res_1096_);
                return v___x_1099_;
            }
            8 => {
                v___x_1108_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1108_, 0, v___x_1107_);
                crate::leanh::lean_ctor_set(v___x_1108_, 1, v_res_1105_);
                return v___x_1108_;
            }
            9 => {
                v___x_1116_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1116_, 0, v___x_1115_);
                return v___x_1116_;
            }
            10 => {
                v___x_1125_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1125_, 0, v___x_1124_);
                crate::leanh::lean_ctor_set(v___x_1125_, 1, v_res_1121_);
                return v___x_1125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed(
    mut v_s_1129_: *mut crate::leanh::LeanObject,
    mut v_x_1130_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1131_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0(
        v_s_1129_, v_x_1130_,
    );
    crate::leanh::lean_dec_ref(v_s_1129_);
    return v_res_1131_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep(
    mut v_s_1132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1133_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep___lam__0___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1133_, 0, v_s_1132_);
    return v___f_1133_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(
    mut v_s_1134_: *mut crate::leanh::LeanObject,
    mut v_x_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pos_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1139_: u8 = 0;
    let mut v___x_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1146_: u8 = 0;
    let mut v_pos_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v_stackPos_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_x_1135_) {
                0 => {
                    v_pos_1136_ = crate::leanh::lean_ctor_get(v_x_1135_, 0);
                    v_isSharedCheck_1146_ = (!crate::leanh::lean_is_exclusive(v_x_1135_)) as u8;
                    if v_isSharedCheck_1146_ == 0 {
                        v___x_1138_ = v_x_1135_;
                        v_isShared_1139_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1136_);
                        crate::leanh::lean_dec(v_x_1135_);
                        v___x_1138_ = crate::leanh::lean_box(0);
                        v_isShared_1139_ = v_isSharedCheck_1146_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v_pos_1147_ = crate::leanh::lean_ctor_get(v_x_1135_, 0);
                    v_isSharedCheck_1157_ = (!crate::leanh::lean_is_exclusive(v_x_1135_)) as u8;
                    if v_isSharedCheck_1157_ == 0 {
                        v___x_1149_ = v_x_1135_;
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_pos_1147_);
                        crate::leanh::lean_dec(v_x_1135_);
                        v___x_1149_ = crate::leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 3;
                        continue;
                    }
                }
                2 => {
                    v_stackPos_1158_ = crate::leanh::lean_ctor_get(v_x_1135_, 2);
                    crate::leanh::lean_inc(v_stackPos_1158_);
                    v_needlePos_1159_ = crate::leanh::lean_ctor_get(v_x_1135_, 3);
                    crate::leanh::lean_inc(v_needlePos_1159_);
                    crate::leanh::lean_dec_ref_known(v_x_1135_, 4);
                    v_startInclusive_1160_ = crate::leanh::lean_ctor_get(v_s_1134_, 1);
                    v_endExclusive_1161_ = crate::leanh::lean_ctor_get(v_s_1134_, 2);
                    v___x_1162_ = lean_nat_sub(v_endExclusive_1161_, v_startInclusive_1160_);
                    v___x_1163_ = lean_nat_sub(v___x_1162_, v_stackPos_1158_);
                    crate::leanh::lean_dec(v_stackPos_1158_);
                    crate::leanh::lean_dec(v___x_1162_);
                    v___x_1164_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1164_, 0, v___x_1163_);
                    crate::leanh::lean_ctor_set(v___x_1164_, 1, v_needlePos_1159_);
                    v___x_1165_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1165_, 0, v___x_1164_);
                    return v___x_1165_;
                }
                _ => {
                    v___x_1166_ = crate::leanh::lean_box(0);
                    return v___x_1166_;
                }
            },
            1 => {
                v___x_1140_ = l_String_Slice_Pos_remainingBytes(v_s_1134_, v_pos_1136_);
                crate::leanh::lean_dec(v_pos_1136_);
                v___x_1141_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_1142_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1142_, 0, v___x_1140_);
                crate::leanh::lean_ctor_set(v___x_1142_, 1, v___x_1141_);
                if v_isShared_1139_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1138_, 1);
                    crate::leanh::lean_ctor_set(v___x_1138_, 0, v___x_1142_);
                    v___x_1144_ = v___x_1138_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1145_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
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
                crate::leanh::lean_dec(v_pos_1147_);
                v___x_1152_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1153_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1153_, 0, v___x_1151_);
                crate::leanh::lean_ctor_set(v___x_1153_, 1, v___x_1152_);
                if v_isShared_1150_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1149_, 0, v___x_1153_);
                    v___x_1155_ = v___x_1149_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1153_);
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
    mut v_s_1167_: *mut crate::leanh::LeanObject,
    mut v_x_1168_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1169_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_toOption(v_s_1167_, v_x_1168_);
    crate::leanh::lean_dec_ref(v_s_1167_);
    return v_res_1169_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(
    mut v_s_1170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1171_ = crate::leanh::lean_box(0);
    return v___x_1171_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation___boxed(
    mut v_s_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instWellFoundedRelation(v_s_1172_);
    crate::leanh::lean_dec_ref(v_s_1172_);
    return v_res_1173_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___redArg(
    mut v_x_1174_: *mut crate::leanh::LeanObject,
    mut v_h__1_1175_: *mut crate::leanh::LeanObject,
    mut v_h__2_1176_: *mut crate::leanh::LeanObject,
    mut v_h__3_1177_: *mut crate::leanh::LeanObject,
    mut v_h__4_1178_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1174_) {
        0 => {
            let mut v_pos_1179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1178_);
            crate::leanh::lean_dec(v_h__3_1177_);
            crate::leanh::lean_dec(v_h__2_1176_);
            v_pos_1179_ = crate::leanh::lean_ctor_get(v_x_1174_, 0);
            crate::leanh::lean_inc(v_pos_1179_);
            crate::leanh::lean_dec_ref_known(v_x_1174_, 1);
            v___x_1180_ = crate::leanh::lean_apply_1(v_h__1_1175_, v_pos_1179_);
            return v___x_1180_;
        }
        1 => {
            let mut v_pos_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1178_);
            crate::leanh::lean_dec(v_h__3_1177_);
            crate::leanh::lean_dec(v_h__1_1175_);
            v_pos_1181_ = crate::leanh::lean_ctor_get(v_x_1174_, 0);
            crate::leanh::lean_inc(v_pos_1181_);
            crate::leanh::lean_dec_ref_known(v_x_1174_, 1);
            v___x_1182_ =
                crate::leanh::lean_apply_2(v_h__2_1176_, v_pos_1181_, crate::leanh::lean_box(0));
            return v___x_1182_;
        }
        2 => {
            let mut v_needle_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1178_);
            crate::leanh::lean_dec(v_h__2_1176_);
            crate::leanh::lean_dec(v_h__1_1175_);
            v_needle_1183_ = crate::leanh::lean_ctor_get(v_x_1174_, 0);
            crate::leanh::lean_inc_ref(v_needle_1183_);
            v_table_1184_ = crate::leanh::lean_ctor_get(v_x_1174_, 1);
            crate::leanh::lean_inc_ref(v_table_1184_);
            v_stackPos_1185_ = crate::leanh::lean_ctor_get(v_x_1174_, 2);
            crate::leanh::lean_inc(v_stackPos_1185_);
            v_needlePos_1186_ = crate::leanh::lean_ctor_get(v_x_1174_, 3);
            crate::leanh::lean_inc(v_needlePos_1186_);
            crate::leanh::lean_dec_ref_known(v_x_1174_, 4);
            v___x_1187_ = crate::leanh::lean_apply_6(
                v_h__3_1177_,
                v_needle_1183_,
                v_table_1184_,
                crate::leanh::lean_box(0),
                v_stackPos_1185_,
                v_needlePos_1186_,
                crate::leanh::lean_box(0),
            );
            return v___x_1187_;
        }
        _ => {
            let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1177_);
            crate::leanh::lean_dec(v_h__2_1176_);
            crate::leanh::lean_dec(v_h__1_1175_);
            v___x_1188_ = crate::leanh::lean_box(0);
            v___x_1189_ = crate::leanh::lean_apply_1(v_h__4_1178_, v___x_1188_);
            return v___x_1189_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(
    mut v_s_1190_: *mut crate::leanh::LeanObject,
    mut v_motive_1191_: *mut crate::leanh::LeanObject,
    mut v_x_1192_: *mut crate::leanh::LeanObject,
    mut v_h__1_1193_: *mut crate::leanh::LeanObject,
    mut v_h__2_1194_: *mut crate::leanh::LeanObject,
    mut v_h__3_1195_: *mut crate::leanh::LeanObject,
    mut v_h__4_1196_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1192_) {
        0 => {
            let mut v_pos_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1196_);
            crate::leanh::lean_dec(v_h__3_1195_);
            crate::leanh::lean_dec(v_h__2_1194_);
            v_pos_1197_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
            crate::leanh::lean_inc(v_pos_1197_);
            crate::leanh::lean_dec_ref_known(v_x_1192_, 1);
            v___x_1198_ = crate::leanh::lean_apply_1(v_h__1_1193_, v_pos_1197_);
            return v___x_1198_;
        }
        1 => {
            let mut v_pos_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1196_);
            crate::leanh::lean_dec(v_h__3_1195_);
            crate::leanh::lean_dec(v_h__1_1193_);
            v_pos_1199_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
            crate::leanh::lean_inc(v_pos_1199_);
            crate::leanh::lean_dec_ref_known(v_x_1192_, 1);
            v___x_1200_ =
                crate::leanh::lean_apply_2(v_h__2_1194_, v_pos_1199_, crate::leanh::lean_box(0));
            return v___x_1200_;
        }
        2 => {
            let mut v_needle_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_table_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_stackPos_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_needlePos_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__4_1196_);
            crate::leanh::lean_dec(v_h__2_1194_);
            crate::leanh::lean_dec(v_h__1_1193_);
            v_needle_1201_ = crate::leanh::lean_ctor_get(v_x_1192_, 0);
            crate::leanh::lean_inc_ref(v_needle_1201_);
            v_table_1202_ = crate::leanh::lean_ctor_get(v_x_1192_, 1);
            crate::leanh::lean_inc_ref(v_table_1202_);
            v_stackPos_1203_ = crate::leanh::lean_ctor_get(v_x_1192_, 2);
            crate::leanh::lean_inc(v_stackPos_1203_);
            v_needlePos_1204_ = crate::leanh::lean_ctor_get(v_x_1192_, 3);
            crate::leanh::lean_inc(v_needlePos_1204_);
            crate::leanh::lean_dec_ref_known(v_x_1192_, 4);
            v___x_1205_ = crate::leanh::lean_apply_6(
                v_h__3_1195_,
                v_needle_1201_,
                v_table_1202_,
                crate::leanh::lean_box(0),
                v_stackPos_1203_,
                v_needlePos_1204_,
                crate::leanh::lean_box(0),
            );
            return v___x_1205_;
        }
        _ => {
            let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1195_);
            crate::leanh::lean_dec(v_h__2_1194_);
            crate::leanh::lean_dec(v_h__1_1193_);
            v___x_1206_ = crate::leanh::lean_box(0);
            v___x_1207_ = crate::leanh::lean_apply_1(v_h__4_1196_, v___x_1206_);
            return v___x_1207_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter___boxed(
    mut v_s_1208_: *mut crate::leanh::LeanObject,
    mut v_motive_1209_: *mut crate::leanh::LeanObject,
    mut v_x_1210_: *mut crate::leanh::LeanObject,
    mut v_h__1_1211_: *mut crate::leanh::LeanObject,
    mut v_h__2_1212_: *mut crate::leanh::LeanObject,
    mut v_h__3_1213_: *mut crate::leanh::LeanObject,
    mut v_h__4_1214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1215_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__1_splitter(v_s_1208_, v_motive_1209_, v_x_1210_, v_h__1_1211_, v_h__2_1212_, v_h__3_1213_, v_h__4_1214_);
    crate::leanh::lean_dec_ref(v_s_1208_);
    return v_res_1215_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___redArg(
    mut v_x_1216_: *mut crate::leanh::LeanObject,
    mut v_h__1_1217_: *mut crate::leanh::LeanObject,
    mut v_h__2_1218_: *mut crate::leanh::LeanObject,
    mut v_h__3_1219_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1216_) {
        0 => {
            let mut v_it_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1219_);
            crate::leanh::lean_dec(v_h__2_1218_);
            v_it_1220_ = crate::leanh::lean_ctor_get(v_x_1216_, 0);
            crate::leanh::lean_inc(v_it_1220_);
            v_out_1221_ = crate::leanh::lean_ctor_get(v_x_1216_, 1);
            crate::leanh::lean_inc(v_out_1221_);
            crate::leanh::lean_dec_ref_known(v_x_1216_, 2);
            v___x_1222_ = crate::leanh::lean_apply_2(v_h__1_1217_, v_it_1220_, v_out_1221_);
            return v___x_1222_;
        }
        1 => {
            let mut v_it_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1219_);
            crate::leanh::lean_dec(v_h__1_1217_);
            v_it_1223_ = crate::leanh::lean_ctor_get(v_x_1216_, 0);
            crate::leanh::lean_inc(v_it_1223_);
            crate::leanh::lean_dec_ref_known(v_x_1216_, 1);
            v___x_1224_ = crate::leanh::lean_apply_1(v_h__2_1218_, v_it_1223_);
            return v___x_1224_;
        }
        _ => {
            let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1218_);
            crate::leanh::lean_dec(v_h__1_1217_);
            v___x_1225_ = crate::leanh::lean_box(0);
            v___x_1226_ = crate::leanh::lean_apply_1(v_h__3_1219_, v___x_1225_);
            return v___x_1226_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(
    mut v_s_1227_: *mut crate::leanh::LeanObject,
    mut v_motive_1228_: *mut crate::leanh::LeanObject,
    mut v_x_1229_: *mut crate::leanh::LeanObject,
    mut v_h__1_1230_: *mut crate::leanh::LeanObject,
    mut v_h__2_1231_: *mut crate::leanh::LeanObject,
    mut v_h__3_1232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_x_1229_) {
        0 => {
            let mut v_it_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1232_);
            crate::leanh::lean_dec(v_h__2_1231_);
            v_it_1233_ = crate::leanh::lean_ctor_get(v_x_1229_, 0);
            crate::leanh::lean_inc(v_it_1233_);
            v_out_1234_ = crate::leanh::lean_ctor_get(v_x_1229_, 1);
            crate::leanh::lean_inc(v_out_1234_);
            crate::leanh::lean_dec_ref_known(v_x_1229_, 2);
            v___x_1235_ = crate::leanh::lean_apply_2(v_h__1_1230_, v_it_1233_, v_out_1234_);
            return v___x_1235_;
        }
        1 => {
            let mut v_it_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__3_1232_);
            crate::leanh::lean_dec(v_h__1_1230_);
            v_it_1236_ = crate::leanh::lean_ctor_get(v_x_1229_, 0);
            crate::leanh::lean_inc(v_it_1236_);
            crate::leanh::lean_dec_ref_known(v_x_1229_, 1);
            v___x_1237_ = crate::leanh::lean_apply_1(v_h__2_1231_, v_it_1236_);
            return v___x_1237_;
        }
        _ => {
            let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_h__2_1231_);
            crate::leanh::lean_dec(v_h__1_1230_);
            v___x_1238_ = crate::leanh::lean_box(0);
            v___x_1239_ = crate::leanh::lean_apply_1(v_h__3_1232_, v___x_1238_);
            return v___x_1239_;
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter___boxed(
    mut v_s_1240_: *mut crate::leanh::LeanObject,
    mut v_motive_1241_: *mut crate::leanh::LeanObject,
    mut v_x_1242_: *mut crate::leanh::LeanObject,
    mut v_h__1_1243_: *mut crate::leanh::LeanObject,
    mut v_h__2_1244_: *mut crate::leanh::LeanObject,
    mut v_h__3_1245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1246_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_instIteratorIdSearchStep_match__3_splitter(v_s_1240_, v_motive_1241_, v_x_1242_, v_h__1_1243_, v_h__2_1244_, v_h__3_1245_);
    crate::leanh::lean_dec_ref(v_s_1240_);
    return v_res_1246_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(
    mut v_s_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = crate::leanh::lean_box(0);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation___boxed(
    mut v_s_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1250_ = l___private_Init_Data_String_Pattern_String_0__String_Slice_Pattern_ForwardSliceSearcher_finitenessRelation(v_s_1249_);
    crate::leanh::lean_dec_ref(v_s_1249_);
    return v_res_1250_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0(
    mut v___y_1251_: *mut crate::leanh::LeanObject,
    mut v_acc_1252_: *mut crate::leanh::LeanObject,
    mut v_recur_1253_: *mut crate::leanh::LeanObject,
    mut v_s_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1254_) {
        0 => {
            let mut v_it_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1255_ = crate::leanh::lean_ctor_get(v_s_1254_, 0);
            crate::leanh::lean_inc(v_it_1255_);
            v_out_1256_ = crate::leanh::lean_ctor_get(v_s_1254_, 1);
            crate::leanh::lean_inc(v_out_1256_);
            crate::leanh::lean_dec_ref_known(v_s_1254_, 2);
            v_val_1257_ = crate::leanh::lean_apply_3(
                v___y_1251_,
                v_out_1256_,
                crate::leanh::lean_box(0),
                v_acc_1252_,
            );
            if crate::leanh::lean_obj_tag(v_val_1257_) == 0 {
                let mut v_a_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_it_1255_);
                crate::leanh::lean_dec(v_recur_1253_);
                v_a_1258_ = crate::leanh::lean_ctor_get(v_val_1257_, 0);
                crate::leanh::lean_inc(v_a_1258_);
                crate::leanh::lean_dec_ref_known(v_val_1257_, 1);
                return v_a_1258_;
            } else {
                let mut v_a_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1259_ = crate::leanh::lean_ctor_get(v_val_1257_, 0);
                crate::leanh::lean_inc(v_a_1259_);
                crate::leanh::lean_dec_ref_known(v_val_1257_, 1);
                v___x_1260_ = crate::leanh::lean_apply_4(
                    v_recur_1253_,
                    v_it_1255_,
                    v_a_1259_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1260_;
            }
        }
        1 => {
            let mut v_it_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___y_1251_);
            v_it_1261_ = crate::leanh::lean_ctor_get(v_s_1254_, 0);
            crate::leanh::lean_inc(v_it_1261_);
            crate::leanh::lean_dec_ref_known(v_s_1254_, 1);
            v___x_1262_ = crate::leanh::lean_apply_4(
                v_recur_1253_,
                v_it_1261_,
                v_acc_1252_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1262_;
        }
        _ => {
            crate::leanh::lean_dec(v_recur_1253_);
            crate::leanh::lean_dec_ref(v___y_1251_);
            return v_acc_1252_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(
    mut v___y_1263_: *mut crate::leanh::LeanObject,
    mut v_s_1264_: *mut crate::leanh::LeanObject,
    mut v_lift_1265_: *mut crate::leanh::LeanObject,
    mut v_it_1266_: *mut crate::leanh::LeanObject,
    mut v_acc_1267_: *mut crate::leanh::LeanObject,
    mut v_hP_1268_: *mut crate::leanh::LeanObject,
    mut v_recur_1269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_pos_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1274_: u8 = 0;
    let mut v_res_1275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1279_: u8 = 0;
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1288_: u8 = 0;
    let mut v_pos_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1292_: u8 = 0;
    let mut v_str_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1304_: u8 = 0;
    let mut v_needle_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_table_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackPos_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_needlePos_1308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1311_: u8 = 0;
    let mut v_str_1312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1322_: u8 = 0;
    let mut v___x_1323_: u8 = 0;
    let mut v___x_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stackByte_1332_: u8 = 0;
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_patByte_1334_: u8 = 0;
    let mut v___x_1335_: u8 = 0;
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1337_: u8 = 0;
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNeedlePos_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1341_: u8 = 0;
    let mut v_oldBasePos_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newBasePos_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_basePos_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextStackPos_1370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextNeedlePos_1371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1372_: u8 = 0;
    let mut v___x_1374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_res_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1388_: u8 = 0;
    let mut v___x_1389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1270_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__0 as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_1270_, 0, v___y_1263_);
                crate::leanh::lean_closure_set(v___f_1270_, 1, v_acc_1267_);
                crate::leanh::lean_closure_set(v___f_1270_, 2, v_recur_1269_);
                match crate::leanh::lean_obj_tag(v_it_1266_) {
                    0 => {
                        v_pos_1271_ = crate::leanh::lean_ctor_get(v_it_1266_, 0);
                        v_isSharedCheck_1288_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1288_ == 0 {
                            v___x_1273_ = v_it_1266_;
                            v_isShared_1274_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_1271_);
                            crate::leanh::lean_dec(v_it_1266_);
                            v___x_1273_ = crate::leanh::lean_box(0);
                            v_isShared_1274_ = v_isSharedCheck_1288_;
                            state = 1;
                            continue;
                        }
                    }
                    1 => {
                        v_pos_1289_ = crate::leanh::lean_ctor_get(v_it_1266_, 0);
                        v_isSharedCheck_1304_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1304_ == 0 {
                            v___x_1291_ = v_it_1266_;
                            v_isShared_1292_ = v_isSharedCheck_1304_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_pos_1289_);
                            crate::leanh::lean_dec(v_it_1266_);
                            v___x_1291_ = crate::leanh::lean_box(0);
                            v_isShared_1292_ = v_isSharedCheck_1304_;
                            state = 3;
                            continue;
                        }
                    }
                    2 => {
                        v_needle_1305_ = crate::leanh::lean_ctor_get(v_it_1266_, 0);
                        v_table_1306_ = crate::leanh::lean_ctor_get(v_it_1266_, 1);
                        v_stackPos_1307_ = crate::leanh::lean_ctor_get(v_it_1266_, 2);
                        v_needlePos_1308_ = crate::leanh::lean_ctor_get(v_it_1266_, 3);
                        v_isSharedCheck_1388_ =
                            (!crate::leanh::lean_is_exclusive(v_it_1266_)) as u8;
                        if v_isSharedCheck_1388_ == 0 {
                            v___x_1310_ = v_it_1266_;
                            v_isShared_1311_ = v_isSharedCheck_1388_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_needlePos_1308_);
                            crate::leanh::lean_inc(v_stackPos_1307_);
                            crate::leanh::lean_inc(v_table_1306_);
                            crate::leanh::lean_inc(v_needle_1305_);
                            crate::leanh::lean_dec(v_it_1266_);
                            v___x_1310_ = crate::leanh::lean_box(0);
                            v_isShared_1311_ = v_isSharedCheck_1388_;
                            state = 5;
                            continue;
                        }
                    }
                    _ => {
                        v___x_1389_ = crate::leanh::lean_box(2);
                        v___x_1390_ = crate::leanh::lean_apply_4(
                            v_lift_1265_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1389_,
                        );
                        return v___x_1390_;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_n(v_pos_1271_, 2);
                v_res_1275_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_res_1275_, 0, v_pos_1271_);
                crate::leanh::lean_ctor_set(v_res_1275_, 1, v_pos_1271_);
                v_startInclusive_1276_ = crate::leanh::lean_ctor_get(v_s_1264_, 1);
                v_endExclusive_1277_ = crate::leanh::lean_ctor_get(v_s_1264_, 2);
                v___x_1278_ = lean_nat_sub(v_endExclusive_1277_, v_startInclusive_1276_);
                v___x_1279_ = lean_nat_dec_eq(v_pos_1271_, v___x_1278_);
                crate::leanh::lean_dec(v___x_1278_);
                if v___x_1279_ == 0 {
                    if v_isShared_1274_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_1273_, 1);
                        v___x_1281_ = v___x_1273_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1284_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1284_, 0, v_pos_1271_);
                        v___x_1281_ = v_reuseFailAlloc_1284_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1273_);
                    crate::leanh::lean_dec(v_pos_1271_);
                    v___x_1285_ = crate::leanh::lean_box(3);
                    v___x_1286_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1286_, 0, v___x_1285_);
                    crate::leanh::lean_ctor_set(v___x_1286_, 1, v_res_1275_);
                    v___x_1287_ = crate::leanh::lean_apply_4(
                        v_lift_1265_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1270_,
                        v___x_1286_,
                    );
                    return v___x_1287_;
                }
            }
            2 => {
                v___x_1282_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1282_, 0, v___x_1281_);
                crate::leanh::lean_ctor_set(v___x_1282_, 1, v_res_1275_);
                v___x_1283_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1282_,
                );
                return v___x_1283_;
            }
            3 => {
                v_str_1293_ = crate::leanh::lean_ctor_get(v_s_1264_, 0);
                v_startInclusive_1294_ = crate::leanh::lean_ctor_get(v_s_1264_, 1);
                v___x_1295_ = lean_nat_add(v_startInclusive_1294_, v_pos_1289_);
                v___x_1296_ = lean_string_utf8_next_fast(v_str_1293_, v___x_1295_);
                crate::leanh::lean_dec(v___x_1295_);
                v___x_1297_ = lean_nat_sub(v___x_1296_, v_startInclusive_1294_);
                crate::leanh::lean_inc(v___x_1297_);
                v_res_1298_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v_res_1298_, 0, v_pos_1289_);
                crate::leanh::lean_ctor_set(v_res_1298_, 1, v___x_1297_);
                if v_isShared_1292_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_1291_, 0);
                    crate::leanh::lean_ctor_set(v___x_1291_, 0, v___x_1297_);
                    v___x_1300_ = v___x_1291_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1303_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1297_);
                    v___x_1300_ = v_reuseFailAlloc_1303_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_1301_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1301_, 0, v___x_1300_);
                crate::leanh::lean_ctor_set(v___x_1301_, 1, v_res_1298_);
                v___x_1302_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1301_,
                );
                return v___x_1302_;
            }
            5 => {
                v_str_1312_ = crate::leanh::lean_ctor_get(v_needle_1305_, 0);
                v_startInclusive_1313_ = crate::leanh::lean_ctor_get(v_needle_1305_, 1);
                v_endExclusive_1314_ = crate::leanh::lean_ctor_get(v_needle_1305_, 2);
                v_str_1315_ = crate::leanh::lean_ctor_get(v_s_1264_, 0);
                v_startInclusive_1316_ = crate::leanh::lean_ctor_get(v_s_1264_, 1);
                v_endExclusive_1317_ = crate::leanh::lean_ctor_get(v_s_1264_, 2);
                v_basePos_1318_ = lean_nat_sub(v_stackPos_1307_, v_needlePos_1308_);
                v___x_1319_ = lean_nat_sub(v_endExclusive_1314_, v_startInclusive_1313_);
                v___x_1320_ = lean_nat_add(v_basePos_1318_, v___x_1319_);
                v___x_1321_ = lean_nat_sub(v_endExclusive_1317_, v_startInclusive_1316_);
                v___x_1322_ = lean_nat_dec_le(v___x_1320_, v___x_1321_);
                crate::leanh::lean_dec(v___x_1320_);
                if v___x_1322_ == 0 {
                    crate::leanh::lean_dec(v___x_1319_);
                    crate::leanh::lean_del_object(v___x_1310_);
                    crate::leanh::lean_dec(v_needlePos_1308_);
                    crate::leanh::lean_dec(v_stackPos_1307_);
                    crate::leanh::lean_dec_ref(v_table_1306_);
                    crate::leanh::lean_dec_ref(v_needle_1305_);
                    v___x_1323_ = lean_nat_dec_lt(v_basePos_1318_, v___x_1321_);
                    if v___x_1323_ == 0 {
                        crate::leanh::lean_dec(v___x_1321_);
                        crate::leanh::lean_dec(v_basePos_1318_);
                        v___x_1324_ = crate::leanh::lean_box(2);
                        v___x_1325_ = crate::leanh::lean_apply_4(
                            v_lift_1265_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1324_,
                        );
                        return v___x_1325_;
                    } else {
                        v___x_1326_ = l_String_Slice_pos_x21(v_s_1264_, v_basePos_1318_);
                        crate::leanh::lean_dec(v_basePos_1318_);
                        v_res_1327_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_res_1327_, 0, v___x_1326_);
                        crate::leanh::lean_ctor_set(v_res_1327_, 1, v___x_1321_);
                        v___x_1328_ = crate::leanh::lean_box(3);
                        v___x_1329_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1329_, 0, v___x_1328_);
                        crate::leanh::lean_ctor_set(v___x_1329_, 1, v_res_1327_);
                        v___x_1330_ = crate::leanh::lean_apply_4(
                            v_lift_1265_,
                            crate::leanh::lean_box(0),
                            crate::leanh::lean_box(0),
                            v___f_1270_,
                            v___x_1329_,
                        );
                        return v___x_1330_;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1321_);
                    v___x_1331_ = lean_nat_add(v_startInclusive_1316_, v_stackPos_1307_);
                    v_stackByte_1332_ = lean_string_get_byte_fast(v_str_1315_, v___x_1331_);
                    v___x_1333_ = lean_nat_add(v_startInclusive_1313_, v_needlePos_1308_);
                    v_patByte_1334_ = lean_string_get_byte_fast(v_str_1312_, v___x_1333_);
                    v___x_1335_ = lean_uint8_dec_eq(v_stackByte_1332_, v_patByte_1334_);
                    if v___x_1335_ == 0 {
                        crate::leanh::lean_dec(v___x_1319_);
                        v___x_1336_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_1337_ = lean_nat_dec_eq(v_needlePos_1308_, v___x_1336_);
                        if v___x_1337_ == 0 {
                            v___x_1338_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1339_ = lean_nat_sub(v_needlePos_1308_, v___x_1338_);
                            crate::leanh::lean_dec(v_needlePos_1308_);
                            v_newNeedlePos_1340_ =
                                lean_array_fget_borrowed(v_table_1306_, v___x_1339_);
                            crate::leanh::lean_dec(v___x_1339_);
                            v___x_1341_ = lean_nat_dec_eq(v_newNeedlePos_1340_, v___x_1336_);
                            if v___x_1341_ == 0 {
                                crate::leanh::lean_inc(v_newNeedlePos_1340_);
                                v_oldBasePos_1342_ =
                                    l_String_Slice_pos_x21(v_s_1264_, v_basePos_1318_);
                                crate::leanh::lean_dec(v_basePos_1318_);
                                v___x_1343_ = lean_nat_sub(v_stackPos_1307_, v_newNeedlePos_1340_);
                                v_newBasePos_1344_ = l_String_Slice_pos_x21(v_s_1264_, v___x_1343_);
                                crate::leanh::lean_dec(v___x_1343_);
                                v_res_1345_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_res_1345_, 0, v_oldBasePos_1342_);
                                crate::leanh::lean_ctor_set(v_res_1345_, 1, v_newBasePos_1344_);
                                if v_isShared_1311_ == 0 {
                                    crate::leanh::lean_ctor_set(
                                        v___x_1310_,
                                        3,
                                        v_newNeedlePos_1340_,
                                    );
                                    v___x_1347_ = v___x_1310_;
                                    state = 6;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1350_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        0,
                                        v_needle_1305_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        1,
                                        v_table_1306_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1350_,
                                        2,
                                        v_stackPos_1307_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                                crate::leanh::lean_dec(v_basePos_1318_);
                                v_nextStackPos_1352_ =
                                    l_String_Slice_posGE___redArg(v_s_1264_, v_stackPos_1307_);
                                crate::leanh::lean_inc(v_nextStackPos_1352_);
                                v_res_1353_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v_res_1353_, 0, v_basePos_1351_);
                                crate::leanh::lean_ctor_set(v_res_1353_, 1, v_nextStackPos_1352_);
                                if v_isShared_1311_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_1310_, 3, v___x_1336_);
                                    crate::leanh::lean_ctor_set(
                                        v___x_1310_,
                                        2,
                                        v_nextStackPos_1352_,
                                    );
                                    v___x_1355_ = v___x_1310_;
                                    state = 7;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_1358_ =
                                        crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        0,
                                        v_needle_1305_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        1,
                                        v_table_1306_,
                                    );
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_1358_,
                                        2,
                                        v_nextStackPos_1352_,
                                    );
                                    crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_dec(v_basePos_1318_);
                            crate::leanh::lean_dec(v_needlePos_1308_);
                            v_basePos_1359_ = l_String_Slice_pos_x21(v_s_1264_, v_stackPos_1307_);
                            v___x_1360_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_1361_ = lean_nat_add(v_stackPos_1307_, v___x_1360_);
                            crate::leanh::lean_dec(v_stackPos_1307_);
                            v_nextStackPos_1362_ =
                                l_String_Slice_posGE___redArg(v_s_1264_, v___x_1361_);
                            crate::leanh::lean_inc(v_nextStackPos_1362_);
                            v_res_1363_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_res_1363_, 0, v_basePos_1359_);
                            crate::leanh::lean_ctor_set(v_res_1363_, 1, v_nextStackPos_1362_);
                            if v_isShared_1311_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1310_, 3, v___x_1336_);
                                crate::leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1362_);
                                v___x_1365_ = v___x_1310_;
                                state = 8;
                                continue;
                            } else {
                                v_reuseFailAlloc_1368_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    0,
                                    v_needle_1305_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    1,
                                    v_table_1306_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1368_,
                                    2,
                                    v_nextStackPos_1362_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1368_, 3, v___x_1336_);
                                v___x_1365_ = v_reuseFailAlloc_1368_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_basePos_1318_);
                        v___x_1369_ = crate::leanh::lean_unsigned_to_nat(1);
                        v_nextStackPos_1370_ = lean_nat_add(v_stackPos_1307_, v___x_1369_);
                        crate::leanh::lean_dec(v_stackPos_1307_);
                        v_nextNeedlePos_1371_ = lean_nat_add(v_needlePos_1308_, v___x_1369_);
                        crate::leanh::lean_dec(v_needlePos_1308_);
                        v___x_1372_ = lean_nat_dec_eq(v_nextNeedlePos_1371_, v___x_1319_);
                        crate::leanh::lean_dec(v___x_1319_);
                        if v___x_1372_ == 0 {
                            if v_isShared_1311_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1310_, 3, v_nextNeedlePos_1371_);
                                crate::leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1370_);
                                v___x_1374_ = v___x_1310_;
                                state = 9;
                                continue;
                            } else {
                                v_reuseFailAlloc_1377_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    0,
                                    v_needle_1305_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    1,
                                    v_table_1306_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1377_,
                                    2,
                                    v_nextStackPos_1370_,
                                );
                                crate::leanh::lean_ctor_set(
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
                            crate::leanh::lean_dec(v_nextNeedlePos_1371_);
                            v___x_1379_ = l_String_Slice_pos_x21(v_s_1264_, v___x_1378_);
                            crate::leanh::lean_dec(v___x_1378_);
                            v___x_1380_ = l_String_Slice_pos_x21(v_s_1264_, v_nextStackPos_1370_);
                            v_res_1381_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_res_1381_, 0, v___x_1379_);
                            crate::leanh::lean_ctor_set(v_res_1381_, 1, v___x_1380_);
                            v___x_1382_ = crate::leanh::lean_unsigned_to_nat(0);
                            if v_isShared_1311_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_1310_, 3, v___x_1382_);
                                crate::leanh::lean_ctor_set(v___x_1310_, 2, v_nextStackPos_1370_);
                                v___x_1384_ = v___x_1310_;
                                state = 10;
                                continue;
                            } else {
                                v_reuseFailAlloc_1387_ =
                                    crate::leanh::lean_alloc_ctor(2, 4, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    0,
                                    v_needle_1305_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    1,
                                    v_table_1306_,
                                );
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_1387_,
                                    2,
                                    v_nextStackPos_1370_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_1387_, 3, v___x_1382_);
                                v___x_1384_ = v_reuseFailAlloc_1387_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                v___x_1348_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1348_, 0, v___x_1347_);
                crate::leanh::lean_ctor_set(v___x_1348_, 1, v_res_1345_);
                v___x_1349_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1348_,
                );
                return v___x_1349_;
            }
            7 => {
                v___x_1356_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1356_, 0, v___x_1355_);
                crate::leanh::lean_ctor_set(v___x_1356_, 1, v_res_1353_);
                v___x_1357_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1356_,
                );
                return v___x_1357_;
            }
            8 => {
                v___x_1366_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1366_, 0, v___x_1365_);
                crate::leanh::lean_ctor_set(v___x_1366_, 1, v_res_1363_);
                v___x_1367_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1366_,
                );
                return v___x_1367_;
            }
            9 => {
                v___x_1375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1375_, 0, v___x_1374_);
                v___x_1376_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1270_,
                    v___x_1375_,
                );
                return v___x_1376_;
            }
            10 => {
                v___x_1385_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1385_, 0, v___x_1384_);
                crate::leanh::lean_ctor_set(v___x_1385_, 1, v_res_1381_);
                v___x_1386_ = crate::leanh::lean_apply_4(
                    v_lift_1265_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
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
    mut v___y_1391_: *mut crate::leanh::LeanObject,
    mut v_s_1392_: *mut crate::leanh::LeanObject,
    mut v_lift_1393_: *mut crate::leanh::LeanObject,
    mut v_it_1394_: *mut crate::leanh::LeanObject,
    mut v_acc_1395_: *mut crate::leanh::LeanObject,
    mut v_hP_1396_: *mut crate::leanh::LeanObject,
    mut v_recur_1397_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1398_ = l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1(
        v___y_1391_,
        v_s_1392_,
        v_lift_1393_,
        v_it_1394_,
        v_acc_1395_,
        v_hP_1396_,
        v_recur_1397_,
    );
    crate::leanh::lean_dec_ref(v_s_1392_);
    return v_res_1398_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2(
    mut v_s_1399_: *mut crate::leanh::LeanObject,
    mut v_lift_1400_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1401_: *mut crate::leanh::LeanObject,
    mut v_Pl_1402_: *mut crate::leanh::LeanObject,
    mut v_it_1403_: *mut crate::leanh::LeanObject,
    mut v_init_1404_: *mut crate::leanh::LeanObject,
    mut v___y_1405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1406_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__1___boxed
            as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1406_, 0, v___y_1405_);
    crate::leanh::lean_closure_set(v___f_1406_, 1, v_s_1399_);
    crate::leanh::lean_closure_set(v___f_1406_, 2, v_lift_1400_);
    v___x_1407_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1406_,
        v_it_1403_,
        v_init_1404_,
        crate::leanh::lean_box(0),
    );
    return v___x_1407_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep(
    mut v_s_1408_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1409_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instIteratorLoopIdSearchStep___lam__2
            as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1409_, 0, v_s_1408_);
    return v___f_1409_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher(
    mut v_pat_1410_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1411_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1411_, 0, v_pat_1410_);
    return v___x_1411_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(
    mut v_pat_1412_: *mut crate::leanh::LeanObject,
    mut v_s_1413_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_1414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    v_str_1414_ = crate::leanh::lean_ctor_get(v_pat_1412_, 0);
    v_startInclusive_1415_ = crate::leanh::lean_ctor_get(v_pat_1412_, 1);
    v_endExclusive_1416_ = crate::leanh::lean_ctor_get(v_pat_1412_, 2);
    v_str_1417_ = crate::leanh::lean_ctor_get(v_s_1413_, 0);
    v_startInclusive_1418_ = crate::leanh::lean_ctor_get(v_s_1413_, 1);
    v_endExclusive_1419_ = crate::leanh::lean_ctor_get(v_s_1413_, 2);
    v___x_1420_ = lean_nat_sub(v_endExclusive_1416_, v_startInclusive_1415_);
    v___x_1421_ = lean_nat_sub(v_endExclusive_1419_, v_startInclusive_1418_);
    v___x_1422_ = lean_nat_dec_le(v___x_1420_, v___x_1421_);
    crate::leanh::lean_dec(v___x_1421_);
    if v___x_1422_ == 0 {
        crate::leanh::lean_dec(v___x_1420_);
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
        crate::leanh::lean_dec(v___x_1420_);
        return v___x_1423_;
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed(
    mut v_pat_1424_: *mut crate::leanh::LeanObject,
    mut v_s_1425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1426_: u8 = 0;
    let mut v_r_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1426_ = l_String_Slice_Pattern_ForwardSliceSearcher_startsWith(v_pat_1424_, v_s_1425_);
    crate::leanh::lean_dec_ref(v_s_1425_);
    crate::leanh::lean_dec_ref(v_pat_1424_);
    v_r_1427_ = crate::leanh::lean_box((v_res_1426_) as usize);
    return v_r_1427_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(
    mut v_pat_1428_: *mut crate::leanh::LeanObject,
    mut v_s_1429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1438_: u8 = 0;
    v_str_1430_ = crate::leanh::lean_ctor_get(v_pat_1428_, 0);
    v_startInclusive_1431_ = crate::leanh::lean_ctor_get(v_pat_1428_, 1);
    v_endExclusive_1432_ = crate::leanh::lean_ctor_get(v_pat_1428_, 2);
    v_str_1433_ = crate::leanh::lean_ctor_get(v_s_1429_, 0);
    v_startInclusive_1434_ = crate::leanh::lean_ctor_get(v_s_1429_, 1);
    v_endExclusive_1435_ = crate::leanh::lean_ctor_get(v_s_1429_, 2);
    v___x_1436_ = lean_nat_sub(v_endExclusive_1432_, v_startInclusive_1431_);
    v___x_1437_ = lean_nat_sub(v_endExclusive_1435_, v_startInclusive_1434_);
    v___x_1438_ = lean_nat_dec_le(v___x_1436_, v___x_1437_);
    crate::leanh::lean_dec(v___x_1437_);
    if v___x_1438_ == 0 {
        let mut v___x_1439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1436_);
        v___x_1439_ = crate::leanh::lean_box(0);
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
            let mut v___x_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1436_);
            v___x_1441_ = crate::leanh::lean_box(0);
            return v___x_1441_;
        } else {
            let mut v___x_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1442_ = l_String_Slice_pos_x21(v_s_1429_, v___x_1436_);
            crate::leanh::lean_dec(v___x_1436_);
            v___x_1443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1443_, 0, v___x_1442_);
            return v___x_1443_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed(
    mut v_pat_1444_: *mut crate::leanh::LeanObject,
    mut v_s_1445_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1446_ =
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f(v_pat_1444_, v_s_1445_);
    crate::leanh::lean_dec_ref(v_s_1445_);
    crate::leanh::lean_dec_ref(v_pat_1444_);
    return v_res_1446_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(
    mut v_pat_1447_: *mut crate::leanh::LeanObject,
    mut v_s_1448_: *mut crate::leanh::LeanObject,
    mut v_x_1449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1458_: u8 = 0;
    v_str_1450_ = crate::leanh::lean_ctor_get(v_pat_1447_, 0);
    v_startInclusive_1451_ = crate::leanh::lean_ctor_get(v_pat_1447_, 1);
    v_endExclusive_1452_ = crate::leanh::lean_ctor_get(v_pat_1447_, 2);
    v_str_1453_ = crate::leanh::lean_ctor_get(v_s_1448_, 0);
    v_startInclusive_1454_ = crate::leanh::lean_ctor_get(v_s_1448_, 1);
    v_endExclusive_1455_ = crate::leanh::lean_ctor_get(v_s_1448_, 2);
    v___x_1456_ = lean_nat_sub(v_endExclusive_1452_, v_startInclusive_1451_);
    v___x_1457_ = lean_nat_sub(v_endExclusive_1455_, v_startInclusive_1454_);
    v___x_1458_ = lean_nat_dec_le(v___x_1456_, v___x_1457_);
    crate::leanh::lean_dec(v___x_1457_);
    if v___x_1458_ == 0 {
        let mut v___x_1459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1456_);
        v___x_1459_ = crate::leanh::lean_box(0);
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
            let mut v___x_1461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1456_);
            v___x_1461_ = crate::leanh::lean_box(0);
            return v___x_1461_;
        } else {
            let mut v___x_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1462_ = l_String_Slice_pos_x21(v_s_1448_, v___x_1456_);
            crate::leanh::lean_dec(v___x_1456_);
            v___x_1463_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1463_, 0, v___x_1462_);
            return v___x_1463_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed(
    mut v_pat_1464_: *mut crate::leanh::LeanObject,
    mut v_s_1465_: *mut crate::leanh::LeanObject,
    mut v_x_1466_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1467_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0(
        v_pat_1464_,
        v_s_1465_,
        v_x_1466_,
    );
    crate::leanh::lean_dec_ref(v_s_1465_);
    crate::leanh::lean_dec_ref(v_pat_1464_);
    return v_res_1467_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern(
    mut v_pat_1468_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_pat_1468_, 2);
    v___f_1469_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1469_, 0, v_pat_1468_);
    v___x_1470_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1470_, 0, v_pat_1468_);
    v___x_1471_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1471_, 0, v_pat_1468_);
    v___x_1472_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1472_, 0, v___x_1470_);
    crate::leanh::lean_ctor_set(v___x_1472_, 1, v___f_1469_);
    crate::leanh::lean_ctor_set(v___x_1472_, 2, v___x_1471_);
    return v___x_1472_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instToForwardSearcher__1(
    mut v_pat_1473_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1474_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1475_ = lean_string_utf8_byte_size(v_pat_1473_);
    v___x_1476_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1476_, 0, v_pat_1473_);
    crate::leanh::lean_ctor_set(v___x_1476_, 1, v___x_1474_);
    crate::leanh::lean_ctor_set(v___x_1476_, 2, v___x_1475_);
    v___x_1477_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_iter___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1477_, 0, v___x_1476_);
    return v___x_1477_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(
    mut v___x_1478_: *mut crate::leanh::LeanObject,
    mut v_pat_1479_: *mut crate::leanh::LeanObject,
    mut v___x_1480_: *mut crate::leanh::LeanObject,
    mut v_s_1481_: *mut crate::leanh::LeanObject,
    mut v_x_1482_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1487_: u8 = 0;
    v_str_1483_ = crate::leanh::lean_ctor_get(v_s_1481_, 0);
    v_startInclusive_1484_ = crate::leanh::lean_ctor_get(v_s_1481_, 1);
    v_endExclusive_1485_ = crate::leanh::lean_ctor_get(v_s_1481_, 2);
    v___x_1486_ = lean_nat_sub(v_endExclusive_1485_, v_startInclusive_1484_);
    v___x_1487_ = lean_nat_dec_le(v___x_1478_, v___x_1486_);
    crate::leanh::lean_dec(v___x_1486_);
    if v___x_1487_ == 0 {
        let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1488_ = crate::leanh::lean_box(0);
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
            let mut v___x_1490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1490_ = crate::leanh::lean_box(0);
            return v___x_1490_;
        } else {
            let mut v___x_1491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1491_ = l_String_Slice_pos_x21(v_s_1481_, v___x_1478_);
            v___x_1492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1492_, 0, v___x_1491_);
            return v___x_1492_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed(
    mut v___x_1493_: *mut crate::leanh::LeanObject,
    mut v_pat_1494_: *mut crate::leanh::LeanObject,
    mut v___x_1495_: *mut crate::leanh::LeanObject,
    mut v_s_1496_: *mut crate::leanh::LeanObject,
    mut v_x_1497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1498_ = l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0(
        v___x_1493_,
        v_pat_1494_,
        v___x_1495_,
        v_s_1496_,
        v_x_1497_,
    );
    crate::leanh::lean_dec_ref(v_s_1496_);
    crate::leanh::lean_dec(v___x_1495_);
    crate::leanh::lean_dec_ref(v_pat_1494_);
    crate::leanh::lean_dec(v___x_1493_);
    return v_res_1498_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1(
    mut v_pat_1499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1500_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1501_ = lean_string_utf8_byte_size(v_pat_1499_);
    crate::leanh::lean_inc_ref(v_pat_1499_);
    v___f_1502_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_instForwardPattern__1___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1502_, 0, v___x_1501_);
    crate::leanh::lean_closure_set(v___f_1502_, 1, v_pat_1499_);
    crate::leanh::lean_closure_set(v___f_1502_, 2, v___x_1500_);
    v___x_1503_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1503_, 0, v_pat_1499_);
    crate::leanh::lean_ctor_set(v___x_1503_, 1, v___x_1500_);
    crate::leanh::lean_ctor_set(v___x_1503_, 2, v___x_1501_);
    crate::leanh::lean_inc_ref(v___x_1503_);
    v___x_1504_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_skipPrefix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1504_, 0, v___x_1503_);
    v___x_1505_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ForwardSliceSearcher_startsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1505_, 0, v___x_1503_);
    v___x_1506_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1506_, 0, v___x_1504_);
    crate::leanh::lean_ctor_set(v___x_1506_, 1, v___f_1502_);
    crate::leanh::lean_ctor_set(v___x_1506_, 2, v___x_1505_);
    return v___x_1506_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(
    mut v_pat_1507_: *mut crate::leanh::LeanObject,
    mut v_s_1508_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1517_: u8 = 0;
    v_str_1509_ = crate::leanh::lean_ctor_get(v_pat_1507_, 0);
    v_startInclusive_1510_ = crate::leanh::lean_ctor_get(v_pat_1507_, 1);
    v_endExclusive_1511_ = crate::leanh::lean_ctor_get(v_pat_1507_, 2);
    v_str_1512_ = crate::leanh::lean_ctor_get(v_s_1508_, 0);
    v_startInclusive_1513_ = crate::leanh::lean_ctor_get(v_s_1508_, 1);
    v_endExclusive_1514_ = crate::leanh::lean_ctor_get(v_s_1508_, 2);
    v___x_1515_ = lean_nat_sub(v_endExclusive_1511_, v_startInclusive_1510_);
    v___x_1516_ = lean_nat_sub(v_endExclusive_1514_, v_startInclusive_1513_);
    v___x_1517_ = lean_nat_dec_le(v___x_1515_, v___x_1516_);
    if v___x_1517_ == 0 {
        crate::leanh::lean_dec(v___x_1516_);
        crate::leanh::lean_dec(v___x_1515_);
        return v___x_1517_;
    } else {
        let mut v___x_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1520_: u8 = 0;
        v___x_1518_ = lean_nat_sub(v___x_1516_, v___x_1515_);
        crate::leanh::lean_dec(v___x_1516_);
        v___x_1519_ = lean_nat_add(v_startInclusive_1513_, v___x_1518_);
        crate::leanh::lean_dec(v___x_1518_);
        v___x_1520_ = lean_string_memcmp(
            v_str_1512_,
            v_str_1509_,
            v___x_1519_,
            v_startInclusive_1510_,
            v___x_1515_,
        );
        crate::leanh::lean_dec(v___x_1515_);
        crate::leanh::lean_dec(v___x_1519_);
        return v___x_1520_;
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed(
    mut v_pat_1521_: *mut crate::leanh::LeanObject,
    mut v_s_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1523_: u8 = 0;
    let mut v_r_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1523_ = l_String_Slice_Pattern_BackwardSliceSearcher_endsWith(v_pat_1521_, v_s_1522_);
    crate::leanh::lean_dec_ref(v_s_1522_);
    crate::leanh::lean_dec_ref(v_pat_1521_);
    v_r_1524_ = crate::leanh::lean_box((v_res_1523_) as usize);
    return v_r_1524_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(
    mut v_pat_1525_: *mut crate::leanh::LeanObject,
    mut v_s_1526_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1535_: u8 = 0;
    v_str_1527_ = crate::leanh::lean_ctor_get(v_pat_1525_, 0);
    v_startInclusive_1528_ = crate::leanh::lean_ctor_get(v_pat_1525_, 1);
    v_endExclusive_1529_ = crate::leanh::lean_ctor_get(v_pat_1525_, 2);
    v_str_1530_ = crate::leanh::lean_ctor_get(v_s_1526_, 0);
    v_startInclusive_1531_ = crate::leanh::lean_ctor_get(v_s_1526_, 1);
    v_endExclusive_1532_ = crate::leanh::lean_ctor_get(v_s_1526_, 2);
    v___x_1533_ = lean_nat_sub(v_endExclusive_1529_, v_startInclusive_1528_);
    v___x_1534_ = lean_nat_sub(v_endExclusive_1532_, v_startInclusive_1531_);
    v___x_1535_ = lean_nat_dec_le(v___x_1533_, v___x_1534_);
    if v___x_1535_ == 0 {
        let mut v___x_1536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1534_);
        crate::leanh::lean_dec(v___x_1533_);
        v___x_1536_ = crate::leanh::lean_box(0);
        return v___x_1536_;
    } else {
        let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1539_: u8 = 0;
        v___x_1537_ = lean_nat_sub(v___x_1534_, v___x_1533_);
        crate::leanh::lean_dec(v___x_1534_);
        v___x_1538_ = lean_nat_add(v_startInclusive_1531_, v___x_1537_);
        v___x_1539_ = lean_string_memcmp(
            v_str_1530_,
            v_str_1527_,
            v___x_1538_,
            v_startInclusive_1528_,
            v___x_1533_,
        );
        crate::leanh::lean_dec(v___x_1533_);
        crate::leanh::lean_dec(v___x_1538_);
        if v___x_1539_ == 0 {
            let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1537_);
            v___x_1540_ = crate::leanh::lean_box(0);
            return v___x_1540_;
        } else {
            let mut v___x_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1541_ = l_String_Slice_pos_x21(v_s_1526_, v___x_1537_);
            crate::leanh::lean_dec(v___x_1537_);
            v___x_1542_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1542_, 0, v___x_1541_);
            return v___x_1542_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed(
    mut v_pat_1543_: *mut crate::leanh::LeanObject,
    mut v_s_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1545_ =
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f(v_pat_1543_, v_s_1544_);
    crate::leanh::lean_dec_ref(v_s_1544_);
    crate::leanh::lean_dec_ref(v_pat_1543_);
    return v_res_1545_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(
    mut v_pat_1546_: *mut crate::leanh::LeanObject,
    mut v_s_1547_: *mut crate::leanh::LeanObject,
    mut v_x_1548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1557_: u8 = 0;
    v_str_1549_ = crate::leanh::lean_ctor_get(v_pat_1546_, 0);
    v_startInclusive_1550_ = crate::leanh::lean_ctor_get(v_pat_1546_, 1);
    v_endExclusive_1551_ = crate::leanh::lean_ctor_get(v_pat_1546_, 2);
    v_str_1552_ = crate::leanh::lean_ctor_get(v_s_1547_, 0);
    v_startInclusive_1553_ = crate::leanh::lean_ctor_get(v_s_1547_, 1);
    v_endExclusive_1554_ = crate::leanh::lean_ctor_get(v_s_1547_, 2);
    v___x_1555_ = lean_nat_sub(v_endExclusive_1551_, v_startInclusive_1550_);
    v___x_1556_ = lean_nat_sub(v_endExclusive_1554_, v_startInclusive_1553_);
    v___x_1557_ = lean_nat_dec_le(v___x_1555_, v___x_1556_);
    if v___x_1557_ == 0 {
        let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1556_);
        crate::leanh::lean_dec(v___x_1555_);
        v___x_1558_ = crate::leanh::lean_box(0);
        return v___x_1558_;
    } else {
        let mut v___x_1559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1561_: u8 = 0;
        v___x_1559_ = lean_nat_sub(v___x_1556_, v___x_1555_);
        crate::leanh::lean_dec(v___x_1556_);
        v___x_1560_ = lean_nat_add(v_startInclusive_1553_, v___x_1559_);
        v___x_1561_ = lean_string_memcmp(
            v_str_1552_,
            v_str_1549_,
            v___x_1560_,
            v_startInclusive_1550_,
            v___x_1555_,
        );
        crate::leanh::lean_dec(v___x_1555_);
        crate::leanh::lean_dec(v___x_1560_);
        if v___x_1561_ == 0 {
            let mut v___x_1562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1559_);
            v___x_1562_ = crate::leanh::lean_box(0);
            return v___x_1562_;
        } else {
            let mut v___x_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1563_ = l_String_Slice_pos_x21(v_s_1547_, v___x_1559_);
            crate::leanh::lean_dec(v___x_1559_);
            v___x_1564_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1564_, 0, v___x_1563_);
            return v___x_1564_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed(
    mut v_pat_1565_: *mut crate::leanh::LeanObject,
    mut v_s_1566_: *mut crate::leanh::LeanObject,
    mut v_x_1567_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1568_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0(
        v_pat_1565_,
        v_s_1566_,
        v_x_1567_,
    );
    crate::leanh::lean_dec_ref(v_s_1566_);
    crate::leanh::lean_dec_ref(v_pat_1565_);
    return v_res_1568_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern(
    mut v_pat_1569_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref_n(v_pat_1569_, 2);
    v___f_1570_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1570_, 0, v_pat_1569_);
    v___x_1571_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1571_, 0, v_pat_1569_);
    v___x_1572_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1572_, 0, v_pat_1569_);
    v___x_1573_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1573_, 0, v___x_1571_);
    crate::leanh::lean_ctor_set(v___x_1573_, 1, v___f_1570_);
    crate::leanh::lean_ctor_set(v___x_1573_, 2, v___x_1572_);
    return v___x_1573_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(
    mut v___x_1574_: *mut crate::leanh::LeanObject,
    mut v_pat_1575_: *mut crate::leanh::LeanObject,
    mut v___x_1576_: *mut crate::leanh::LeanObject,
    mut v_s_1577_: *mut crate::leanh::LeanObject,
    mut v_x_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: u8 = 0;
    v_str_1579_ = crate::leanh::lean_ctor_get(v_s_1577_, 0);
    v_startInclusive_1580_ = crate::leanh::lean_ctor_get(v_s_1577_, 1);
    v_endExclusive_1581_ = crate::leanh::lean_ctor_get(v_s_1577_, 2);
    v___x_1582_ = lean_nat_sub(v_endExclusive_1581_, v_startInclusive_1580_);
    v___x_1583_ = lean_nat_dec_le(v___x_1574_, v___x_1582_);
    if v___x_1583_ == 0 {
        let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1582_);
        v___x_1584_ = crate::leanh::lean_box(0);
        return v___x_1584_;
    } else {
        let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1587_: u8 = 0;
        v___x_1585_ = lean_nat_sub(v___x_1582_, v___x_1574_);
        crate::leanh::lean_dec(v___x_1582_);
        v___x_1586_ = lean_nat_add(v_startInclusive_1580_, v___x_1585_);
        v___x_1587_ = lean_string_memcmp(
            v_str_1579_,
            v_pat_1575_,
            v___x_1586_,
            v___x_1576_,
            v___x_1574_,
        );
        crate::leanh::lean_dec(v___x_1586_);
        if v___x_1587_ == 0 {
            let mut v___x_1588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v___x_1585_);
            v___x_1588_ = crate::leanh::lean_box(0);
            return v___x_1588_;
        } else {
            let mut v___x_1589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_1589_ = l_String_Slice_pos_x21(v_s_1577_, v___x_1585_);
            crate::leanh::lean_dec(v___x_1585_);
            v___x_1590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
            crate::leanh::lean_ctor_set(v___x_1590_, 0, v___x_1589_);
            return v___x_1590_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed(
    mut v___x_1591_: *mut crate::leanh::LeanObject,
    mut v_pat_1592_: *mut crate::leanh::LeanObject,
    mut v___x_1593_: *mut crate::leanh::LeanObject,
    mut v_s_1594_: *mut crate::leanh::LeanObject,
    mut v_x_1595_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1596_ = l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0(
        v___x_1591_,
        v_pat_1592_,
        v___x_1593_,
        v_s_1594_,
        v_x_1595_,
    );
    crate::leanh::lean_dec_ref(v_s_1594_);
    crate::leanh::lean_dec(v___x_1593_);
    crate::leanh::lean_dec_ref(v_pat_1592_);
    crate::leanh::lean_dec(v___x_1591_);
    return v_res_1596_;
}
pub unsafe fn l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1(
    mut v_pat_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1598_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1599_ = lean_string_utf8_byte_size(v_pat_1597_);
    crate::leanh::lean_inc_ref(v_pat_1597_);
    v___f_1600_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_instBackwardPattern__1___lam__0___boxed
            as *mut core::ffi::c_void,
        5,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1600_, 0, v___x_1599_);
    crate::leanh::lean_closure_set(v___f_1600_, 1, v_pat_1597_);
    crate::leanh::lean_closure_set(v___f_1600_, 2, v___x_1598_);
    v___x_1601_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1601_, 0, v_pat_1597_);
    crate::leanh::lean_ctor_set(v___x_1601_, 1, v___x_1598_);
    crate::leanh::lean_ctor_set(v___x_1601_, 2, v___x_1599_);
    crate::leanh::lean_inc_ref(v___x_1601_);
    v___x_1602_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_skipSuffix_x3f___boxed
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1602_, 0, v___x_1601_);
    v___x_1603_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_BackwardSliceSearcher_endsWith___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___x_1603_, 0, v___x_1601_);
    v___x_1604_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1604_, 0, v___x_1602_);
    crate::leanh::lean_ctor_set(v___x_1604_, 1, v___f_1600_);
    crate::leanh::lean_ctor_set(v___x_1604_, 2, v___x_1603_);
    return v___x_1604_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_String(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_String(
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
pub unsafe fn initialize_Init_Data_String_Pattern_String(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Vector_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_String(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_String(builtin);
}

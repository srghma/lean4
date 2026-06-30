// Lean compiler output
// Module: Init.Data.String.Pattern.Basic
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.String.Defs Init.Data.String.Basic Init.Data.String.FindPos Init.Data.String.Lemmas.FindPos Init.Data.Iterators.Consumers.Loop Init.Omega Init.Data.String.Lemmas.IsEmpty Init.Data.String.Termination Init.Data.String.OrderInstances Init.Data.String.Lemmas.Order
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_get_byte_fast,
    lean_string_memcmp, lean_string_utf8_next_fast, lean_uint8_dec_eq,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Monadic::Loop::{
    initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::Defs::{
    initialize_Init_Data_String_Defs, runtime_initialize_Init_Data_String_Defs,
};
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, l_String_Slice_posLE,
    runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::IsEmpty::{
    initialize_Init_Data_String_Lemmas_IsEmpty, runtime_initialize_Init_Data_String_Lemmas_IsEmpty,
};
use crate::r#gen::Init::Data::String::Lemmas::Order::{
    initialize_Init_Data_String_Lemmas_Order, runtime_initialize_Init_Data_String_Lemmas_Order,
};
use crate::r#gen::Init::Data::String::OrderInstances::{
    initialize_Init_Data_String_OrderInstances, runtime_initialize_Init_Data_String_OrderInstances,
};
use crate::r#gen::Init::Data::String::Termination::{
    initialize_Init_Data_String_Termination, runtime_initialize_Init_Data_String_Termination,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
pub static l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value:
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
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
    ],
};
static mut l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(
    mut v_x_674_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_674_) == 0 {
        let mut v___x_675_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_675_ = leanh::lean_unsigned_to_nat(0);
        return v___x_675_;
    } else {
        let mut v___x_676_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_676_ = leanh::lean_unsigned_to_nat(1);
        return v___x_676_;
    }
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___redArg___boxed(
    mut v_x_677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_678_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_677_);
    leanh::lean_dec_ref(v_x_677_);
    return v_res_678_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx(
    mut v_s_679_: *mut leanh::LeanObject,
    mut v_x_680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_680_);
    return v___x_681_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___boxed(
    mut v_s_682_: *mut leanh::LeanObject,
    mut v_x_683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_684_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_String_Slice_Pattern_SearchStep_ctorIdx(v_s_682_, v_x_683_);
    leanh::lean_dec_ref(v_x_683_);
    leanh::lean_dec_ref(v_s_682_);
    return v_res_684_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim___redArg(
    mut v_t_685_: *mut leanh::LeanObject,
    mut v_k_686_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startPos_687_ = leanh::lean_ctor_get(v_t_685_, 0);
    leanh::lean_inc(v_startPos_687_);
    v_endPos_688_ = leanh::lean_ctor_get(v_t_685_, 1);
    leanh::lean_inc(v_endPos_688_);
    leanh::lean_dec_ref(v_t_685_);
    v___x_689_ = leanh::lean_apply_2(v_k_686_, v_startPos_687_, v_endPos_688_);
    return v___x_689_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim(
    mut v_s_690_: *mut leanh::LeanObject,
    mut v_motive_691_: *mut leanh::LeanObject,
    mut v_ctorIdx_692_: *mut leanh::LeanObject,
    mut v_t_693_: *mut leanh::LeanObject,
    mut v_h_694_: *mut leanh::LeanObject,
    mut v_k_695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_693_, v_k_695_);
    return v___x_696_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim___boxed(
    mut v_s_697_: *mut leanh::LeanObject,
    mut v_motive_698_: *mut leanh::LeanObject,
    mut v_ctorIdx_699_: *mut leanh::LeanObject,
    mut v_t_700_: *mut leanh::LeanObject,
    mut v_h_701_: *mut leanh::LeanObject,
    mut v_k_702_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_String_Slice_Pattern_SearchStep_ctorElim(
        v_s_697_,
        v_motive_698_,
        v_ctorIdx_699_,
        v_t_700_,
        v_h_701_,
        v_k_702_,
    );
    leanh::lean_dec(v_ctorIdx_699_);
    leanh::lean_dec_ref(v_s_697_);
    return v_res_703_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim___redArg(
    mut v_t_704_: *mut leanh::LeanObject,
    mut v_rejected_705_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_704_, v_rejected_705_);
    return v___x_706_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim(
    mut v_s_707_: *mut leanh::LeanObject,
    mut v_motive_708_: *mut leanh::LeanObject,
    mut v_t_709_: *mut leanh::LeanObject,
    mut v_h_710_: *mut leanh::LeanObject,
    mut v_rejected_711_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_712_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_709_, v_rejected_711_);
    return v___x_712_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim___boxed(
    mut v_s_713_: *mut leanh::LeanObject,
    mut v_motive_714_: *mut leanh::LeanObject,
    mut v_t_715_: *mut leanh::LeanObject,
    mut v_h_716_: *mut leanh::LeanObject,
    mut v_rejected_717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_String_Slice_Pattern_SearchStep_rejected_elim(
        v_s_713_,
        v_motive_714_,
        v_t_715_,
        v_h_716_,
        v_rejected_717_,
    );
    leanh::lean_dec_ref(v_s_713_);
    return v_res_718_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim___redArg(
    mut v_t_719_: *mut leanh::LeanObject,
    mut v_matched_720_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_721_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_719_, v_matched_720_);
    return v___x_721_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim(
    mut v_s_722_: *mut leanh::LeanObject,
    mut v_motive_723_: *mut leanh::LeanObject,
    mut v_t_724_: *mut leanh::LeanObject,
    mut v_h_725_: *mut leanh::LeanObject,
    mut v_matched_726_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_727_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_724_, v_matched_726_);
    return v___x_727_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim___boxed(
    mut v_s_728_: *mut leanh::LeanObject,
    mut v_motive_729_: *mut leanh::LeanObject,
    mut v_t_730_: *mut leanh::LeanObject,
    mut v_h_731_: *mut leanh::LeanObject,
    mut v_matched_732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_733_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_String_Slice_Pattern_SearchStep_matched_elim(
        v_s_728_,
        v_motive_729_,
        v_t_730_,
        v_h_731_,
        v_matched_732_,
    );
    leanh::lean_dec_ref(v_s_728_);
    return v_res_733_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep_default(
    mut v_s_736_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_737_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0;
    return v___x_737_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(
    mut v_s_738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_s_738_);
    leanh::lean_dec_ref(v_s_738_);
    return v_res_739_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep(
    mut v_a_740_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_a_740_);
    return v___x_741_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep___boxed(
    mut v_a_742_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_743_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_743_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_742_);
    leanh::lean_dec_ref(v_a_742_);
    return v_res_743_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(
    mut v_x_744_: *mut leanh::LeanObject,
    mut v_x_745_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_a_747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: u8 = 0;
    let mut v___x_752_: u8 = 0;
    let mut v_startPos_753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v_startPos_758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_744_) == 0 {
                    if leanh::lean_obj_tag(v_x_745_) == 0 {
                        v_startPos_753_ = leanh::lean_ctor_get(v_x_744_, 0);
                        v_endPos_754_ = leanh::lean_ctor_get(v_x_744_, 1);
                        v_startPos_755_ = leanh::lean_ctor_get(v_x_745_, 0);
                        v_endPos_756_ = leanh::lean_ctor_get(v_x_745_, 1);
                        v_a_747_ = v_startPos_753_;
                        v_a_748_ = v_endPos_754_;
                        v_b_749_ = v_startPos_755_;
                        v_b_750_ = v_endPos_756_;
                        state = 1;
                        continue;
                    } else {
                        v___x_757_ = 0;
                        return v___x_757_;
                    }
                } else {
                    if leanh::lean_obj_tag(v_x_745_) == 1 {
                        v_startPos_758_ = leanh::lean_ctor_get(v_x_744_, 0);
                        v_endPos_759_ = leanh::lean_ctor_get(v_x_744_, 1);
                        v_startPos_760_ = leanh::lean_ctor_get(v_x_745_, 0);
                        v_endPos_761_ = leanh::lean_ctor_get(v_x_745_, 1);
                        v_a_747_ = v_startPos_758_;
                        v_a_748_ = v_endPos_759_;
                        v_b_749_ = v_startPos_760_;
                        v_b_750_ = v_endPos_761_;
                        state = 1;
                        continue;
                    } else {
                        v___x_762_ = 0;
                        return v___x_762_;
                    }
                }
            }
            1 => {
                v___x_751_ = lean_nat_dec_eq(v_a_747_, v_b_749_);
                if v___x_751_ == 0 {
                    return v___x_751_;
                } else {
                    v___x_752_ = lean_nat_dec_eq(v_a_748_, v_b_750_);
                    return v___x_752_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq___redArg___boxed(
    mut v_x_763_: *mut leanh::LeanObject,
    mut v_x_764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_763_, v_x_764_);
    leanh::lean_dec_ref(v_x_764_);
    leanh::lean_dec_ref(v_x_763_);
    v_r_766_ = leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq(
    mut v_s_767_: *mut leanh::LeanObject,
    mut v_x_768_: *mut leanh::LeanObject,
    mut v_x_769_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_770_: u8 = 0;
    v___x_770_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_768_, v_x_769_);
    return v___x_770_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(
    mut v_s_771_: *mut leanh::LeanObject,
    mut v_x_772_: *mut leanh::LeanObject,
    mut v_x_773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_774_: u8 = 0;
    let mut v_r_775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_771_, v_x_772_, v_x_773_);
    leanh::lean_dec_ref(v_x_773_);
    leanh::lean_dec_ref(v_x_772_);
    leanh::lean_dec_ref(v_s_771_);
    v_r_775_ = leanh::lean_box((v_res_774_) as usize);
    return v_r_775_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep(
    mut v_s_776_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_777_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_instBEqSearchStep_beq___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    leanh::lean_closure_set(v___x_777_, 0, v_s_776_);
    return v___x_777_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___redArg(
    mut v_st_778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startPos_779_ = leanh::lean_ctor_get(v_st_778_, 0);
    leanh::lean_inc(v_startPos_779_);
    return v_startPos_779_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(
    mut v_st_780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_781_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_780_);
    leanh::lean_dec_ref(v_st_780_);
    return v_res_781_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos(
    mut v_s_782_: *mut leanh::LeanObject,
    mut v_st_783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startPos_784_ = leanh::lean_ctor_get(v_st_783_, 0);
    leanh::lean_inc(v_startPos_784_);
    return v_startPos_784_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___boxed(
    mut v_s_785_: *mut leanh::LeanObject,
    mut v_st_786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_785_, v_st_786_);
    leanh::lean_dec_ref(v_st_786_);
    leanh::lean_dec_ref(v_s_785_);
    return v_res_787_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___redArg(
    mut v_st_788_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_endPos_789_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_endPos_789_ = leanh::lean_ctor_get(v_st_788_, 1);
    leanh::lean_inc(v_endPos_789_);
    return v_endPos_789_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(
    mut v_st_790_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_791_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_790_);
    leanh::lean_dec_ref(v_st_790_);
    return v_res_791_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos(
    mut v_s_792_: *mut leanh::LeanObject,
    mut v_st_793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_endPos_794_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_endPos_794_ = leanh::lean_ctor_get(v_st_793_, 1);
    leanh::lean_inc(v_endPos_794_);
    return v_endPos_794_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___boxed(
    mut v_s_795_: *mut leanh::LeanObject,
    mut v_st_796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_795_, v_st_796_);
    leanh::lean_dec_ref(v_st_796_);
    leanh::lean_dec_ref(v_s_795_);
    return v_res_797_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(
    mut v_p_798_: *mut leanh::LeanObject,
    mut v_st_799_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_810_: u8 = 0;
    let mut v_startPos_811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_st_799_) == 0 {
                    v_startPos_800_ = leanh::lean_ctor_get(v_st_799_, 0);
                    v_endPos_801_ = leanh::lean_ctor_get(v_st_799_, 1);
                    v_isSharedCheck_810_ = (!leanh::lean_is_exclusive(v_st_799_)) as u8;
                    if v_isSharedCheck_810_ == 0 {
                        v___x_803_ = v_st_799_;
                        v_isShared_804_ = v_isSharedCheck_810_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_801_);
                        leanh::lean_inc(v_startPos_800_);
                        leanh::lean_dec(v_st_799_);
                        v___x_803_ = leanh::lean_box(0);
                        v_isShared_804_ = v_isSharedCheck_810_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_811_ = leanh::lean_ctor_get(v_st_799_, 0);
                    v_endPos_812_ = leanh::lean_ctor_get(v_st_799_, 1);
                    v_isSharedCheck_821_ = (!leanh::lean_is_exclusive(v_st_799_)) as u8;
                    if v_isSharedCheck_821_ == 0 {
                        v___x_814_ = v_st_799_;
                        v_isShared_815_ = v_isSharedCheck_821_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_812_);
                        leanh::lean_inc(v_startPos_811_);
                        leanh::lean_dec(v_st_799_);
                        v___x_814_ = leanh::lean_box(0);
                        v_isShared_815_ = v_isSharedCheck_821_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_805_ = lean_nat_add(v_p_798_, v_startPos_800_);
                leanh::lean_dec(v_startPos_800_);
                v___x_806_ = lean_nat_add(v_p_798_, v_endPos_801_);
                leanh::lean_dec(v_endPos_801_);
                if v_isShared_804_ == 0 {
                    leanh::lean_ctor_set(v___x_803_, 1, v___x_806_);
                    leanh::lean_ctor_set(v___x_803_, 0, v___x_805_);
                    v___x_808_ = v___x_803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_809_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
                    v___x_808_ = v_reuseFailAlloc_809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_808_;
            }
            3 => {
                v___x_816_ = lean_nat_add(v_p_798_, v_startPos_811_);
                leanh::lean_dec(v_startPos_811_);
                v___x_817_ = lean_nat_add(v_p_798_, v_endPos_812_);
                leanh::lean_dec(v_endPos_812_);
                if v_isShared_815_ == 0 {
                    leanh::lean_ctor_set(v___x_814_, 1, v___x_817_);
                    leanh::lean_ctor_set(v___x_814_, 0, v___x_816_);
                    v___x_819_ = v___x_814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_820_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
                    v___x_819_ = v_reuseFailAlloc_820_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_819_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg___boxed(
    mut v_p_822_: *mut leanh::LeanObject,
    mut v_st_823_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_824_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_822_, v_st_823_);
    leanh::lean_dec(v_p_822_);
    return v_res_824_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom(
    mut v_s_825_: *mut leanh::LeanObject,
    mut v_p_826_: *mut leanh::LeanObject,
    mut v_st_827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_826_, v_st_827_);
    return v___x_828_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(
    mut v_s_829_: *mut leanh::LeanObject,
    mut v_p_830_: *mut leanh::LeanObject,
    mut v_st_831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_829_, v_p_830_, v_st_831_);
    leanh::lean_dec(v_p_830_);
    leanh::lean_dec_ref(v_s_829_);
    return v_res_832_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(
    mut v_st_833_: *mut leanh::LeanObject,
    mut v_h__1_834_: *mut leanh::LeanObject,
    mut v_h__2_835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_st_833_) == 0 {
        let mut v_startPos_836_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_837_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_835_);
        v_startPos_836_ = leanh::lean_ctor_get(v_st_833_, 0);
        leanh::lean_inc(v_startPos_836_);
        v_endPos_837_ = leanh::lean_ctor_get(v_st_833_, 1);
        leanh::lean_inc(v_endPos_837_);
        leanh::lean_dec_ref_known(v_st_833_, 2);
        v___x_838_ = leanh::lean_apply_2(v_h__1_834_, v_startPos_836_, v_endPos_837_);
        return v___x_838_;
    } else {
        let mut v_startPos_839_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_840_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_834_);
        v_startPos_839_ = leanh::lean_ctor_get(v_st_833_, 0);
        leanh::lean_inc(v_startPos_839_);
        v_endPos_840_ = leanh::lean_ctor_get(v_st_833_, 1);
        leanh::lean_inc(v_endPos_840_);
        leanh::lean_dec_ref_known(v_st_833_, 2);
        v___x_841_ = leanh::lean_apply_2(v_h__2_835_, v_startPos_839_, v_endPos_840_);
        return v___x_841_;
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(
    mut v_s_842_: *mut leanh::LeanObject,
    mut v_p_843_: *mut leanh::LeanObject,
    mut v_motive_844_: *mut leanh::LeanObject,
    mut v_st_845_: *mut leanh::LeanObject,
    mut v_h__1_846_: *mut leanh::LeanObject,
    mut v_h__2_847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_st_845_) == 0 {
        let mut v_startPos_848_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_849_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__2_847_);
        v_startPos_848_ = leanh::lean_ctor_get(v_st_845_, 0);
        leanh::lean_inc(v_startPos_848_);
        v_endPos_849_ = leanh::lean_ctor_get(v_st_845_, 1);
        leanh::lean_inc(v_endPos_849_);
        leanh::lean_dec_ref_known(v_st_845_, 2);
        v___x_850_ = leanh::lean_apply_2(v_h__1_846_, v_startPos_848_, v_endPos_849_);
        return v___x_850_;
    } else {
        let mut v_startPos_851_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_852_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_h__1_846_);
        v_startPos_851_ = leanh::lean_ctor_get(v_st_845_, 0);
        leanh::lean_inc(v_startPos_851_);
        v_endPos_852_ = leanh::lean_ctor_get(v_st_845_, 1);
        leanh::lean_inc(v_endPos_852_);
        leanh::lean_dec_ref_known(v_st_845_, 2);
        v___x_853_ = leanh::lean_apply_2(v_h__2_847_, v_startPos_851_, v_endPos_852_);
        return v___x_853_;
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(
    mut v_s_854_: *mut leanh::LeanObject,
    mut v_p_855_: *mut leanh::LeanObject,
    mut v_motive_856_: *mut leanh::LeanObject,
    mut v_st_857_: *mut leanh::LeanObject,
    mut v_h__1_858_: *mut leanh::LeanObject,
    mut v_h__2_859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_854_, v_p_855_, v_motive_856_, v_st_857_, v_h__1_858_, v_h__2_859_);
    leanh::lean_dec(v_p_855_);
    leanh::lean_dec_ref(v_s_854_);
    return v_res_860_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_cast___redArg(
    mut v_x_861_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v_startPos_871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_875_: u8 = 0;
    let mut v___x_877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_861_) == 0 {
                    v_startPos_862_ = leanh::lean_ctor_get(v_x_861_, 0);
                    v_endPos_863_ = leanh::lean_ctor_get(v_x_861_, 1);
                    v_isSharedCheck_870_ = (!leanh::lean_is_exclusive(v_x_861_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_865_ = v_x_861_;
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_863_);
                        leanh::lean_inc(v_startPos_862_);
                        leanh::lean_dec(v_x_861_);
                        v___x_865_ = leanh::lean_box(0);
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_871_ = leanh::lean_ctor_get(v_x_861_, 0);
                    v_endPos_872_ = leanh::lean_ctor_get(v_x_861_, 1);
                    v_isSharedCheck_879_ = (!leanh::lean_is_exclusive(v_x_861_)) as u8;
                    if v_isSharedCheck_879_ == 0 {
                        v___x_874_ = v_x_861_;
                        v_isShared_875_ = v_isSharedCheck_879_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_872_);
                        leanh::lean_inc(v_startPos_871_);
                        leanh::lean_dec(v_x_861_);
                        v___x_874_ = leanh::lean_box(0);
                        v_isShared_875_ = v_isSharedCheck_879_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_866_ == 0 {
                    v___x_868_ = v___x_865_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_869_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_startPos_862_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v_endPos_863_);
                    v___x_868_ = v_reuseFailAlloc_869_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_868_;
            }
            3 => {
                if v_isShared_875_ == 0 {
                    v___x_877_ = v___x_874_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_878_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_878_, 0, v_startPos_871_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_878_, 1, v_endPos_872_);
                    v___x_877_ = v_reuseFailAlloc_878_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_877_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_cast(
    mut v_s_880_: *mut leanh::LeanObject,
    mut v_t_881_: *mut leanh::LeanObject,
    mut v_hst_882_: *mut leanh::LeanObject,
    mut v_x_883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startPos_884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_892_: u8 = 0;
    let mut v_startPos_893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_883_) == 0 {
                    v_startPos_884_ = leanh::lean_ctor_get(v_x_883_, 0);
                    v_endPos_885_ = leanh::lean_ctor_get(v_x_883_, 1);
                    v_isSharedCheck_892_ = (!leanh::lean_is_exclusive(v_x_883_)) as u8;
                    if v_isSharedCheck_892_ == 0 {
                        v___x_887_ = v_x_883_;
                        v_isShared_888_ = v_isSharedCheck_892_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_885_);
                        leanh::lean_inc(v_startPos_884_);
                        leanh::lean_dec(v_x_883_);
                        v___x_887_ = leanh::lean_box(0);
                        v_isShared_888_ = v_isSharedCheck_892_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_893_ = leanh::lean_ctor_get(v_x_883_, 0);
                    v_endPos_894_ = leanh::lean_ctor_get(v_x_883_, 1);
                    v_isSharedCheck_901_ = (!leanh::lean_is_exclusive(v_x_883_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v___x_896_ = v_x_883_;
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_endPos_894_);
                        leanh::lean_inc(v_startPos_893_);
                        leanh::lean_dec(v_x_883_);
                        v___x_896_ = leanh::lean_box(0);
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_888_ == 0 {
                    v___x_890_ = v___x_887_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_891_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v_startPos_884_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v_endPos_885_);
                    v___x_890_ = v_reuseFailAlloc_891_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_890_;
            }
            3 => {
                if v_isShared_897_ == 0 {
                    v___x_899_ = v___x_896_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_900_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_startPos_893_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_900_, 1, v_endPos_894_);
                    v___x_899_ = v_reuseFailAlloc_900_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_899_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_cast___boxed(
    mut v_s_902_: *mut leanh::LeanObject,
    mut v_t_903_: *mut leanh::LeanObject,
    mut v_hst_904_: *mut leanh::LeanObject,
    mut v_x_905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_String_Slice_Pattern_SearchStep_cast(v_s_902_, v_t_903_, v_hst_904_, v_x_905_);
    leanh::lean_dec_ref(v_t_903_);
    leanh::lean_dec_ref(v_s_902_);
    return v_res_906_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(
    mut v_inst_907_: *mut leanh::LeanObject,
    mut v_s_908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipPrefix_x3f_909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipPrefix_x3f_909_ = leanh::lean_ctor_get(v_inst_907_, 0);
    leanh::lean_inc_ref(v_skipPrefix_x3f_909_);
    leanh::lean_dec_ref(v_inst_907_);
    v___x_910_ = leanh::lean_apply_1(v_skipPrefix_x3f_909_, v_s_908_);
    return v___x_910_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(
    mut v_00_u03c1_911_: *mut leanh::LeanObject,
    mut v_pat_912_: *mut leanh::LeanObject,
    mut v_inst_913_: *mut leanh::LeanObject,
    mut v_s_914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ =
        l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_913_, v_s_914_);
    return v___x_915_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(
    mut v_00_u03c1_916_: *mut leanh::LeanObject,
    mut v_pat_917_: *mut leanh::LeanObject,
    mut v_inst_918_: *mut leanh::LeanObject,
    mut v_s_919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(
        v_00_u03c1_916_,
        v_pat_917_,
        v_inst_918_,
        v_s_919_,
    );
    leanh::lean_dec(v_pat_917_);
    return v_res_920_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(
    mut v_00_u03c1_921_: *mut leanh::LeanObject,
    mut v_pat_922_: *mut leanh::LeanObject,
    mut v_s_923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_924_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = leanh::lean_unsigned_to_nat(0);
    return v___x_924_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(
    mut v_00_u03c1_925_: *mut leanh::LeanObject,
    mut v_pat_926_: *mut leanh::LeanObject,
    mut v_s_927_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ =
        l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(
            v_00_u03c1_925_,
            v_pat_926_,
            v_s_927_,
        );
    leanh::lean_dec_ref(v_s_927_);
    leanh::lean_dec(v_pat_926_);
    return v_res_928_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(
    mut v_a_929_: *mut leanh::LeanObject,
    mut v_a_930_: *mut leanh::LeanObject,
    mut v_a_931_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_932_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = leanh::lean_unsigned_to_nat(0);
    return v___x_932_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(
    mut v_a_933_: *mut leanh::LeanObject,
    mut v_a_934_: *mut leanh::LeanObject,
    mut v_a_935_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_936_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_936_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(
        v_a_933_, v_a_934_, v_a_935_,
    );
    leanh::lean_dec_ref(v_a_935_);
    leanh::lean_dec(v_a_934_);
    return v_res_936_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(
    mut v_00_u03c1_937_: *mut leanh::LeanObject,
    mut v_pat_938_: *mut leanh::LeanObject,
    mut v_s_939_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_940_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = leanh::lean_unsigned_to_nat(0);
    return v___x_940_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(
    mut v_00_u03c1_941_: *mut leanh::LeanObject,
    mut v_pat_942_: *mut leanh::LeanObject,
    mut v_s_943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(
        v_00_u03c1_941_,
        v_pat_942_,
        v_s_943_,
    );
    leanh::lean_dec_ref(v_s_943_);
    leanh::lean_dec(v_pat_942_);
    return v_res_944_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(
    mut v_s_945_: *mut leanh::LeanObject,
    mut v_inst_946_: *mut leanh::LeanObject,
    mut v_it_947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v_skipPrefixOfNonempty_x3f_956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_948_ = leanh::lean_ctor_get(v_s_945_, 0);
                v_startInclusive_949_ = leanh::lean_ctor_get(v_s_945_, 1);
                v_endExclusive_950_ = leanh::lean_ctor_get(v_s_945_, 2);
                v_isSharedCheck_971_ = (!leanh::lean_is_exclusive(v_s_945_)) as u8;
                if v_isSharedCheck_971_ == 0 {
                    v___x_952_ = v_s_945_;
                    v_isShared_953_ = v_isSharedCheck_971_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_950_);
                    leanh::lean_inc(v_startInclusive_949_);
                    leanh::lean_inc(v_str_948_);
                    leanh::lean_dec(v_s_945_);
                    v___x_952_ = leanh::lean_box(0);
                    v_isShared_953_ = v_isSharedCheck_971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_954_ = lean_nat_sub(v_endExclusive_950_, v_startInclusive_949_);
                v___x_955_ = lean_nat_dec_eq(v_it_947_, v___x_954_);
                leanh::lean_dec(v___x_954_);
                if v___x_955_ == 0 {
                    v_skipPrefixOfNonempty_x3f_956_ = leanh::lean_ctor_get(v_inst_946_, 1);
                    leanh::lean_inc_ref(v_skipPrefixOfNonempty_x3f_956_);
                    leanh::lean_dec_ref(v_inst_946_);
                    v___x_957_ = lean_nat_add(v_startInclusive_949_, v_it_947_);
                    leanh::lean_inc(v___x_957_);
                    leanh::lean_inc_ref(v_str_948_);
                    if v_isShared_953_ == 0 {
                        leanh::lean_ctor_set(v___x_952_, 1, v___x_957_);
                        v___x_959_ = v___x_952_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_969_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_969_, 0, v_str_948_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_957_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_969_, 2, v_endExclusive_950_);
                        v___x_959_ = v_reuseFailAlloc_969_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_952_);
                    leanh::lean_dec(v_endExclusive_950_);
                    leanh::lean_dec(v_startInclusive_949_);
                    leanh::lean_dec_ref(v_str_948_);
                    leanh::lean_dec(v_it_947_);
                    leanh::lean_dec_ref(v_inst_946_);
                    v___x_970_ = leanh::lean_box(2);
                    return v___x_970_;
                }
            }
            2 => {
                v___x_960_ = leanh::lean_apply_2(
                    v_skipPrefixOfNonempty_x3f_956_,
                    v___x_959_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_960_) == 0 {
                    v___x_961_ = lean_string_utf8_next_fast(v_str_948_, v___x_957_);
                    leanh::lean_dec(v___x_957_);
                    leanh::lean_dec_ref(v_str_948_);
                    v___x_962_ = lean_nat_sub(v___x_961_, v_startInclusive_949_);
                    leanh::lean_dec(v_startInclusive_949_);
                    leanh::lean_inc(v___x_962_);
                    v___x_963_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_963_, 0, v_it_947_);
                    leanh::lean_ctor_set(v___x_963_, 1, v___x_962_);
                    v___x_964_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_964_, 0, v___x_962_);
                    leanh::lean_ctor_set(v___x_964_, 1, v___x_963_);
                    return v___x_964_;
                } else {
                    leanh::lean_dec(v___x_957_);
                    leanh::lean_dec(v_startInclusive_949_);
                    leanh::lean_dec_ref(v_str_948_);
                    v_val_965_ = leanh::lean_ctor_get(v___x_960_, 0);
                    leanh::lean_inc(v_val_965_);
                    leanh::lean_dec_ref_known(v___x_960_, 1);
                    v___x_966_ = lean_nat_add(v_it_947_, v_val_965_);
                    leanh::lean_dec(v_val_965_);
                    leanh::lean_inc(v___x_966_);
                    v___x_967_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_967_, 0, v_it_947_);
                    leanh::lean_ctor_set(v___x_967_, 1, v___x_966_);
                    v___x_968_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_968_, 0, v___x_966_);
                    leanh::lean_ctor_set(v___x_968_, 1, v___x_967_);
                    return v___x_968_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(
    mut v_s_972_: *mut leanh::LeanObject,
    mut v_inst_973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_974_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_974_, 0, v_s_972_);
    leanh::lean_closure_set(v___f_974_, 1, v_inst_973_);
    return v___f_974_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(
    mut v_00_u03c1_975_: *mut leanh::LeanObject,
    mut v_pat_976_: *mut leanh::LeanObject,
    mut v_s_977_: *mut leanh::LeanObject,
    mut v_inst_978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_979_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_979_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_979_, 0, v_s_977_);
    leanh::lean_closure_set(v___f_979_, 1, v_inst_978_);
    return v___f_979_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(
    mut v_00_u03c1_980_: *mut leanh::LeanObject,
    mut v_pat_981_: *mut leanh::LeanObject,
    mut v_s_982_: *mut leanh::LeanObject,
    mut v_inst_983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_980_, v_pat_981_, v_s_982_, v_inst_983_);
    leanh::lean_dec(v_pat_981_);
    return v_res_984_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(
    mut v_00_u03c1_985_: *mut leanh::LeanObject,
    mut v_pat_986_: *mut leanh::LeanObject,
    mut v_s_987_: *mut leanh::LeanObject,
    mut v_inst_988_: *mut leanh::LeanObject,
    mut v_inst_989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_990_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = leanh::lean_box(0);
    return v___x_990_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(
    mut v_00_u03c1_991_: *mut leanh::LeanObject,
    mut v_pat_992_: *mut leanh::LeanObject,
    mut v_s_993_: *mut leanh::LeanObject,
    mut v_inst_994_: *mut leanh::LeanObject,
    mut v_inst_995_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_996_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_991_, v_pat_992_, v_s_993_, v_inst_994_, v_inst_995_);
    leanh::lean_dec_ref(v_inst_994_);
    leanh::lean_dec_ref(v_s_993_);
    leanh::lean_dec(v_pat_992_);
    return v_res_996_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(
    mut v___y_997_: *mut leanh::LeanObject,
    mut v_acc_998_: *mut leanh::LeanObject,
    mut v_recur_999_: *mut leanh::LeanObject,
    mut v_s_1000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    match leanh::lean_obj_tag(v_s_1000_) {
        0 => {
            let mut v_it_1001_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1002_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1003_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_it_1001_ = leanh::lean_ctor_get(v_s_1000_, 0);
            leanh::lean_inc(v_it_1001_);
            v_out_1002_ = leanh::lean_ctor_get(v_s_1000_, 1);
            leanh::lean_inc(v_out_1002_);
            leanh::lean_dec_ref_known(v_s_1000_, 2);
            v_val_1003_ = leanh::lean_apply_3(
                v___y_997_,
                v_out_1002_,
                leanh::lean_box(0),
                v_acc_998_,
            );
            if leanh::lean_obj_tag(v_val_1003_) == 0 {
                let mut v_a_1004_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec(v_it_1001_);
                leanh::lean_dec(v_recur_999_);
                v_a_1004_ = leanh::lean_ctor_get(v_val_1003_, 0);
                leanh::lean_inc(v_a_1004_);
                leanh::lean_dec_ref_known(v_val_1003_, 1);
                return v_a_1004_;
            } else {
                let mut v_a_1005_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: *mut leanh::LeanObject = core::ptr::null_mut();
                v_a_1005_ = leanh::lean_ctor_get(v_val_1003_, 0);
                leanh::lean_inc(v_a_1005_);
                leanh::lean_dec_ref_known(v_val_1003_, 1);
                v___x_1006_ = leanh::lean_apply_4(
                    v_recur_999_,
                    v_it_1001_,
                    v_a_1005_,
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                );
                return v___x_1006_;
            }
        }
        1 => {
            let mut v_it_1007_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1008_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___y_997_);
            v_it_1007_ = leanh::lean_ctor_get(v_s_1000_, 0);
            leanh::lean_inc(v_it_1007_);
            leanh::lean_dec_ref_known(v_s_1000_, 1);
            v___x_1008_ = leanh::lean_apply_4(
                v_recur_999_,
                v_it_1007_,
                v_acc_998_,
                leanh::lean_box(0),
                leanh::lean_box(0),
            );
            return v___x_1008_;
        }
        _ => {
            leanh::lean_dec(v_recur_999_);
            leanh::lean_dec_ref(v___y_997_);
            return v_acc_998_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(
    mut v_s_1009_: *mut leanh::LeanObject,
    mut v___y_1010_: *mut leanh::LeanObject,
    mut v_inst_1011_: *mut leanh::LeanObject,
    mut v_lift_1012_: *mut leanh::LeanObject,
    mut v_it_1013_: *mut leanh::LeanObject,
    mut v_acc_1014_: *mut leanh::LeanObject,
    mut v_hP_1015_: *mut leanh::LeanObject,
    mut v_recur_1016_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_str_1017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v___f_1023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    let mut v_skipPrefixOfNonempty_x3f_1026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1017_ = leanh::lean_ctor_get(v_s_1009_, 0);
                v_startInclusive_1018_ = leanh::lean_ctor_get(v_s_1009_, 1);
                v_endExclusive_1019_ = leanh::lean_ctor_get(v_s_1009_, 2);
                v_isSharedCheck_1044_ = (!leanh::lean_is_exclusive(v_s_1009_)) as u8;
                if v_isSharedCheck_1044_ == 0 {
                    v___x_1021_ = v_s_1009_;
                    v_isShared_1022_ = v_isSharedCheck_1044_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_endExclusive_1019_);
                    leanh::lean_inc(v_startInclusive_1018_);
                    leanh::lean_inc(v_str_1017_);
                    leanh::lean_dec(v_s_1009_);
                    v___x_1021_ = leanh::lean_box(0);
                    v_isShared_1022_ = v_isSharedCheck_1044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1023_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_1023_, 0, v___y_1010_);
                leanh::lean_closure_set(v___f_1023_, 1, v_acc_1014_);
                leanh::lean_closure_set(v___f_1023_, 2, v_recur_1016_);
                v___x_1024_ = lean_nat_sub(v_endExclusive_1019_, v_startInclusive_1018_);
                v___x_1025_ = lean_nat_dec_eq(v_it_1013_, v___x_1024_);
                leanh::lean_dec(v___x_1024_);
                if v___x_1025_ == 0 {
                    v_skipPrefixOfNonempty_x3f_1026_ = leanh::lean_ctor_get(v_inst_1011_, 1);
                    leanh::lean_inc_ref(v_skipPrefixOfNonempty_x3f_1026_);
                    leanh::lean_dec_ref(v_inst_1011_);
                    v___x_1027_ = lean_nat_add(v_startInclusive_1018_, v_it_1013_);
                    leanh::lean_inc(v___x_1027_);
                    leanh::lean_inc_ref(v_str_1017_);
                    if v_isShared_1022_ == 0 {
                        leanh::lean_ctor_set(v___x_1021_, 1, v___x_1027_);
                        v___x_1029_ = v___x_1021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1041_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_str_1017_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1027_);
                        leanh::lean_ctor_set(
                            v_reuseFailAlloc_1041_,
                            2,
                            v_endExclusive_1019_,
                        );
                        v___x_1029_ = v_reuseFailAlloc_1041_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_1021_);
                    leanh::lean_dec(v_endExclusive_1019_);
                    leanh::lean_dec(v_startInclusive_1018_);
                    leanh::lean_dec_ref(v_str_1017_);
                    leanh::lean_dec(v_it_1013_);
                    leanh::lean_dec_ref(v_inst_1011_);
                    v___x_1042_ = leanh::lean_box(2);
                    v___x_1043_ = leanh::lean_apply_4(
                        v_lift_1012_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1023_,
                        v___x_1042_,
                    );
                    return v___x_1043_;
                }
            }
            2 => {
                v___x_1030_ = leanh::lean_apply_2(
                    v_skipPrefixOfNonempty_x3f_1026_,
                    v___x_1029_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1030_) == 0 {
                    v___x_1031_ = lean_string_utf8_next_fast(v_str_1017_, v___x_1027_);
                    leanh::lean_dec(v___x_1027_);
                    leanh::lean_dec_ref(v_str_1017_);
                    v___x_1032_ = lean_nat_sub(v___x_1031_, v_startInclusive_1018_);
                    leanh::lean_dec(v_startInclusive_1018_);
                    leanh::lean_inc(v___x_1032_);
                    v___x_1033_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1033_, 0, v_it_1013_);
                    leanh::lean_ctor_set(v___x_1033_, 1, v___x_1032_);
                    v___x_1034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1034_, 0, v___x_1032_);
                    leanh::lean_ctor_set(v___x_1034_, 1, v___x_1033_);
                    v___x_1035_ = leanh::lean_apply_4(
                        v_lift_1012_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1023_,
                        v___x_1034_,
                    );
                    return v___x_1035_;
                } else {
                    leanh::lean_dec(v___x_1027_);
                    leanh::lean_dec(v_startInclusive_1018_);
                    leanh::lean_dec_ref(v_str_1017_);
                    v_val_1036_ = leanh::lean_ctor_get(v___x_1030_, 0);
                    leanh::lean_inc(v_val_1036_);
                    leanh::lean_dec_ref_known(v___x_1030_, 1);
                    v___x_1037_ = lean_nat_add(v_it_1013_, v_val_1036_);
                    leanh::lean_dec(v_val_1036_);
                    leanh::lean_inc(v___x_1037_);
                    v___x_1038_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1038_, 0, v_it_1013_);
                    leanh::lean_ctor_set(v___x_1038_, 1, v___x_1037_);
                    v___x_1039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1039_, 0, v___x_1037_);
                    leanh::lean_ctor_set(v___x_1039_, 1, v___x_1038_);
                    v___x_1040_ = leanh::lean_apply_4(
                        v_lift_1012_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1023_,
                        v___x_1039_,
                    );
                    return v___x_1040_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2(
    mut v_s_1045_: *mut leanh::LeanObject,
    mut v_inst_1046_: *mut leanh::LeanObject,
    mut v_lift_1047_: *mut leanh::LeanObject,
    mut v_00_u03b3_1048_: *mut leanh::LeanObject,
    mut v_Pl_1049_: *mut leanh::LeanObject,
    mut v_it_1050_: *mut leanh::LeanObject,
    mut v_init_1051_: *mut leanh::LeanObject,
    mut v___y_1052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1053_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1 as *mut core::ffi::c_void, 8, 4);
    leanh::lean_closure_set(v___f_1053_, 0, v_s_1045_);
    leanh::lean_closure_set(v___f_1053_, 1, v___y_1052_);
    leanh::lean_closure_set(v___f_1053_, 2, v_inst_1046_);
    leanh::lean_closure_set(v___f_1053_, 3, v_lift_1047_);
    v___x_1054_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1053_,
        v_it_1050_,
        v_init_1051_,
        leanh::lean_box(0),
    );
    return v___x_1054_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(
    mut v_s_1055_: *mut leanh::LeanObject,
    mut v_inst_1056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1057_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2 as *mut core::ffi::c_void, 8, 2);
    leanh::lean_closure_set(v___f_1057_, 0, v_s_1055_);
    leanh::lean_closure_set(v___f_1057_, 1, v_inst_1056_);
    return v___f_1057_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(
    mut v_00_u03c1_1058_: *mut leanh::LeanObject,
    mut v_pat_1059_: *mut leanh::LeanObject,
    mut v_s_1060_: *mut leanh::LeanObject,
    mut v_inst_1061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1062_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2 as *mut core::ffi::c_void, 8, 2);
    leanh::lean_closure_set(v___f_1062_, 0, v_s_1060_);
    leanh::lean_closure_set(v___f_1062_, 1, v_inst_1061_);
    return v___f_1062_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(
    mut v_00_u03c1_1063_: *mut leanh::LeanObject,
    mut v_pat_1064_: *mut leanh::LeanObject,
    mut v_s_1065_: *mut leanh::LeanObject,
    mut v_inst_1066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_1063_, v_pat_1064_, v_s_1065_, v_inst_1066_);
    leanh::lean_dec(v_pat_1064_);
    return v_res_1067_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(
    mut v_pat_1068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1069_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1069_, 1, v_pat_1068_);
    return v___x_1069_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(
    mut v_00_u03c1_1070_: *mut leanh::LeanObject,
    mut v_pat_1071_: *mut leanh::LeanObject,
    mut v_inst_1072_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1073_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1073_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1073_, 1, v_pat_1071_);
    return v___x_1073_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(
    mut v_00_u03c1_1074_: *mut leanh::LeanObject,
    mut v_pat_1075_: *mut leanh::LeanObject,
    mut v_inst_1076_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(
        v_00_u03c1_1074_,
        v_pat_1075_,
        v_inst_1076_,
    );
    leanh::lean_dec_ref(v_inst_1076_);
    return v_res_1077_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(
    mut v_lhs_1078_: *mut leanh::LeanObject,
    mut v_rhs_1079_: *mut leanh::LeanObject,
    mut v_lstart_1080_: *mut leanh::LeanObject,
    mut v_rstart_1081_: *mut leanh::LeanObject,
    mut v_len_1082_: *mut leanh::LeanObject,
    mut v_curr_1083_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1084_ = lean_nat_dec_lt(v_curr_1083_, v_len_1082_);
                if v___x_1084_ == 0 {
                    leanh::lean_dec(v_curr_1083_);
                    v___x_1085_ = 1;
                    return v___x_1085_;
                } else {
                    v___x_1086_ = lean_nat_add(v_lstart_1080_, v_curr_1083_);
                    v___x_1087_ = lean_string_get_byte_fast(v_lhs_1078_, v___x_1086_);
                    v___x_1088_ = lean_nat_add(v_rstart_1081_, v_curr_1083_);
                    v___x_1089_ = lean_string_get_byte_fast(v_rhs_1079_, v___x_1088_);
                    v___x_1090_ = lean_uint8_dec_eq(v___x_1087_, v___x_1089_);
                    if v___x_1090_ == 0 {
                        leanh::lean_dec(v_curr_1083_);
                        return v___x_1090_;
                    } else {
                        v___x_1091_ = leanh::lean_unsigned_to_nat(1);
                        v___x_1092_ = lean_nat_add(v_curr_1083_, v___x_1091_);
                        leanh::lean_dec(v_curr_1083_);
                        v_curr_1083_ = v___x_1092_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg___boxed(
    mut v_lhs_1094_: *mut leanh::LeanObject,
    mut v_rhs_1095_: *mut leanh::LeanObject,
    mut v_lstart_1096_: *mut leanh::LeanObject,
    mut v_rstart_1097_: *mut leanh::LeanObject,
    mut v_len_1098_: *mut leanh::LeanObject,
    mut v_curr_1099_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1100_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_1094_, v_rhs_1095_, v_lstart_1096_, v_rstart_1097_, v_len_1098_, v_curr_1099_);
    leanh::lean_dec(v_len_1098_);
    leanh::lean_dec(v_rstart_1097_);
    leanh::lean_dec(v_lstart_1096_);
    leanh::lean_dec_ref(v_rhs_1095_);
    leanh::lean_dec_ref(v_lhs_1094_);
    v_r_1101_ = leanh::lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(
    mut v_lhs_1102_: *mut leanh::LeanObject,
    mut v_rhs_1103_: *mut leanh::LeanObject,
    mut v_lstart_1104_: *mut leanh::LeanObject,
    mut v_rstart_1105_: *mut leanh::LeanObject,
    mut v_len_1106_: *mut leanh::LeanObject,
    mut v_h1_1107_: *mut leanh::LeanObject,
    mut v_h2_1108_: *mut leanh::LeanObject,
    mut v_curr_1109_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_1110_: u8 = 0;
    v___x_1110_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_1102_, v_rhs_1103_, v_lstart_1104_, v_rstart_1105_, v_len_1106_, v_curr_1109_);
    return v___x_1110_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(
    mut v_lhs_1111_: *mut leanh::LeanObject,
    mut v_rhs_1112_: *mut leanh::LeanObject,
    mut v_lstart_1113_: *mut leanh::LeanObject,
    mut v_rstart_1114_: *mut leanh::LeanObject,
    mut v_len_1115_: *mut leanh::LeanObject,
    mut v_h1_1116_: *mut leanh::LeanObject,
    mut v_h2_1117_: *mut leanh::LeanObject,
    mut v_curr_1118_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1119_: u8 = 0;
    let mut v_r_1120_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1119_ =
        l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(
            v_lhs_1111_,
            v_rhs_1112_,
            v_lstart_1113_,
            v_rstart_1114_,
            v_len_1115_,
            v_h1_1116_,
            v_h2_1117_,
            v_curr_1118_,
        );
    leanh::lean_dec(v_len_1115_);
    leanh::lean_dec(v_rstart_1114_);
    leanh::lean_dec(v_lstart_1113_);
    leanh::lean_dec_ref(v_rhs_1112_);
    leanh::lean_dec_ref(v_lhs_1111_);
    v_r_1120_ = leanh::lean_box((v_res_1119_) as usize);
    return v_r_1120_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpStr___boxed(
    mut v_lhs_1128_: *mut leanh::LeanObject,
    mut v_rhs_1129_: *mut leanh::LeanObject,
    mut v_lstart_1130_: *mut leanh::LeanObject,
    mut v_rstart_1131_: *mut leanh::LeanObject,
    mut v_len_1132_: *mut leanh::LeanObject,
    mut v_h1_1133_: *mut leanh::LeanObject,
    mut v_h2_1134_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1135_: u8 = 0;
    let mut v_r_1136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = lean_string_memcmp(
        v_lhs_1128_,
        v_rhs_1129_,
        v_lstart_1130_,
        v_rstart_1131_,
        v_len_1132_,
    );
    leanh::lean_dec(v_len_1132_);
    leanh::lean_dec(v_rstart_1131_);
    leanh::lean_dec(v_lstart_1130_);
    leanh::lean_dec_ref(v_rhs_1129_);
    leanh::lean_dec_ref(v_lhs_1128_);
    v_r_1136_ = leanh::lean_box((v_res_1135_) as usize);
    return v_r_1136_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___redArg(
    mut v_lhs_1137_: *mut leanh::LeanObject,
    mut v_rhs_1138_: *mut leanh::LeanObject,
    mut v_lstart_1139_: *mut leanh::LeanObject,
    mut v_rstart_1140_: *mut leanh::LeanObject,
    mut v_len_1141_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_1142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    v_str_1142_ = leanh::lean_ctor_get(v_lhs_1137_, 0);
    v_startInclusive_1143_ = leanh::lean_ctor_get(v_lhs_1137_, 1);
    v_str_1144_ = leanh::lean_ctor_get(v_rhs_1138_, 0);
    v_startInclusive_1145_ = leanh::lean_ctor_get(v_rhs_1138_, 1);
    v___x_1146_ = lean_nat_add(v_startInclusive_1143_, v_lstart_1139_);
    v___x_1147_ = lean_nat_add(v_startInclusive_1145_, v_rstart_1140_);
    v___x_1148_ = lean_string_memcmp(
        v_str_1142_,
        v_str_1144_,
        v___x_1146_,
        v___x_1147_,
        v_len_1141_,
    );
    leanh::lean_dec(v___x_1147_);
    leanh::lean_dec(v___x_1146_);
    return v___x_1148_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(
    mut v_lhs_1149_: *mut leanh::LeanObject,
    mut v_rhs_1150_: *mut leanh::LeanObject,
    mut v_lstart_1151_: *mut leanh::LeanObject,
    mut v_rstart_1152_: *mut leanh::LeanObject,
    mut v_len_1153_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1154_: u8 = 0;
    let mut v_r_1155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(
        v_lhs_1149_,
        v_rhs_1150_,
        v_lstart_1151_,
        v_rstart_1152_,
        v_len_1153_,
    );
    leanh::lean_dec(v_len_1153_);
    leanh::lean_dec(v_rstart_1152_);
    leanh::lean_dec(v_lstart_1151_);
    leanh::lean_dec_ref(v_rhs_1150_);
    leanh::lean_dec_ref(v_lhs_1149_);
    v_r_1155_ = leanh::lean_box((v_res_1154_) as usize);
    return v_r_1155_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice(
    mut v_lhs_1156_: *mut leanh::LeanObject,
    mut v_rhs_1157_: *mut leanh::LeanObject,
    mut v_lstart_1158_: *mut leanh::LeanObject,
    mut v_rstart_1159_: *mut leanh::LeanObject,
    mut v_len_1160_: *mut leanh::LeanObject,
    mut v_h1_1161_: *mut leanh::LeanObject,
    mut v_h2_1162_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_str_1163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    v_str_1163_ = leanh::lean_ctor_get(v_lhs_1156_, 0);
    v_startInclusive_1164_ = leanh::lean_ctor_get(v_lhs_1156_, 1);
    v_str_1165_ = leanh::lean_ctor_get(v_rhs_1157_, 0);
    v_startInclusive_1166_ = leanh::lean_ctor_get(v_rhs_1157_, 1);
    v___x_1167_ = lean_nat_add(v_startInclusive_1164_, v_lstart_1158_);
    v___x_1168_ = lean_nat_add(v_startInclusive_1166_, v_rstart_1159_);
    v___x_1169_ = lean_string_memcmp(
        v_str_1163_,
        v_str_1165_,
        v___x_1167_,
        v___x_1168_,
        v_len_1160_,
    );
    leanh::lean_dec(v___x_1168_);
    leanh::lean_dec(v___x_1167_);
    return v___x_1169_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___boxed(
    mut v_lhs_1170_: *mut leanh::LeanObject,
    mut v_rhs_1171_: *mut leanh::LeanObject,
    mut v_lstart_1172_: *mut leanh::LeanObject,
    mut v_rstart_1173_: *mut leanh::LeanObject,
    mut v_len_1174_: *mut leanh::LeanObject,
    mut v_h1_1175_: *mut leanh::LeanObject,
    mut v_h2_1176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1177_: u8 = 0;
    let mut v_r_1178_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_String_Slice_Pattern_Internal_memcmpSlice(
        v_lhs_1170_,
        v_rhs_1171_,
        v_lstart_1172_,
        v_rstart_1173_,
        v_len_1174_,
        v_h1_1175_,
        v_h2_1176_,
    );
    leanh::lean_dec(v_len_1174_);
    leanh::lean_dec(v_rstart_1173_);
    leanh::lean_dec(v_lstart_1172_);
    leanh::lean_dec_ref(v_rhs_1171_);
    leanh::lean_dec_ref(v_lhs_1170_);
    v_r_1178_ = leanh::lean_box((v_res_1177_) as usize);
    return v_r_1178_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(
    mut v_00_u03c1_1179_: *mut leanh::LeanObject,
    mut v_pat_1180_: *mut leanh::LeanObject,
    mut v_s_1181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1182_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1182_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(
    mut v_00_u03c1_1183_: *mut leanh::LeanObject,
    mut v_pat_1184_: *mut leanh::LeanObject,
    mut v_s_1185_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1186_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(
            v_00_u03c1_1183_,
            v_pat_1184_,
            v_s_1185_,
        );
    leanh::lean_dec_ref(v_s_1185_);
    leanh::lean_dec(v_pat_1184_);
    return v_res_1186_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(
    mut v_a_1187_: *mut leanh::LeanObject,
    mut v_a_1188_: *mut leanh::LeanObject,
    mut v_a_1189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = leanh::lean_unsigned_to_nat(0);
    return v___x_1190_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(
    mut v_a_1191_: *mut leanh::LeanObject,
    mut v_a_1192_: *mut leanh::LeanObject,
    mut v_a_1193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(
        v_a_1191_, v_a_1192_, v_a_1193_,
    );
    leanh::lean_dec_ref(v_a_1193_);
    leanh::lean_dec(v_a_1192_);
    return v_res_1194_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(
    mut v_s_1195_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1196_ = leanh::lean_ctor_get(v_s_1195_, 1);
    v_endExclusive_1197_ = leanh::lean_ctor_get(v_s_1195_, 2);
    v___x_1198_ = lean_nat_sub(v_endExclusive_1197_, v_startInclusive_1196_);
    return v___x_1198_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(
    mut v_s_1199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1200_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ =
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_1199_);
    leanh::lean_dec_ref(v_s_1199_);
    return v_res_1200_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(
    mut v_00_u03c1_1201_: *mut leanh::LeanObject,
    mut v_pat_1202_: *mut leanh::LeanObject,
    mut v_s_1203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_startInclusive_1204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1204_ = leanh::lean_ctor_get(v_s_1203_, 1);
    v_endExclusive_1205_ = leanh::lean_ctor_get(v_s_1203_, 2);
    v___x_1206_ = lean_nat_sub(v_endExclusive_1205_, v_startInclusive_1204_);
    return v___x_1206_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(
    mut v_00_u03c1_1207_: *mut leanh::LeanObject,
    mut v_pat_1208_: *mut leanh::LeanObject,
    mut v_s_1209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1210_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(
        v_00_u03c1_1207_,
        v_pat_1208_,
        v_s_1209_,
    );
    leanh::lean_dec_ref(v_s_1209_);
    leanh::lean_dec(v_pat_1208_);
    return v_res_1210_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(
    mut v_inst_1211_: *mut leanh::LeanObject,
    mut v_s_1212_: *mut leanh::LeanObject,
    mut v_it_1213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v_skipSuffixOfNonempty_x3f_1216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v_str_1220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1221_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_unused_1236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1214_ = leanh::lean_unsigned_to_nat(0);
                v___x_1215_ = lean_nat_dec_eq(v_it_1213_, v___x_1214_);
                if v___x_1215_ == 0 {
                    v_skipSuffixOfNonempty_x3f_1216_ = leanh::lean_ctor_get(v_inst_1211_, 1);
                    v_isSharedCheck_1235_ = (!leanh::lean_is_exclusive(v_inst_1211_)) as u8;
                    if v_isSharedCheck_1235_ == 0 {
                        v_unused_1236_ = leanh::lean_ctor_get(v_inst_1211_, 2);
                        leanh::lean_dec(v_unused_1236_);
                        v_unused_1237_ = leanh::lean_ctor_get(v_inst_1211_, 0);
                        leanh::lean_dec(v_unused_1237_);
                        v___x_1218_ = v_inst_1211_;
                        v_isShared_1219_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_skipSuffixOfNonempty_x3f_1216_);
                        leanh::lean_dec(v_inst_1211_);
                        v___x_1218_ = leanh::lean_box(0);
                        v_isShared_1219_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_it_1213_);
                    leanh::lean_dec_ref(v_inst_1211_);
                    v___x_1238_ = leanh::lean_box(2);
                    return v___x_1238_;
                }
            }
            1 => {
                v_str_1220_ = leanh::lean_ctor_get(v_s_1212_, 0);
                v_startInclusive_1221_ = leanh::lean_ctor_get(v_s_1212_, 1);
                v___x_1222_ = lean_nat_add(v_startInclusive_1221_, v_it_1213_);
                leanh::lean_inc(v_startInclusive_1221_);
                leanh::lean_inc_ref(v_str_1220_);
                if v_isShared_1219_ == 0 {
                    leanh::lean_ctor_set(v___x_1218_, 2, v___x_1222_);
                    leanh::lean_ctor_set(v___x_1218_, 1, v_startInclusive_1221_);
                    leanh::lean_ctor_set(v___x_1218_, 0, v_str_1220_);
                    v___x_1224_ = v___x_1218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_str_1220_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_startInclusive_1221_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 2, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1225_ = leanh::lean_apply_2(
                    v_skipSuffixOfNonempty_x3f_1216_,
                    v___x_1224_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1225_) == 0 {
                    v___x_1226_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1227_ = lean_nat_sub(v_it_1213_, v___x_1226_);
                    v___x_1228_ = l_String_Slice_posLE(v_s_1212_, v___x_1227_);
                    leanh::lean_inc(v___x_1228_);
                    v___x_1229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1229_, 0, v___x_1228_);
                    leanh::lean_ctor_set(v___x_1229_, 1, v_it_1213_);
                    v___x_1230_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1230_, 0, v___x_1228_);
                    leanh::lean_ctor_set(v___x_1230_, 1, v___x_1229_);
                    return v___x_1230_;
                } else {
                    v_val_1231_ = leanh::lean_ctor_get(v___x_1225_, 0);
                    leanh::lean_inc_n(v_val_1231_, 2);
                    leanh::lean_dec_ref_known(v___x_1225_, 1);
                    v___x_1232_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1232_, 0, v_val_1231_);
                    leanh::lean_ctor_set(v___x_1232_, 1, v_it_1213_);
                    v___x_1233_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1233_, 0, v_val_1231_);
                    leanh::lean_ctor_set(v___x_1233_, 1, v___x_1232_);
                    return v___x_1233_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(
    mut v_inst_1239_: *mut leanh::LeanObject,
    mut v_s_1240_: *mut leanh::LeanObject,
    mut v_it_1241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_1239_, v_s_1240_, v_it_1241_);
    leanh::lean_dec_ref(v_s_1240_);
    return v_res_1242_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(
    mut v_s_1243_: *mut leanh::LeanObject,
    mut v_inst_1244_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1245_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1245_, 0, v_inst_1244_);
    leanh::lean_closure_set(v___f_1245_, 1, v_s_1243_);
    return v___f_1245_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(
    mut v_00_u03c1_1246_: *mut leanh::LeanObject,
    mut v_pat_1247_: *mut leanh::LeanObject,
    mut v_s_1248_: *mut leanh::LeanObject,
    mut v_inst_1249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1250_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1250_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    leanh::lean_closure_set(v___f_1250_, 0, v_inst_1249_);
    leanh::lean_closure_set(v___f_1250_, 1, v_s_1248_);
    return v___f_1250_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(
    mut v_00_u03c1_1251_: *mut leanh::LeanObject,
    mut v_pat_1252_: *mut leanh::LeanObject,
    mut v_s_1253_: *mut leanh::LeanObject,
    mut v_inst_1254_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_1251_, v_pat_1252_, v_s_1253_, v_inst_1254_);
    leanh::lean_dec(v_pat_1252_);
    return v_res_1255_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(
    mut v_00_u03c1_1256_: *mut leanh::LeanObject,
    mut v_pat_1257_: *mut leanh::LeanObject,
    mut v_s_1258_: *mut leanh::LeanObject,
    mut v_inst_1259_: *mut leanh::LeanObject,
    mut v_inst_1260_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1261_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = leanh::lean_box(0);
    return v___x_1261_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(
    mut v_00_u03c1_1262_: *mut leanh::LeanObject,
    mut v_pat_1263_: *mut leanh::LeanObject,
    mut v_s_1264_: *mut leanh::LeanObject,
    mut v_inst_1265_: *mut leanh::LeanObject,
    mut v_inst_1266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1267_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_1262_, v_pat_1263_, v_s_1264_, v_inst_1265_, v_inst_1266_);
    leanh::lean_dec_ref(v_inst_1265_);
    leanh::lean_dec_ref(v_s_1264_);
    leanh::lean_dec(v_pat_1263_);
    return v_res_1267_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(
    mut v___y_1268_: *mut leanh::LeanObject,
    mut v_inst_1269_: *mut leanh::LeanObject,
    mut v_s_1270_: *mut leanh::LeanObject,
    mut v_lift_1271_: *mut leanh::LeanObject,
    mut v_it_1272_: *mut leanh::LeanObject,
    mut v_acc_1273_: *mut leanh::LeanObject,
    mut v_hP_1274_: *mut leanh::LeanObject,
    mut v_recur_1275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut v_skipSuffixOfNonempty_x3f_1279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v_str_1283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut v_unused_1301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1276_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                leanh::lean_closure_set(v___f_1276_, 0, v___y_1268_);
                leanh::lean_closure_set(v___f_1276_, 1, v_acc_1273_);
                leanh::lean_closure_set(v___f_1276_, 2, v_recur_1275_);
                v___x_1277_ = leanh::lean_unsigned_to_nat(0);
                v___x_1278_ = lean_nat_dec_eq(v_it_1272_, v___x_1277_);
                if v___x_1278_ == 0 {
                    v_skipSuffixOfNonempty_x3f_1279_ = leanh::lean_ctor_get(v_inst_1269_, 1);
                    v_isSharedCheck_1300_ = (!leanh::lean_is_exclusive(v_inst_1269_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v_unused_1301_ = leanh::lean_ctor_get(v_inst_1269_, 2);
                        leanh::lean_dec(v_unused_1301_);
                        v_unused_1302_ = leanh::lean_ctor_get(v_inst_1269_, 0);
                        leanh::lean_dec(v_unused_1302_);
                        v___x_1281_ = v_inst_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_skipSuffixOfNonempty_x3f_1279_);
                        leanh::lean_dec(v_inst_1269_);
                        v___x_1281_ = leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1300_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_it_1272_);
                    leanh::lean_dec_ref(v_inst_1269_);
                    v___x_1303_ = leanh::lean_box(2);
                    v___x_1304_ = leanh::lean_apply_4(
                        v_lift_1271_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1276_,
                        v___x_1303_,
                    );
                    return v___x_1304_;
                }
            }
            1 => {
                v_str_1283_ = leanh::lean_ctor_get(v_s_1270_, 0);
                v_startInclusive_1284_ = leanh::lean_ctor_get(v_s_1270_, 1);
                v___x_1285_ = lean_nat_add(v_startInclusive_1284_, v_it_1272_);
                leanh::lean_inc(v_startInclusive_1284_);
                leanh::lean_inc_ref(v_str_1283_);
                if v_isShared_1282_ == 0 {
                    leanh::lean_ctor_set(v___x_1281_, 2, v___x_1285_);
                    leanh::lean_ctor_set(v___x_1281_, 1, v_startInclusive_1284_);
                    leanh::lean_ctor_set(v___x_1281_, 0, v_str_1283_);
                    v___x_1287_ = v___x_1281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_str_1283_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_startInclusive_1284_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___x_1285_);
                    v___x_1287_ = v_reuseFailAlloc_1299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1288_ = leanh::lean_apply_2(
                    v_skipSuffixOfNonempty_x3f_1279_,
                    v___x_1287_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_1288_) == 0 {
                    v___x_1289_ = leanh::lean_unsigned_to_nat(1);
                    v___x_1290_ = lean_nat_sub(v_it_1272_, v___x_1289_);
                    v___x_1291_ = l_String_Slice_posLE(v_s_1270_, v___x_1290_);
                    leanh::lean_inc(v___x_1291_);
                    v___x_1292_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1292_, 0, v___x_1291_);
                    leanh::lean_ctor_set(v___x_1292_, 1, v_it_1272_);
                    v___x_1293_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1293_, 0, v___x_1291_);
                    leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
                    v___x_1294_ = leanh::lean_apply_4(
                        v_lift_1271_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1276_,
                        v___x_1293_,
                    );
                    return v___x_1294_;
                } else {
                    v_val_1295_ = leanh::lean_ctor_get(v___x_1288_, 0);
                    leanh::lean_inc_n(v_val_1295_, 2);
                    leanh::lean_dec_ref_known(v___x_1288_, 1);
                    v___x_1296_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1296_, 0, v_val_1295_);
                    leanh::lean_ctor_set(v___x_1296_, 1, v_it_1272_);
                    v___x_1297_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_1297_, 0, v_val_1295_);
                    leanh::lean_ctor_set(v___x_1297_, 1, v___x_1296_);
                    v___x_1298_ = leanh::lean_apply_4(
                        v_lift_1271_,
                        leanh::lean_box(0),
                        leanh::lean_box(0),
                        v___f_1276_,
                        v___x_1297_,
                    );
                    return v___x_1298_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed(
    mut v___y_1305_: *mut leanh::LeanObject,
    mut v_inst_1306_: *mut leanh::LeanObject,
    mut v_s_1307_: *mut leanh::LeanObject,
    mut v_lift_1308_: *mut leanh::LeanObject,
    mut v_it_1309_: *mut leanh::LeanObject,
    mut v_acc_1310_: *mut leanh::LeanObject,
    mut v_hP_1311_: *mut leanh::LeanObject,
    mut v_recur_1312_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1313_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_1305_, v_inst_1306_, v_s_1307_, v_lift_1308_, v_it_1309_, v_acc_1310_, v_hP_1311_, v_recur_1312_);
    leanh::lean_dec_ref(v_s_1307_);
    return v_res_1313_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(
    mut v_inst_1314_: *mut leanh::LeanObject,
    mut v_s_1315_: *mut leanh::LeanObject,
    mut v_lift_1316_: *mut leanh::LeanObject,
    mut v_00_u03b3_1317_: *mut leanh::LeanObject,
    mut v_Pl_1318_: *mut leanh::LeanObject,
    mut v_it_1319_: *mut leanh::LeanObject,
    mut v_init_1320_: *mut leanh::LeanObject,
    mut v___y_1321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1322_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
    leanh::lean_closure_set(v___f_1322_, 0, v___y_1321_);
    leanh::lean_closure_set(v___f_1322_, 1, v_inst_1314_);
    leanh::lean_closure_set(v___f_1322_, 2, v_s_1315_);
    leanh::lean_closure_set(v___f_1322_, 3, v_lift_1316_);
    v___x_1323_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1322_,
        v_it_1319_,
        v_init_1320_,
        leanh::lean_box(0),
    );
    return v___x_1323_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(
    mut v_s_1324_: *mut leanh::LeanObject,
    mut v_inst_1325_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1326_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1326_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 8, 2);
    leanh::lean_closure_set(v___f_1326_, 0, v_inst_1325_);
    leanh::lean_closure_set(v___f_1326_, 1, v_s_1324_);
    return v___f_1326_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(
    mut v_00_u03c1_1327_: *mut leanh::LeanObject,
    mut v_pat_1328_: *mut leanh::LeanObject,
    mut v_s_1329_: *mut leanh::LeanObject,
    mut v_inst_1330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_1331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1331_ = leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 8, 2);
    leanh::lean_closure_set(v___f_1331_, 0, v_inst_1330_);
    leanh::lean_closure_set(v___f_1331_, 1, v_s_1329_);
    return v___f_1331_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(
    mut v_00_u03c1_1332_: *mut leanh::LeanObject,
    mut v_pat_1333_: *mut leanh::LeanObject,
    mut v_s_1334_: *mut leanh::LeanObject,
    mut v_inst_1335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_1332_, v_pat_1333_, v_s_1334_, v_inst_1335_);
    leanh::lean_dec(v_pat_1333_);
    return v_res_1336_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(
    mut v_pat_1337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1338_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1338_, 1, v_pat_1337_);
    return v___x_1338_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(
    mut v_00_u03c1_1339_: *mut leanh::LeanObject,
    mut v_pat_1340_: *mut leanh::LeanObject,
    mut v_inst_1341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1342_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___x_1342_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_1342_, 1, v_pat_1340_);
    return v___x_1342_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(
    mut v_00_u03c1_1343_: *mut leanh::LeanObject,
    mut v_pat_1344_: *mut leanh::LeanObject,
    mut v_inst_1345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(
        v_00_u03c1_1343_,
        v_pat_1344_,
        v_inst_1345_,
    );
    leanh::lean_dec_ref(v_inst_1345_);
    return v_res_1346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_Basic(
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
pub unsafe fn initialize_Init_Data_String_Pattern_Basic(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_Basic(builtin);
}
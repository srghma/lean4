// Lean compiler output
// Module: Init.Data.String.Pattern.Basic
// Imports: Init.Data.Iterators.Consumers.Monadic.Loop Init.Data.String.Defs Init.Data.String.Basic Init.Data.String.FindPos Init.Data.String.Lemmas.FindPos Init.Data.Iterators.Consumers.Loop Init.Omega Init.Data.String.Lemmas.IsEmpty Init.Data.String.Termination Init.Data.String.OrderInstances Init.Data.String.Lemmas.Order
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
use crate::ffi::lean_string_utf8_next_fast;
use crate::ffi::lean_string_memcmp;
use crate::ffi::lean_string_get_byte_fast;
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_uint8_dec_eq,
};
pub static l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value:
    crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(
    mut v_x_674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_674_) == 0 {
        let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_675_ = crate::leanh::lean_unsigned_to_nat(0);
        return v___x_675_;
    } else {
        let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_676_ = crate::leanh::lean_unsigned_to_nat(1);
        return v___x_676_;
    }
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___redArg___boxed(
    mut v_x_677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_678_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_677_);
    crate::leanh::lean_dec_ref(v_x_677_);
    return v_res_678_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx(
    mut v_s_679_: *mut crate::leanh::LeanObject,
    mut v_x_680_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_681_ = l_String_Slice_Pattern_SearchStep_ctorIdx___redArg(v_x_680_);
    return v___x_681_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorIdx___boxed(
    mut v_s_682_: *mut crate::leanh::LeanObject,
    mut v_x_683_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_684_ = l_String_Slice_Pattern_SearchStep_ctorIdx(v_s_682_, v_x_683_);
    crate::leanh::lean_dec_ref(v_x_683_);
    crate::leanh::lean_dec_ref(v_s_682_);
    return v_res_684_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim___redArg(
    mut v_t_685_: *mut crate::leanh::LeanObject,
    mut v_k_686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startPos_687_ = crate::leanh::lean_ctor_get(v_t_685_, 0);
    crate::leanh::lean_inc(v_startPos_687_);
    v_endPos_688_ = crate::leanh::lean_ctor_get(v_t_685_, 1);
    crate::leanh::lean_inc(v_endPos_688_);
    crate::leanh::lean_dec_ref(v_t_685_);
    v___x_689_ = crate::leanh::lean_apply_2(v_k_686_, v_startPos_687_, v_endPos_688_);
    return v___x_689_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim(
    mut v_s_690_: *mut crate::leanh::LeanObject,
    mut v_motive_691_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_692_: *mut crate::leanh::LeanObject,
    mut v_t_693_: *mut crate::leanh::LeanObject,
    mut v_h_694_: *mut crate::leanh::LeanObject,
    mut v_k_695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_696_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_693_, v_k_695_);
    return v___x_696_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ctorElim___boxed(
    mut v_s_697_: *mut crate::leanh::LeanObject,
    mut v_motive_698_: *mut crate::leanh::LeanObject,
    mut v_ctorIdx_699_: *mut crate::leanh::LeanObject,
    mut v_t_700_: *mut crate::leanh::LeanObject,
    mut v_h_701_: *mut crate::leanh::LeanObject,
    mut v_k_702_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_703_ = l_String_Slice_Pattern_SearchStep_ctorElim(
        v_s_697_,
        v_motive_698_,
        v_ctorIdx_699_,
        v_t_700_,
        v_h_701_,
        v_k_702_,
    );
    crate::leanh::lean_dec(v_ctorIdx_699_);
    crate::leanh::lean_dec_ref(v_s_697_);
    return v_res_703_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim___redArg(
    mut v_t_704_: *mut crate::leanh::LeanObject,
    mut v_rejected_705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_706_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_704_, v_rejected_705_);
    return v___x_706_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim(
    mut v_s_707_: *mut crate::leanh::LeanObject,
    mut v_motive_708_: *mut crate::leanh::LeanObject,
    mut v_t_709_: *mut crate::leanh::LeanObject,
    mut v_h_710_: *mut crate::leanh::LeanObject,
    mut v_rejected_711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_712_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_709_, v_rejected_711_);
    return v___x_712_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_rejected_elim___boxed(
    mut v_s_713_: *mut crate::leanh::LeanObject,
    mut v_motive_714_: *mut crate::leanh::LeanObject,
    mut v_t_715_: *mut crate::leanh::LeanObject,
    mut v_h_716_: *mut crate::leanh::LeanObject,
    mut v_rejected_717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_718_ = l_String_Slice_Pattern_SearchStep_rejected_elim(
        v_s_713_,
        v_motive_714_,
        v_t_715_,
        v_h_716_,
        v_rejected_717_,
    );
    crate::leanh::lean_dec_ref(v_s_713_);
    return v_res_718_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim___redArg(
    mut v_t_719_: *mut crate::leanh::LeanObject,
    mut v_matched_720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_721_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_719_, v_matched_720_);
    return v___x_721_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim(
    mut v_s_722_: *mut crate::leanh::LeanObject,
    mut v_motive_723_: *mut crate::leanh::LeanObject,
    mut v_t_724_: *mut crate::leanh::LeanObject,
    mut v_h_725_: *mut crate::leanh::LeanObject,
    mut v_matched_726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_727_ = l_String_Slice_Pattern_SearchStep_ctorElim___redArg(v_t_724_, v_matched_726_);
    return v___x_727_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_matched_elim___boxed(
    mut v_s_728_: *mut crate::leanh::LeanObject,
    mut v_motive_729_: *mut crate::leanh::LeanObject,
    mut v_t_730_: *mut crate::leanh::LeanObject,
    mut v_h_731_: *mut crate::leanh::LeanObject,
    mut v_matched_732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_733_ = l_String_Slice_Pattern_SearchStep_matched_elim(
        v_s_728_,
        v_motive_729_,
        v_t_730_,
        v_h_731_,
        v_matched_732_,
    );
    crate::leanh::lean_dec_ref(v_s_728_);
    return v_res_733_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep_default(
    mut v_s_736_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_737_ = l_String_Slice_Pattern_instInhabitedSearchStep_default___closed__0;
    return v___x_737_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep_default___boxed(
    mut v_s_738_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_739_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_s_738_);
    crate::leanh::lean_dec_ref(v_s_738_);
    return v_res_739_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep(
    mut v_a_740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_741_ = l_String_Slice_Pattern_instInhabitedSearchStep_default(v_a_740_);
    return v___x_741_;
}
pub unsafe fn l_String_Slice_Pattern_instInhabitedSearchStep___boxed(
    mut v_a_742_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_743_ = l_String_Slice_Pattern_instInhabitedSearchStep(v_a_742_);
    crate::leanh::lean_dec_ref(v_a_742_);
    return v_res_743_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(
    mut v_x_744_: *mut crate::leanh::LeanObject,
    mut v_x_745_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_a_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_b_750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_751_: u8 = 0;
    let mut v___x_752_: u8 = 0;
    let mut v_startPos_753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_757_: u8 = 0;
    let mut v_startPos_758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startPos_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_762_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_744_) == 0 {
                    if crate::leanh::lean_obj_tag(v_x_745_) == 0 {
                        v_startPos_753_ = crate::leanh::lean_ctor_get(v_x_744_, 0);
                        v_endPos_754_ = crate::leanh::lean_ctor_get(v_x_744_, 1);
                        v_startPos_755_ = crate::leanh::lean_ctor_get(v_x_745_, 0);
                        v_endPos_756_ = crate::leanh::lean_ctor_get(v_x_745_, 1);
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
                    if crate::leanh::lean_obj_tag(v_x_745_) == 1 {
                        v_startPos_758_ = crate::leanh::lean_ctor_get(v_x_744_, 0);
                        v_endPos_759_ = crate::leanh::lean_ctor_get(v_x_744_, 1);
                        v_startPos_760_ = crate::leanh::lean_ctor_get(v_x_745_, 0);
                        v_endPos_761_ = crate::leanh::lean_ctor_get(v_x_745_, 1);
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
    mut v_x_763_: *mut crate::leanh::LeanObject,
    mut v_x_764_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_765_: u8 = 0;
    let mut v_r_766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_765_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_763_, v_x_764_);
    crate::leanh::lean_dec_ref(v_x_764_);
    crate::leanh::lean_dec_ref(v_x_763_);
    v_r_766_ = crate::leanh::lean_box((v_res_765_) as usize);
    return v_r_766_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq(
    mut v_s_767_: *mut crate::leanh::LeanObject,
    mut v_x_768_: *mut crate::leanh::LeanObject,
    mut v_x_769_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_770_: u8 = 0;
    v___x_770_ = l_String_Slice_Pattern_instBEqSearchStep_beq___redArg(v_x_768_, v_x_769_);
    return v___x_770_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep_beq___boxed(
    mut v_s_771_: *mut crate::leanh::LeanObject,
    mut v_x_772_: *mut crate::leanh::LeanObject,
    mut v_x_773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_774_: u8 = 0;
    let mut v_r_775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_774_ = l_String_Slice_Pattern_instBEqSearchStep_beq(v_s_771_, v_x_772_, v_x_773_);
    crate::leanh::lean_dec_ref(v_x_773_);
    crate::leanh::lean_dec_ref(v_x_772_);
    crate::leanh::lean_dec_ref(v_s_771_);
    v_r_775_ = crate::leanh::lean_box((v_res_774_) as usize);
    return v_r_775_;
}
pub unsafe fn l_String_Slice_Pattern_instBEqSearchStep(
    mut v_s_776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_777_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_instBEqSearchStep_beq___boxed as *mut core::ffi::c_void,
        3,
        1,
    );
    crate::leanh::lean_closure_set(v___x_777_, 0, v_s_776_);
    return v___x_777_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___redArg(
    mut v_st_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startPos_779_ = crate::leanh::lean_ctor_get(v_st_778_, 0);
    crate::leanh::lean_inc(v_startPos_779_);
    return v_startPos_779_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___redArg___boxed(
    mut v_st_780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_781_ = l_String_Slice_Pattern_SearchStep_startPos___redArg(v_st_780_);
    crate::leanh::lean_dec_ref(v_st_780_);
    return v_res_781_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos(
    mut v_s_782_: *mut crate::leanh::LeanObject,
    mut v_st_783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startPos_784_ = crate::leanh::lean_ctor_get(v_st_783_, 0);
    crate::leanh::lean_inc(v_startPos_784_);
    return v_startPos_784_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_startPos___boxed(
    mut v_s_785_: *mut crate::leanh::LeanObject,
    mut v_st_786_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_787_ = l_String_Slice_Pattern_SearchStep_startPos(v_s_785_, v_st_786_);
    crate::leanh::lean_dec_ref(v_st_786_);
    crate::leanh::lean_dec_ref(v_s_785_);
    return v_res_787_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___redArg(
    mut v_st_788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_endPos_789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_endPos_789_ = crate::leanh::lean_ctor_get(v_st_788_, 1);
    crate::leanh::lean_inc(v_endPos_789_);
    return v_endPos_789_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___redArg___boxed(
    mut v_st_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_String_Slice_Pattern_SearchStep_endPos___redArg(v_st_790_);
    crate::leanh::lean_dec_ref(v_st_790_);
    return v_res_791_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos(
    mut v_s_792_: *mut crate::leanh::LeanObject,
    mut v_st_793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_endPos_794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_endPos_794_ = crate::leanh::lean_ctor_get(v_st_793_, 1);
    crate::leanh::lean_inc(v_endPos_794_);
    return v_endPos_794_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_endPos___boxed(
    mut v_s_795_: *mut crate::leanh::LeanObject,
    mut v_st_796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_797_ = l_String_Slice_Pattern_SearchStep_endPos(v_s_795_, v_st_796_);
    crate::leanh::lean_dec_ref(v_st_796_);
    crate::leanh::lean_dec_ref(v_s_795_);
    return v_res_797_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(
    mut v_p_798_: *mut crate::leanh::LeanObject,
    mut v_st_799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_804_: u8 = 0;
    let mut v___x_805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_810_: u8 = 0;
    let mut v_startPos_811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_815_: u8 = 0;
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_821_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_st_799_) == 0 {
                    v_startPos_800_ = crate::leanh::lean_ctor_get(v_st_799_, 0);
                    v_endPos_801_ = crate::leanh::lean_ctor_get(v_st_799_, 1);
                    v_isSharedCheck_810_ = (!crate::leanh::lean_is_exclusive(v_st_799_)) as u8;
                    if v_isSharedCheck_810_ == 0 {
                        v___x_803_ = v_st_799_;
                        v_isShared_804_ = v_isSharedCheck_810_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_801_);
                        crate::leanh::lean_inc(v_startPos_800_);
                        crate::leanh::lean_dec(v_st_799_);
                        v___x_803_ = crate::leanh::lean_box(0);
                        v_isShared_804_ = v_isSharedCheck_810_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_811_ = crate::leanh::lean_ctor_get(v_st_799_, 0);
                    v_endPos_812_ = crate::leanh::lean_ctor_get(v_st_799_, 1);
                    v_isSharedCheck_821_ = (!crate::leanh::lean_is_exclusive(v_st_799_)) as u8;
                    if v_isSharedCheck_821_ == 0 {
                        v___x_814_ = v_st_799_;
                        v_isShared_815_ = v_isSharedCheck_821_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_812_);
                        crate::leanh::lean_inc(v_startPos_811_);
                        crate::leanh::lean_dec(v_st_799_);
                        v___x_814_ = crate::leanh::lean_box(0);
                        v_isShared_815_ = v_isSharedCheck_821_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_805_ = lean_nat_add(v_p_798_, v_startPos_800_);
                crate::leanh::lean_dec(v_startPos_800_);
                v___x_806_ = lean_nat_add(v_p_798_, v_endPos_801_);
                crate::leanh::lean_dec(v_endPos_801_);
                if v_isShared_804_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_803_, 1, v___x_806_);
                    crate::leanh::lean_ctor_set(v___x_803_, 0, v___x_805_);
                    v___x_808_ = v___x_803_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_805_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_809_, 1, v___x_806_);
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
                crate::leanh::lean_dec(v_startPos_811_);
                v___x_817_ = lean_nat_add(v_p_798_, v_endPos_812_);
                crate::leanh::lean_dec(v_endPos_812_);
                if v_isShared_815_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_814_, 1, v___x_817_);
                    crate::leanh::lean_ctor_set(v___x_814_, 0, v___x_816_);
                    v___x_819_ = v___x_814_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_820_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_816_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_820_, 1, v___x_817_);
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
    mut v_p_822_: *mut crate::leanh::LeanObject,
    mut v_st_823_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_824_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_822_, v_st_823_);
    crate::leanh::lean_dec(v_p_822_);
    return v_res_824_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom(
    mut v_s_825_: *mut crate::leanh::LeanObject,
    mut v_p_826_: *mut crate::leanh::LeanObject,
    mut v_st_827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_828_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom___redArg(v_p_826_, v_st_827_);
    return v___x_828_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_ofSliceFrom___boxed(
    mut v_s_829_: *mut crate::leanh::LeanObject,
    mut v_p_830_: *mut crate::leanh::LeanObject,
    mut v_st_831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_832_ = l_String_Slice_Pattern_SearchStep_ofSliceFrom(v_s_829_, v_p_830_, v_st_831_);
    crate::leanh::lean_dec(v_p_830_);
    crate::leanh::lean_dec_ref(v_s_829_);
    return v_res_832_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___redArg(
    mut v_st_833_: *mut crate::leanh::LeanObject,
    mut v_h__1_834_: *mut crate::leanh::LeanObject,
    mut v_h__2_835_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_st_833_) == 0 {
        let mut v_startPos_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_835_);
        v_startPos_836_ = crate::leanh::lean_ctor_get(v_st_833_, 0);
        crate::leanh::lean_inc(v_startPos_836_);
        v_endPos_837_ = crate::leanh::lean_ctor_get(v_st_833_, 1);
        crate::leanh::lean_inc(v_endPos_837_);
        crate::leanh::lean_dec_ref_known(v_st_833_, 2);
        v___x_838_ = crate::leanh::lean_apply_2(v_h__1_834_, v_startPos_836_, v_endPos_837_);
        return v___x_838_;
    } else {
        let mut v_startPos_839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_834_);
        v_startPos_839_ = crate::leanh::lean_ctor_get(v_st_833_, 0);
        crate::leanh::lean_inc(v_startPos_839_);
        v_endPos_840_ = crate::leanh::lean_ctor_get(v_st_833_, 1);
        crate::leanh::lean_inc(v_endPos_840_);
        crate::leanh::lean_dec_ref_known(v_st_833_, 2);
        v___x_841_ = crate::leanh::lean_apply_2(v_h__2_835_, v_startPos_839_, v_endPos_840_);
        return v___x_841_;
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(
    mut v_s_842_: *mut crate::leanh::LeanObject,
    mut v_p_843_: *mut crate::leanh::LeanObject,
    mut v_motive_844_: *mut crate::leanh::LeanObject,
    mut v_st_845_: *mut crate::leanh::LeanObject,
    mut v_h__1_846_: *mut crate::leanh::LeanObject,
    mut v_h__2_847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_st_845_) == 0 {
        let mut v_startPos_848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_847_);
        v_startPos_848_ = crate::leanh::lean_ctor_get(v_st_845_, 0);
        crate::leanh::lean_inc(v_startPos_848_);
        v_endPos_849_ = crate::leanh::lean_ctor_get(v_st_845_, 1);
        crate::leanh::lean_inc(v_endPos_849_);
        crate::leanh::lean_dec_ref_known(v_st_845_, 2);
        v___x_850_ = crate::leanh::lean_apply_2(v_h__1_846_, v_startPos_848_, v_endPos_849_);
        return v___x_850_;
    } else {
        let mut v_startPos_851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_endPos_852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_846_);
        v_startPos_851_ = crate::leanh::lean_ctor_get(v_st_845_, 0);
        crate::leanh::lean_inc(v_startPos_851_);
        v_endPos_852_ = crate::leanh::lean_ctor_get(v_st_845_, 1);
        crate::leanh::lean_inc(v_endPos_852_);
        crate::leanh::lean_dec_ref_known(v_st_845_, 2);
        v___x_853_ = crate::leanh::lean_apply_2(v_h__2_847_, v_startPos_851_, v_endPos_852_);
        return v___x_853_;
    }
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter___boxed(
    mut v_s_854_: *mut crate::leanh::LeanObject,
    mut v_p_855_: *mut crate::leanh::LeanObject,
    mut v_motive_856_: *mut crate::leanh::LeanObject,
    mut v_st_857_: *mut crate::leanh::LeanObject,
    mut v_h__1_858_: *mut crate::leanh::LeanObject,
    mut v_h__2_859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_860_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_SearchStep_ofSliceFrom_match__1_splitter(v_s_854_, v_p_855_, v_motive_856_, v_st_857_, v_h__1_858_, v_h__2_859_);
    crate::leanh::lean_dec(v_p_855_);
    crate::leanh::lean_dec_ref(v_s_854_);
    return v_res_860_;
}
pub unsafe fn l_String_Slice_Pattern_SearchStep_cast___redArg(
    mut v_x_861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_866_: u8 = 0;
    let mut v___x_868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_870_: u8 = 0;
    let mut v_startPos_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_875_: u8 = 0;
    let mut v___x_877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_879_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_861_) == 0 {
                    v_startPos_862_ = crate::leanh::lean_ctor_get(v_x_861_, 0);
                    v_endPos_863_ = crate::leanh::lean_ctor_get(v_x_861_, 1);
                    v_isSharedCheck_870_ = (!crate::leanh::lean_is_exclusive(v_x_861_)) as u8;
                    if v_isSharedCheck_870_ == 0 {
                        v___x_865_ = v_x_861_;
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_863_);
                        crate::leanh::lean_inc(v_startPos_862_);
                        crate::leanh::lean_dec(v_x_861_);
                        v___x_865_ = crate::leanh::lean_box(0);
                        v_isShared_866_ = v_isSharedCheck_870_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_871_ = crate::leanh::lean_ctor_get(v_x_861_, 0);
                    v_endPos_872_ = crate::leanh::lean_ctor_get(v_x_861_, 1);
                    v_isSharedCheck_879_ = (!crate::leanh::lean_is_exclusive(v_x_861_)) as u8;
                    if v_isSharedCheck_879_ == 0 {
                        v___x_874_ = v_x_861_;
                        v_isShared_875_ = v_isSharedCheck_879_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_872_);
                        crate::leanh::lean_inc(v_startPos_871_);
                        crate::leanh::lean_dec(v_x_861_);
                        v___x_874_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_869_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 0, v_startPos_862_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_869_, 1, v_endPos_863_);
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
                    v_reuseFailAlloc_878_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_878_, 0, v_startPos_871_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_878_, 1, v_endPos_872_);
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
    mut v_s_880_: *mut crate::leanh::LeanObject,
    mut v_t_881_: *mut crate::leanh::LeanObject,
    mut v_hst_882_: *mut crate::leanh::LeanObject,
    mut v_x_883_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startPos_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_888_: u8 = 0;
    let mut v___x_890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_892_: u8 = 0;
    let mut v_startPos_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endPos_894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_897_: u8 = 0;
    let mut v___x_899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_901_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_883_) == 0 {
                    v_startPos_884_ = crate::leanh::lean_ctor_get(v_x_883_, 0);
                    v_endPos_885_ = crate::leanh::lean_ctor_get(v_x_883_, 1);
                    v_isSharedCheck_892_ = (!crate::leanh::lean_is_exclusive(v_x_883_)) as u8;
                    if v_isSharedCheck_892_ == 0 {
                        v___x_887_ = v_x_883_;
                        v_isShared_888_ = v_isSharedCheck_892_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_885_);
                        crate::leanh::lean_inc(v_startPos_884_);
                        crate::leanh::lean_dec(v_x_883_);
                        v___x_887_ = crate::leanh::lean_box(0);
                        v_isShared_888_ = v_isSharedCheck_892_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_startPos_893_ = crate::leanh::lean_ctor_get(v_x_883_, 0);
                    v_endPos_894_ = crate::leanh::lean_ctor_get(v_x_883_, 1);
                    v_isSharedCheck_901_ = (!crate::leanh::lean_is_exclusive(v_x_883_)) as u8;
                    if v_isSharedCheck_901_ == 0 {
                        v___x_896_ = v_x_883_;
                        v_isShared_897_ = v_isSharedCheck_901_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_endPos_894_);
                        crate::leanh::lean_inc(v_startPos_893_);
                        crate::leanh::lean_dec(v_x_883_);
                        v___x_896_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_891_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 0, v_startPos_884_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_891_, 1, v_endPos_885_);
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
                    v_reuseFailAlloc_900_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 0, v_startPos_893_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_900_, 1, v_endPos_894_);
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
    mut v_s_902_: *mut crate::leanh::LeanObject,
    mut v_t_903_: *mut crate::leanh::LeanObject,
    mut v_hst_904_: *mut crate::leanh::LeanObject,
    mut v_x_905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_906_ = l_String_Slice_Pattern_SearchStep_cast(v_s_902_, v_t_903_, v_hst_904_, v_x_905_);
    crate::leanh::lean_dec_ref(v_t_903_);
    crate::leanh::lean_dec_ref(v_s_902_);
    return v_res_906_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(
    mut v_inst_907_: *mut crate::leanh::LeanObject,
    mut v_s_908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_skipPrefix_x3f_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_skipPrefix_x3f_909_ = crate::leanh::lean_ctor_get(v_inst_907_, 0);
    crate::leanh::lean_inc_ref(v_skipPrefix_x3f_909_);
    crate::leanh::lean_dec_ref(v_inst_907_);
    v___x_910_ = crate::leanh::lean_apply_1(v_skipPrefix_x3f_909_, v_s_908_);
    return v___x_910_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(
    mut v_00_u03c1_911_: *mut crate::leanh::LeanObject,
    mut v_pat_912_: *mut crate::leanh::LeanObject,
    mut v_inst_913_: *mut crate::leanh::LeanObject,
    mut v_s_914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_915_ =
        l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___redArg(v_inst_913_, v_s_914_);
    return v___x_915_;
}
pub unsafe fn l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f___boxed(
    mut v_00_u03c1_916_: *mut crate::leanh::LeanObject,
    mut v_pat_917_: *mut crate::leanh::LeanObject,
    mut v_inst_918_: *mut crate::leanh::LeanObject,
    mut v_s_919_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_920_ = l_String_Slice_Pattern_ForwardPattern_dropPrefix_x3f(
        v_00_u03c1_916_,
        v_pat_917_,
        v_inst_918_,
        v_s_919_,
    );
    crate::leanh::lean_dec(v_pat_917_);
    return v_res_920_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(
    mut v_00_u03c1_921_: *mut crate::leanh::LeanObject,
    mut v_pat_922_: *mut crate::leanh::LeanObject,
    mut v_s_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_924_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_924_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default___boxed(
    mut v_00_u03c1_925_: *mut crate::leanh::LeanObject,
    mut v_pat_926_: *mut crate::leanh::LeanObject,
    mut v_s_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ =
        l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher_default(
            v_00_u03c1_925_,
            v_pat_926_,
            v_s_927_,
        );
    crate::leanh::lean_dec_ref(v_s_927_);
    crate::leanh::lean_dec(v_pat_926_);
    return v_res_928_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(
    mut v_a_929_: *mut crate::leanh::LeanObject,
    mut v_a_930_: *mut crate::leanh::LeanObject,
    mut v_a_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_932_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_932_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher___boxed(
    mut v_a_933_: *mut crate::leanh::LeanObject,
    mut v_a_934_: *mut crate::leanh::LeanObject,
    mut v_a_935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_936_ = l_String_Slice_Pattern_ToForwardSearcher_instInhabitedDefaultForwardSearcher(
        v_a_933_, v_a_934_, v_a_935_,
    );
    crate::leanh::lean_dec_ref(v_a_935_);
    crate::leanh::lean_dec(v_a_934_);
    return v_res_936_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(
    mut v_00_u03c1_937_: *mut crate::leanh::LeanObject,
    mut v_pat_938_: *mut crate::leanh::LeanObject,
    mut v_s_939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_940_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_940_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed(
    mut v_00_u03c1_941_: *mut crate::leanh::LeanObject,
    mut v_pat_942_: *mut crate::leanh::LeanObject,
    mut v_s_943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_944_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter(
        v_00_u03c1_941_,
        v_pat_942_,
        v_s_943_,
    );
    crate::leanh::lean_dec_ref(v_s_943_);
    crate::leanh::lean_dec(v_pat_942_);
    return v_res_944_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0(
    mut v_s_945_: *mut crate::leanh::LeanObject,
    mut v_inst_946_: *mut crate::leanh::LeanObject,
    mut v_it_947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_953_: u8 = 0;
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: u8 = 0;
    let mut v_skipPrefixOfNonempty_x3f_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_971_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_948_ = crate::leanh::lean_ctor_get(v_s_945_, 0);
                v_startInclusive_949_ = crate::leanh::lean_ctor_get(v_s_945_, 1);
                v_endExclusive_950_ = crate::leanh::lean_ctor_get(v_s_945_, 2);
                v_isSharedCheck_971_ = (!crate::leanh::lean_is_exclusive(v_s_945_)) as u8;
                if v_isSharedCheck_971_ == 0 {
                    v___x_952_ = v_s_945_;
                    v_isShared_953_ = v_isSharedCheck_971_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_950_);
                    crate::leanh::lean_inc(v_startInclusive_949_);
                    crate::leanh::lean_inc(v_str_948_);
                    crate::leanh::lean_dec(v_s_945_);
                    v___x_952_ = crate::leanh::lean_box(0);
                    v_isShared_953_ = v_isSharedCheck_971_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_954_ = lean_nat_sub(v_endExclusive_950_, v_startInclusive_949_);
                v___x_955_ = lean_nat_dec_eq(v_it_947_, v___x_954_);
                crate::leanh::lean_dec(v___x_954_);
                if v___x_955_ == 0 {
                    v_skipPrefixOfNonempty_x3f_956_ = crate::leanh::lean_ctor_get(v_inst_946_, 1);
                    crate::leanh::lean_inc_ref(v_skipPrefixOfNonempty_x3f_956_);
                    crate::leanh::lean_dec_ref(v_inst_946_);
                    v___x_957_ = lean_nat_add(v_startInclusive_949_, v_it_947_);
                    crate::leanh::lean_inc(v___x_957_);
                    crate::leanh::lean_inc_ref(v_str_948_);
                    if v_isShared_953_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_957_);
                        v___x_959_ = v___x_952_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_969_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_969_, 0, v_str_948_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_957_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_969_, 2, v_endExclusive_950_);
                        v___x_959_ = v_reuseFailAlloc_969_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_952_);
                    crate::leanh::lean_dec(v_endExclusive_950_);
                    crate::leanh::lean_dec(v_startInclusive_949_);
                    crate::leanh::lean_dec_ref(v_str_948_);
                    crate::leanh::lean_dec(v_it_947_);
                    crate::leanh::lean_dec_ref(v_inst_946_);
                    v___x_970_ = crate::leanh::lean_box(2);
                    return v___x_970_;
                }
            }
            2 => {
                v___x_960_ = crate::leanh::lean_apply_2(
                    v_skipPrefixOfNonempty_x3f_956_,
                    v___x_959_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_960_) == 0 {
                    v___x_961_ = lean_string_utf8_next_fast(v_str_948_, v___x_957_);
                    crate::leanh::lean_dec(v___x_957_);
                    crate::leanh::lean_dec_ref(v_str_948_);
                    v___x_962_ = lean_nat_sub(v___x_961_, v_startInclusive_949_);
                    crate::leanh::lean_dec(v_startInclusive_949_);
                    crate::leanh::lean_inc(v___x_962_);
                    v___x_963_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_963_, 0, v_it_947_);
                    crate::leanh::lean_ctor_set(v___x_963_, 1, v___x_962_);
                    v___x_964_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_962_);
                    crate::leanh::lean_ctor_set(v___x_964_, 1, v___x_963_);
                    return v___x_964_;
                } else {
                    crate::leanh::lean_dec(v___x_957_);
                    crate::leanh::lean_dec(v_startInclusive_949_);
                    crate::leanh::lean_dec_ref(v_str_948_);
                    v_val_965_ = crate::leanh::lean_ctor_get(v___x_960_, 0);
                    crate::leanh::lean_inc(v_val_965_);
                    crate::leanh::lean_dec_ref_known(v___x_960_, 1);
                    v___x_966_ = lean_nat_add(v_it_947_, v_val_965_);
                    crate::leanh::lean_dec(v_val_965_);
                    crate::leanh::lean_inc(v___x_966_);
                    v___x_967_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_967_, 0, v_it_947_);
                    crate::leanh::lean_ctor_set(v___x_967_, 1, v___x_966_);
                    v___x_968_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_968_, 0, v___x_966_);
                    crate::leanh::lean_ctor_set(v___x_968_, 1, v___x_967_);
                    return v___x_968_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg(
    mut v_s_972_: *mut crate::leanh::LeanObject,
    mut v_inst_973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_974_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_974_, 0, v_s_972_);
    crate::leanh::lean_closure_set(v___f_974_, 1, v_inst_973_);
    return v___f_974_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(
    mut v_00_u03c1_975_: *mut crate::leanh::LeanObject,
    mut v_pat_976_: *mut crate::leanh::LeanObject,
    mut v_s_977_: *mut crate::leanh::LeanObject,
    mut v_inst_978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_979_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___redArg___lam__0 as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_979_, 0, v_s_977_);
    crate::leanh::lean_closure_set(v___f_979_, 1, v_inst_978_);
    return v___f_979_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern___boxed(
    mut v_00_u03c1_980_: *mut crate::leanh::LeanObject,
    mut v_pat_981_: *mut crate::leanh::LeanObject,
    mut v_s_982_: *mut crate::leanh::LeanObject,
    mut v_inst_983_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_984_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorIdSearchStepOfForwardPattern(v_00_u03c1_980_, v_pat_981_, v_s_982_, v_inst_983_);
    crate::leanh::lean_dec(v_pat_981_);
    return v_res_984_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(
    mut v_00_u03c1_985_: *mut crate::leanh::LeanObject,
    mut v_pat_986_: *mut crate::leanh::LeanObject,
    mut v_s_987_: *mut crate::leanh::LeanObject,
    mut v_inst_988_: *mut crate::leanh::LeanObject,
    mut v_inst_989_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_990_ = crate::leanh::lean_box(0);
    return v___x_990_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation___boxed(
    mut v_00_u03c1_991_: *mut crate::leanh::LeanObject,
    mut v_pat_992_: *mut crate::leanh::LeanObject,
    mut v_s_993_: *mut crate::leanh::LeanObject,
    mut v_inst_994_: *mut crate::leanh::LeanObject,
    mut v_inst_995_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_996_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_finitenessRelation(v_00_u03c1_991_, v_pat_992_, v_s_993_, v_inst_994_, v_inst_995_);
    crate::leanh::lean_dec_ref(v_inst_994_);
    crate::leanh::lean_dec_ref(v_s_993_);
    crate::leanh::lean_dec(v_pat_992_);
    return v_res_996_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(
    mut v___y_997_: *mut crate::leanh::LeanObject,
    mut v_acc_998_: *mut crate::leanh::LeanObject,
    mut v_recur_999_: *mut crate::leanh::LeanObject,
    mut v_s_1000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1000_) {
        0 => {
            let mut v_it_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_val_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1001_ = crate::leanh::lean_ctor_get(v_s_1000_, 0);
            crate::leanh::lean_inc(v_it_1001_);
            v_out_1002_ = crate::leanh::lean_ctor_get(v_s_1000_, 1);
            crate::leanh::lean_inc(v_out_1002_);
            crate::leanh::lean_dec_ref_known(v_s_1000_, 2);
            v_val_1003_ = crate::leanh::lean_apply_3(
                v___y_997_,
                v_out_1002_,
                crate::leanh::lean_box(0),
                v_acc_998_,
            );
            if crate::leanh::lean_obj_tag(v_val_1003_) == 0 {
                let mut v_a_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec(v_it_1001_);
                crate::leanh::lean_dec(v_recur_999_);
                v_a_1004_ = crate::leanh::lean_ctor_get(v_val_1003_, 0);
                crate::leanh::lean_inc(v_a_1004_);
                crate::leanh::lean_dec_ref_known(v_val_1003_, 1);
                return v_a_1004_;
            } else {
                let mut v_a_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v_a_1005_ = crate::leanh::lean_ctor_get(v_val_1003_, 0);
                crate::leanh::lean_inc(v_a_1005_);
                crate::leanh::lean_dec_ref_known(v_val_1003_, 1);
                v___x_1006_ = crate::leanh::lean_apply_4(
                    v_recur_999_,
                    v_it_1001_,
                    v_a_1005_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                );
                return v___x_1006_;
            }
        }
        1 => {
            let mut v_it_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___y_997_);
            v_it_1007_ = crate::leanh::lean_ctor_get(v_s_1000_, 0);
            crate::leanh::lean_inc(v_it_1007_);
            crate::leanh::lean_dec_ref_known(v_s_1000_, 1);
            v___x_1008_ = crate::leanh::lean_apply_4(
                v_recur_999_,
                v_it_1007_,
                v_acc_998_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1008_;
        }
        _ => {
            crate::leanh::lean_dec(v_recur_999_);
            crate::leanh::lean_dec_ref(v___y_997_);
            return v_acc_998_;
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(
    mut v_s_1009_: *mut crate::leanh::LeanObject,
    mut v___y_1010_: *mut crate::leanh::LeanObject,
    mut v_inst_1011_: *mut crate::leanh::LeanObject,
    mut v_lift_1012_: *mut crate::leanh::LeanObject,
    mut v_it_1013_: *mut crate::leanh::LeanObject,
    mut v_acc_1014_: *mut crate::leanh::LeanObject,
    mut v_hP_1015_: *mut crate::leanh::LeanObject,
    mut v_recur_1016_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1022_: u8 = 0;
    let mut v___f_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1025_: u8 = 0;
    let mut v_skipPrefixOfNonempty_x3f_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1044_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1017_ = crate::leanh::lean_ctor_get(v_s_1009_, 0);
                v_startInclusive_1018_ = crate::leanh::lean_ctor_get(v_s_1009_, 1);
                v_endExclusive_1019_ = crate::leanh::lean_ctor_get(v_s_1009_, 2);
                v_isSharedCheck_1044_ = (!crate::leanh::lean_is_exclusive(v_s_1009_)) as u8;
                if v_isSharedCheck_1044_ == 0 {
                    v___x_1021_ = v_s_1009_;
                    v_isShared_1022_ = v_isSharedCheck_1044_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_endExclusive_1019_);
                    crate::leanh::lean_inc(v_startInclusive_1018_);
                    crate::leanh::lean_inc(v_str_1017_);
                    crate::leanh::lean_dec(v_s_1009_);
                    v___x_1021_ = crate::leanh::lean_box(0);
                    v_isShared_1022_ = v_isSharedCheck_1044_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1023_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_1023_, 0, v___y_1010_);
                crate::leanh::lean_closure_set(v___f_1023_, 1, v_acc_1014_);
                crate::leanh::lean_closure_set(v___f_1023_, 2, v_recur_1016_);
                v___x_1024_ = lean_nat_sub(v_endExclusive_1019_, v_startInclusive_1018_);
                v___x_1025_ = lean_nat_dec_eq(v_it_1013_, v___x_1024_);
                crate::leanh::lean_dec(v___x_1024_);
                if v___x_1025_ == 0 {
                    v_skipPrefixOfNonempty_x3f_1026_ = crate::leanh::lean_ctor_get(v_inst_1011_, 1);
                    crate::leanh::lean_inc_ref(v_skipPrefixOfNonempty_x3f_1026_);
                    crate::leanh::lean_dec_ref(v_inst_1011_);
                    v___x_1027_ = lean_nat_add(v_startInclusive_1018_, v_it_1013_);
                    crate::leanh::lean_inc(v___x_1027_);
                    crate::leanh::lean_inc_ref(v_str_1017_);
                    if v_isShared_1022_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1021_, 1, v___x_1027_);
                        v___x_1029_ = v___x_1021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1041_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_str_1017_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1041_, 1, v___x_1027_);
                        crate::leanh::lean_ctor_set(
                            v_reuseFailAlloc_1041_,
                            2,
                            v_endExclusive_1019_,
                        );
                        v___x_1029_ = v_reuseFailAlloc_1041_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1021_);
                    crate::leanh::lean_dec(v_endExclusive_1019_);
                    crate::leanh::lean_dec(v_startInclusive_1018_);
                    crate::leanh::lean_dec_ref(v_str_1017_);
                    crate::leanh::lean_dec(v_it_1013_);
                    crate::leanh::lean_dec_ref(v_inst_1011_);
                    v___x_1042_ = crate::leanh::lean_box(2);
                    v___x_1043_ = crate::leanh::lean_apply_4(
                        v_lift_1012_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1023_,
                        v___x_1042_,
                    );
                    return v___x_1043_;
                }
            }
            2 => {
                v___x_1030_ = crate::leanh::lean_apply_2(
                    v_skipPrefixOfNonempty_x3f_1026_,
                    v___x_1029_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1030_) == 0 {
                    v___x_1031_ = lean_string_utf8_next_fast(v_str_1017_, v___x_1027_);
                    crate::leanh::lean_dec(v___x_1027_);
                    crate::leanh::lean_dec_ref(v_str_1017_);
                    v___x_1032_ = lean_nat_sub(v___x_1031_, v_startInclusive_1018_);
                    crate::leanh::lean_dec(v_startInclusive_1018_);
                    crate::leanh::lean_inc(v___x_1032_);
                    v___x_1033_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1033_, 0, v_it_1013_);
                    crate::leanh::lean_ctor_set(v___x_1033_, 1, v___x_1032_);
                    v___x_1034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1034_, 0, v___x_1032_);
                    crate::leanh::lean_ctor_set(v___x_1034_, 1, v___x_1033_);
                    v___x_1035_ = crate::leanh::lean_apply_4(
                        v_lift_1012_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1023_,
                        v___x_1034_,
                    );
                    return v___x_1035_;
                } else {
                    crate::leanh::lean_dec(v___x_1027_);
                    crate::leanh::lean_dec(v_startInclusive_1018_);
                    crate::leanh::lean_dec_ref(v_str_1017_);
                    v_val_1036_ = crate::leanh::lean_ctor_get(v___x_1030_, 0);
                    crate::leanh::lean_inc(v_val_1036_);
                    crate::leanh::lean_dec_ref_known(v___x_1030_, 1);
                    v___x_1037_ = lean_nat_add(v_it_1013_, v_val_1036_);
                    crate::leanh::lean_dec(v_val_1036_);
                    crate::leanh::lean_inc(v___x_1037_);
                    v___x_1038_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1038_, 0, v_it_1013_);
                    crate::leanh::lean_ctor_set(v___x_1038_, 1, v___x_1037_);
                    v___x_1039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1039_, 0, v___x_1037_);
                    crate::leanh::lean_ctor_set(v___x_1039_, 1, v___x_1038_);
                    v___x_1040_ = crate::leanh::lean_apply_4(
                        v_lift_1012_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v_s_1045_: *mut crate::leanh::LeanObject,
    mut v_inst_1046_: *mut crate::leanh::LeanObject,
    mut v_lift_1047_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1048_: *mut crate::leanh::LeanObject,
    mut v_Pl_1049_: *mut crate::leanh::LeanObject,
    mut v_it_1050_: *mut crate::leanh::LeanObject,
    mut v_init_1051_: *mut crate::leanh::LeanObject,
    mut v___y_1052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1053_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1 as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_1053_, 0, v_s_1045_);
    crate::leanh::lean_closure_set(v___f_1053_, 1, v___y_1052_);
    crate::leanh::lean_closure_set(v___f_1053_, 2, v_inst_1046_);
    crate::leanh::lean_closure_set(v___f_1053_, 3, v_lift_1047_);
    v___x_1054_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1053_,
        v_it_1050_,
        v_init_1051_,
        crate::leanh::lean_box(0),
    );
    return v___x_1054_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg(
    mut v_s_1055_: *mut crate::leanh::LeanObject,
    mut v_inst_1056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1057_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2 as *mut core::ffi::c_void, 8, 2);
    crate::leanh::lean_closure_set(v___f_1057_, 0, v_s_1055_);
    crate::leanh::lean_closure_set(v___f_1057_, 1, v_inst_1056_);
    return v___f_1057_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(
    mut v_00_u03c1_1058_: *mut crate::leanh::LeanObject,
    mut v_pat_1059_: *mut crate::leanh::LeanObject,
    mut v_s_1060_: *mut crate::leanh::LeanObject,
    mut v_inst_1061_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1062_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__2 as *mut core::ffi::c_void, 8, 2);
    crate::leanh::lean_closure_set(v___f_1062_, 0, v_s_1060_);
    crate::leanh::lean_closure_set(v___f_1062_, 1, v_inst_1061_);
    return v___f_1062_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___boxed(
    mut v_00_u03c1_1063_: *mut crate::leanh::LeanObject,
    mut v_pat_1064_: *mut crate::leanh::LeanObject,
    mut v_s_1065_: *mut crate::leanh::LeanObject,
    mut v_inst_1066_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1067_ = l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_1063_, v_pat_1064_, v_s_1065_, v_inst_1066_);
    crate::leanh::lean_dec(v_pat_1064_);
    return v_res_1067_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___redArg(
    mut v_pat_1068_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1069_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1069_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1069_, 1, v_pat_1068_);
    return v___x_1069_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(
    mut v_00_u03c1_1070_: *mut crate::leanh::LeanObject,
    mut v_pat_1071_: *mut crate::leanh::LeanObject,
    mut v_inst_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1073_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1073_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1073_, 1, v_pat_1071_);
    return v___x_1073_;
}
pub unsafe fn l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation___boxed(
    mut v_00_u03c1_1074_: *mut crate::leanh::LeanObject,
    mut v_pat_1075_: *mut crate::leanh::LeanObject,
    mut v_inst_1076_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1077_ = l_String_Slice_Pattern_ToForwardSearcher_defaultImplementation(
        v_00_u03c1_1074_,
        v_pat_1075_,
        v_inst_1076_,
    );
    crate::leanh::lean_dec_ref(v_inst_1076_);
    return v_res_1077_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(
    mut v_lhs_1078_: *mut crate::leanh::LeanObject,
    mut v_rhs_1079_: *mut crate::leanh::LeanObject,
    mut v_lstart_1080_: *mut crate::leanh::LeanObject,
    mut v_rstart_1081_: *mut crate::leanh::LeanObject,
    mut v_len_1082_: *mut crate::leanh::LeanObject,
    mut v_curr_1083_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1084_: u8 = 0;
    let mut v___x_1085_: u8 = 0;
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1087_: u8 = 0;
    let mut v___x_1088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1089_: u8 = 0;
    let mut v___x_1090_: u8 = 0;
    let mut v___x_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1084_ = lean_nat_dec_lt(v_curr_1083_, v_len_1082_);
                if v___x_1084_ == 0 {
                    crate::leanh::lean_dec(v_curr_1083_);
                    v___x_1085_ = 1;
                    return v___x_1085_;
                } else {
                    v___x_1086_ = lean_nat_add(v_lstart_1080_, v_curr_1083_);
                    v___x_1087_ = lean_string_get_byte_fast(v_lhs_1078_, v___x_1086_);
                    v___x_1088_ = lean_nat_add(v_rstart_1081_, v_curr_1083_);
                    v___x_1089_ = lean_string_get_byte_fast(v_rhs_1079_, v___x_1088_);
                    v___x_1090_ = lean_uint8_dec_eq(v___x_1087_, v___x_1089_);
                    if v___x_1090_ == 0 {
                        crate::leanh::lean_dec(v_curr_1083_);
                        return v___x_1090_;
                    } else {
                        v___x_1091_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1092_ = lean_nat_add(v_curr_1083_, v___x_1091_);
                        crate::leanh::lean_dec(v_curr_1083_);
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
    mut v_lhs_1094_: *mut crate::leanh::LeanObject,
    mut v_rhs_1095_: *mut crate::leanh::LeanObject,
    mut v_lstart_1096_: *mut crate::leanh::LeanObject,
    mut v_rstart_1097_: *mut crate::leanh::LeanObject,
    mut v_len_1098_: *mut crate::leanh::LeanObject,
    mut v_curr_1099_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1100_: u8 = 0;
    let mut v_r_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1100_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_1094_, v_rhs_1095_, v_lstart_1096_, v_rstart_1097_, v_len_1098_, v_curr_1099_);
    crate::leanh::lean_dec(v_len_1098_);
    crate::leanh::lean_dec(v_rstart_1097_);
    crate::leanh::lean_dec(v_lstart_1096_);
    crate::leanh::lean_dec_ref(v_rhs_1095_);
    crate::leanh::lean_dec_ref(v_lhs_1094_);
    v_r_1101_ = crate::leanh::lean_box((v_res_1100_) as usize);
    return v_r_1101_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go(
    mut v_lhs_1102_: *mut crate::leanh::LeanObject,
    mut v_rhs_1103_: *mut crate::leanh::LeanObject,
    mut v_lstart_1104_: *mut crate::leanh::LeanObject,
    mut v_rstart_1105_: *mut crate::leanh::LeanObject,
    mut v_len_1106_: *mut crate::leanh::LeanObject,
    mut v_h1_1107_: *mut crate::leanh::LeanObject,
    mut v_h2_1108_: *mut crate::leanh::LeanObject,
    mut v_curr_1109_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_1110_: u8 = 0;
    v___x_1110_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___redArg(v_lhs_1102_, v_rhs_1103_, v_lstart_1104_, v_rstart_1105_, v_len_1106_, v_curr_1109_);
    return v___x_1110_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_Internal_memcmpStr_go___boxed(
    mut v_lhs_1111_: *mut crate::leanh::LeanObject,
    mut v_rhs_1112_: *mut crate::leanh::LeanObject,
    mut v_lstart_1113_: *mut crate::leanh::LeanObject,
    mut v_rstart_1114_: *mut crate::leanh::LeanObject,
    mut v_len_1115_: *mut crate::leanh::LeanObject,
    mut v_h1_1116_: *mut crate::leanh::LeanObject,
    mut v_h2_1117_: *mut crate::leanh::LeanObject,
    mut v_curr_1118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1119_: u8 = 0;
    let mut v_r_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v_len_1115_);
    crate::leanh::lean_dec(v_rstart_1114_);
    crate::leanh::lean_dec(v_lstart_1113_);
    crate::leanh::lean_dec_ref(v_rhs_1112_);
    crate::leanh::lean_dec_ref(v_lhs_1111_);
    v_r_1120_ = crate::leanh::lean_box((v_res_1119_) as usize);
    return v_r_1120_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpStr___boxed(
    mut v_lhs_1128_: *mut crate::leanh::LeanObject,
    mut v_rhs_1129_: *mut crate::leanh::LeanObject,
    mut v_lstart_1130_: *mut crate::leanh::LeanObject,
    mut v_rstart_1131_: *mut crate::leanh::LeanObject,
    mut v_len_1132_: *mut crate::leanh::LeanObject,
    mut v_h1_1133_: *mut crate::leanh::LeanObject,
    mut v_h2_1134_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1135_: u8 = 0;
    let mut v_r_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1135_ = lean_string_memcmp(
        v_lhs_1128_,
        v_rhs_1129_,
        v_lstart_1130_,
        v_rstart_1131_,
        v_len_1132_,
    );
    crate::leanh::lean_dec(v_len_1132_);
    crate::leanh::lean_dec(v_rstart_1131_);
    crate::leanh::lean_dec(v_lstart_1130_);
    crate::leanh::lean_dec_ref(v_rhs_1129_);
    crate::leanh::lean_dec_ref(v_lhs_1128_);
    v_r_1136_ = crate::leanh::lean_box((v_res_1135_) as usize);
    return v_r_1136_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___redArg(
    mut v_lhs_1137_: *mut crate::leanh::LeanObject,
    mut v_rhs_1138_: *mut crate::leanh::LeanObject,
    mut v_lstart_1139_: *mut crate::leanh::LeanObject,
    mut v_rstart_1140_: *mut crate::leanh::LeanObject,
    mut v_len_1141_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1148_: u8 = 0;
    v_str_1142_ = crate::leanh::lean_ctor_get(v_lhs_1137_, 0);
    v_startInclusive_1143_ = crate::leanh::lean_ctor_get(v_lhs_1137_, 1);
    v_str_1144_ = crate::leanh::lean_ctor_get(v_rhs_1138_, 0);
    v_startInclusive_1145_ = crate::leanh::lean_ctor_get(v_rhs_1138_, 1);
    v___x_1146_ = lean_nat_add(v_startInclusive_1143_, v_lstart_1139_);
    v___x_1147_ = lean_nat_add(v_startInclusive_1145_, v_rstart_1140_);
    v___x_1148_ = lean_string_memcmp(
        v_str_1142_,
        v_str_1144_,
        v___x_1146_,
        v___x_1147_,
        v_len_1141_,
    );
    crate::leanh::lean_dec(v___x_1147_);
    crate::leanh::lean_dec(v___x_1146_);
    return v___x_1148_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___redArg___boxed(
    mut v_lhs_1149_: *mut crate::leanh::LeanObject,
    mut v_rhs_1150_: *mut crate::leanh::LeanObject,
    mut v_lstart_1151_: *mut crate::leanh::LeanObject,
    mut v_rstart_1152_: *mut crate::leanh::LeanObject,
    mut v_len_1153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1154_: u8 = 0;
    let mut v_r_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1154_ = l_String_Slice_Pattern_Internal_memcmpSlice___redArg(
        v_lhs_1149_,
        v_rhs_1150_,
        v_lstart_1151_,
        v_rstart_1152_,
        v_len_1153_,
    );
    crate::leanh::lean_dec(v_len_1153_);
    crate::leanh::lean_dec(v_rstart_1152_);
    crate::leanh::lean_dec(v_lstart_1151_);
    crate::leanh::lean_dec_ref(v_rhs_1150_);
    crate::leanh::lean_dec_ref(v_lhs_1149_);
    v_r_1155_ = crate::leanh::lean_box((v_res_1154_) as usize);
    return v_r_1155_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice(
    mut v_lhs_1156_: *mut crate::leanh::LeanObject,
    mut v_rhs_1157_: *mut crate::leanh::LeanObject,
    mut v_lstart_1158_: *mut crate::leanh::LeanObject,
    mut v_rstart_1159_: *mut crate::leanh::LeanObject,
    mut v_len_1160_: *mut crate::leanh::LeanObject,
    mut v_h1_1161_: *mut crate::leanh::LeanObject,
    mut v_h2_1162_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_str_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_1165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1169_: u8 = 0;
    v_str_1163_ = crate::leanh::lean_ctor_get(v_lhs_1156_, 0);
    v_startInclusive_1164_ = crate::leanh::lean_ctor_get(v_lhs_1156_, 1);
    v_str_1165_ = crate::leanh::lean_ctor_get(v_rhs_1157_, 0);
    v_startInclusive_1166_ = crate::leanh::lean_ctor_get(v_rhs_1157_, 1);
    v___x_1167_ = lean_nat_add(v_startInclusive_1164_, v_lstart_1158_);
    v___x_1168_ = lean_nat_add(v_startInclusive_1166_, v_rstart_1159_);
    v___x_1169_ = lean_string_memcmp(
        v_str_1163_,
        v_str_1165_,
        v___x_1167_,
        v___x_1168_,
        v_len_1160_,
    );
    crate::leanh::lean_dec(v___x_1168_);
    crate::leanh::lean_dec(v___x_1167_);
    return v___x_1169_;
}
pub unsafe fn l_String_Slice_Pattern_Internal_memcmpSlice___boxed(
    mut v_lhs_1170_: *mut crate::leanh::LeanObject,
    mut v_rhs_1171_: *mut crate::leanh::LeanObject,
    mut v_lstart_1172_: *mut crate::leanh::LeanObject,
    mut v_rstart_1173_: *mut crate::leanh::LeanObject,
    mut v_len_1174_: *mut crate::leanh::LeanObject,
    mut v_h1_1175_: *mut crate::leanh::LeanObject,
    mut v_h2_1176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1177_: u8 = 0;
    let mut v_r_1178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1177_ = l_String_Slice_Pattern_Internal_memcmpSlice(
        v_lhs_1170_,
        v_rhs_1171_,
        v_lstart_1172_,
        v_rstart_1173_,
        v_len_1174_,
        v_h1_1175_,
        v_h2_1176_,
    );
    crate::leanh::lean_dec(v_len_1174_);
    crate::leanh::lean_dec(v_rstart_1173_);
    crate::leanh::lean_dec(v_lstart_1172_);
    crate::leanh::lean_dec_ref(v_rhs_1171_);
    crate::leanh::lean_dec_ref(v_lhs_1170_);
    v_r_1178_ = crate::leanh::lean_box((v_res_1177_) as usize);
    return v_r_1178_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(
    mut v_00_u03c1_1179_: *mut crate::leanh::LeanObject,
    mut v_pat_1180_: *mut crate::leanh::LeanObject,
    mut v_s_1181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1182_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1182_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default___boxed(
    mut v_00_u03c1_1183_: *mut crate::leanh::LeanObject,
    mut v_pat_1184_: *mut crate::leanh::LeanObject,
    mut v_s_1185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1186_ =
        l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher_default(
            v_00_u03c1_1183_,
            v_pat_1184_,
            v_s_1185_,
        );
    crate::leanh::lean_dec_ref(v_s_1185_);
    crate::leanh::lean_dec(v_pat_1184_);
    return v_res_1186_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(
    mut v_a_1187_: *mut crate::leanh::LeanObject,
    mut v_a_1188_: *mut crate::leanh::LeanObject,
    mut v_a_1189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1190_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1190_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher___boxed(
    mut v_a_1191_: *mut crate::leanh::LeanObject,
    mut v_a_1192_: *mut crate::leanh::LeanObject,
    mut v_a_1193_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1194_ = l_String_Slice_Pattern_ToBackwardSearcher_instInhabitedDefaultBackwardSearcher(
        v_a_1191_, v_a_1192_, v_a_1193_,
    );
    crate::leanh::lean_dec_ref(v_a_1193_);
    crate::leanh::lean_dec(v_a_1192_);
    return v_res_1194_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(
    mut v_s_1195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1196_ = crate::leanh::lean_ctor_get(v_s_1195_, 1);
    v_endExclusive_1197_ = crate::leanh::lean_ctor_get(v_s_1195_, 2);
    v___x_1198_ = lean_nat_sub(v_endExclusive_1197_, v_startInclusive_1196_);
    return v___x_1198_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg___boxed(
    mut v_s_1199_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1200_ =
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___redArg(v_s_1199_);
    crate::leanh::lean_dec_ref(v_s_1199_);
    return v_res_1200_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(
    mut v_00_u03c1_1201_: *mut crate::leanh::LeanObject,
    mut v_pat_1202_: *mut crate::leanh::LeanObject,
    mut v_s_1203_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1204_ = crate::leanh::lean_ctor_get(v_s_1203_, 1);
    v_endExclusive_1205_ = crate::leanh::lean_ctor_get(v_s_1203_, 2);
    v___x_1206_ = lean_nat_sub(v_endExclusive_1205_, v_startInclusive_1204_);
    return v___x_1206_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed(
    mut v_00_u03c1_1207_: *mut crate::leanh::LeanObject,
    mut v_pat_1208_: *mut crate::leanh::LeanObject,
    mut v_s_1209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1210_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter(
        v_00_u03c1_1207_,
        v_pat_1208_,
        v_s_1209_,
    );
    crate::leanh::lean_dec_ref(v_s_1209_);
    crate::leanh::lean_dec(v_pat_1208_);
    return v_res_1210_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(
    mut v_inst_1211_: *mut crate::leanh::LeanObject,
    mut v_s_1212_: *mut crate::leanh::LeanObject,
    mut v_it_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: u8 = 0;
    let mut v_skipSuffixOfNonempty_x3f_1216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1219_: u8 = 0;
    let mut v_str_1220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1235_: u8 = 0;
    let mut v_unused_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1214_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1215_ = lean_nat_dec_eq(v_it_1213_, v___x_1214_);
                if v___x_1215_ == 0 {
                    v_skipSuffixOfNonempty_x3f_1216_ = crate::leanh::lean_ctor_get(v_inst_1211_, 1);
                    v_isSharedCheck_1235_ = (!crate::leanh::lean_is_exclusive(v_inst_1211_)) as u8;
                    if v_isSharedCheck_1235_ == 0 {
                        v_unused_1236_ = crate::leanh::lean_ctor_get(v_inst_1211_, 2);
                        crate::leanh::lean_dec(v_unused_1236_);
                        v_unused_1237_ = crate::leanh::lean_ctor_get(v_inst_1211_, 0);
                        crate::leanh::lean_dec(v_unused_1237_);
                        v___x_1218_ = v_inst_1211_;
                        v_isShared_1219_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_skipSuffixOfNonempty_x3f_1216_);
                        crate::leanh::lean_dec(v_inst_1211_);
                        v___x_1218_ = crate::leanh::lean_box(0);
                        v_isShared_1219_ = v_isSharedCheck_1235_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_it_1213_);
                    crate::leanh::lean_dec_ref(v_inst_1211_);
                    v___x_1238_ = crate::leanh::lean_box(2);
                    return v___x_1238_;
                }
            }
            1 => {
                v_str_1220_ = crate::leanh::lean_ctor_get(v_s_1212_, 0);
                v_startInclusive_1221_ = crate::leanh::lean_ctor_get(v_s_1212_, 1);
                v___x_1222_ = lean_nat_add(v_startInclusive_1221_, v_it_1213_);
                crate::leanh::lean_inc(v_startInclusive_1221_);
                crate::leanh::lean_inc_ref(v_str_1220_);
                if v_isShared_1219_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1218_, 2, v___x_1222_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 1, v_startInclusive_1221_);
                    crate::leanh::lean_ctor_set(v___x_1218_, 0, v_str_1220_);
                    v___x_1224_ = v___x_1218_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1234_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 0, v_str_1220_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 1, v_startInclusive_1221_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1234_, 2, v___x_1222_);
                    v___x_1224_ = v_reuseFailAlloc_1234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1225_ = crate::leanh::lean_apply_2(
                    v_skipSuffixOfNonempty_x3f_1216_,
                    v___x_1224_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1225_) == 0 {
                    v___x_1226_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1227_ = lean_nat_sub(v_it_1213_, v___x_1226_);
                    v___x_1228_ = l_String_Slice_posLE(v_s_1212_, v___x_1227_);
                    crate::leanh::lean_inc(v___x_1228_);
                    v___x_1229_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1229_, 0, v___x_1228_);
                    crate::leanh::lean_ctor_set(v___x_1229_, 1, v_it_1213_);
                    v___x_1230_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1230_, 0, v___x_1228_);
                    crate::leanh::lean_ctor_set(v___x_1230_, 1, v___x_1229_);
                    return v___x_1230_;
                } else {
                    v_val_1231_ = crate::leanh::lean_ctor_get(v___x_1225_, 0);
                    crate::leanh::lean_inc_n(v_val_1231_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1225_, 1);
                    v___x_1232_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1232_, 0, v_val_1231_);
                    crate::leanh::lean_ctor_set(v___x_1232_, 1, v_it_1213_);
                    v___x_1233_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1233_, 0, v_val_1231_);
                    crate::leanh::lean_ctor_set(v___x_1233_, 1, v___x_1232_);
                    return v___x_1233_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed(
    mut v_inst_1239_: *mut crate::leanh::LeanObject,
    mut v_s_1240_: *mut crate::leanh::LeanObject,
    mut v_it_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1242_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0(v_inst_1239_, v_s_1240_, v_it_1241_);
    crate::leanh::lean_dec_ref(v_s_1240_);
    return v_res_1242_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg(
    mut v_s_1243_: *mut crate::leanh::LeanObject,
    mut v_inst_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1245_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1245_, 0, v_inst_1244_);
    crate::leanh::lean_closure_set(v___f_1245_, 1, v_s_1243_);
    return v___f_1245_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(
    mut v_00_u03c1_1246_: *mut crate::leanh::LeanObject,
    mut v_pat_1247_: *mut crate::leanh::LeanObject,
    mut v_s_1248_: *mut crate::leanh::LeanObject,
    mut v_inst_1249_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1250_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
    crate::leanh::lean_closure_set(v___f_1250_, 0, v_inst_1249_);
    crate::leanh::lean_closure_set(v___f_1250_, 1, v_s_1248_);
    return v___f_1250_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern___boxed(
    mut v_00_u03c1_1251_: *mut crate::leanh::LeanObject,
    mut v_pat_1252_: *mut crate::leanh::LeanObject,
    mut v_s_1253_: *mut crate::leanh::LeanObject,
    mut v_inst_1254_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1255_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorIdSearchStepOfBackwardPattern(v_00_u03c1_1251_, v_pat_1252_, v_s_1253_, v_inst_1254_);
    crate::leanh::lean_dec(v_pat_1252_);
    return v_res_1255_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(
    mut v_00_u03c1_1256_: *mut crate::leanh::LeanObject,
    mut v_pat_1257_: *mut crate::leanh::LeanObject,
    mut v_s_1258_: *mut crate::leanh::LeanObject,
    mut v_inst_1259_: *mut crate::leanh::LeanObject,
    mut v_inst_1260_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1261_ = crate::leanh::lean_box(0);
    return v___x_1261_;
}
pub unsafe fn l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation___boxed(
    mut v_00_u03c1_1262_: *mut crate::leanh::LeanObject,
    mut v_pat_1263_: *mut crate::leanh::LeanObject,
    mut v_s_1264_: *mut crate::leanh::LeanObject,
    mut v_inst_1265_: *mut crate::leanh::LeanObject,
    mut v_inst_1266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1267_ = l___private_Init_Data_String_Pattern_Basic_0__String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_finitenessRelation(v_00_u03c1_1262_, v_pat_1263_, v_s_1264_, v_inst_1265_, v_inst_1266_);
    crate::leanh::lean_dec_ref(v_inst_1265_);
    crate::leanh::lean_dec_ref(v_s_1264_);
    crate::leanh::lean_dec(v_pat_1263_);
    return v_res_1267_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(
    mut v___y_1268_: *mut crate::leanh::LeanObject,
    mut v_inst_1269_: *mut crate::leanh::LeanObject,
    mut v_s_1270_: *mut crate::leanh::LeanObject,
    mut v_lift_1271_: *mut crate::leanh::LeanObject,
    mut v_it_1272_: *mut crate::leanh::LeanObject,
    mut v_acc_1273_: *mut crate::leanh::LeanObject,
    mut v_hP_1274_: *mut crate::leanh::LeanObject,
    mut v_recur_1275_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1278_: u8 = 0;
    let mut v_skipSuffixOfNonempty_x3f_1279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1282_: u8 = 0;
    let mut v_str_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1300_: u8 = 0;
    let mut v_unused_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_1302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_1276_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToForwardSearcher_DefaultForwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
                crate::leanh::lean_closure_set(v___f_1276_, 0, v___y_1268_);
                crate::leanh::lean_closure_set(v___f_1276_, 1, v_acc_1273_);
                crate::leanh::lean_closure_set(v___f_1276_, 2, v_recur_1275_);
                v___x_1277_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1278_ = lean_nat_dec_eq(v_it_1272_, v___x_1277_);
                if v___x_1278_ == 0 {
                    v_skipSuffixOfNonempty_x3f_1279_ = crate::leanh::lean_ctor_get(v_inst_1269_, 1);
                    v_isSharedCheck_1300_ = (!crate::leanh::lean_is_exclusive(v_inst_1269_)) as u8;
                    if v_isSharedCheck_1300_ == 0 {
                        v_unused_1301_ = crate::leanh::lean_ctor_get(v_inst_1269_, 2);
                        crate::leanh::lean_dec(v_unused_1301_);
                        v_unused_1302_ = crate::leanh::lean_ctor_get(v_inst_1269_, 0);
                        crate::leanh::lean_dec(v_unused_1302_);
                        v___x_1281_ = v_inst_1269_;
                        v_isShared_1282_ = v_isSharedCheck_1300_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_skipSuffixOfNonempty_x3f_1279_);
                        crate::leanh::lean_dec(v_inst_1269_);
                        v___x_1281_ = crate::leanh::lean_box(0);
                        v_isShared_1282_ = v_isSharedCheck_1300_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_it_1272_);
                    crate::leanh::lean_dec_ref(v_inst_1269_);
                    v___x_1303_ = crate::leanh::lean_box(2);
                    v___x_1304_ = crate::leanh::lean_apply_4(
                        v_lift_1271_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1276_,
                        v___x_1303_,
                    );
                    return v___x_1304_;
                }
            }
            1 => {
                v_str_1283_ = crate::leanh::lean_ctor_get(v_s_1270_, 0);
                v_startInclusive_1284_ = crate::leanh::lean_ctor_get(v_s_1270_, 1);
                v___x_1285_ = lean_nat_add(v_startInclusive_1284_, v_it_1272_);
                crate::leanh::lean_inc(v_startInclusive_1284_);
                crate::leanh::lean_inc_ref(v_str_1283_);
                if v_isShared_1282_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1281_, 2, v___x_1285_);
                    crate::leanh::lean_ctor_set(v___x_1281_, 1, v_startInclusive_1284_);
                    crate::leanh::lean_ctor_set(v___x_1281_, 0, v_str_1283_);
                    v___x_1287_ = v___x_1281_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1299_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 0, v_str_1283_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 1, v_startInclusive_1284_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1299_, 2, v___x_1285_);
                    v___x_1287_ = v_reuseFailAlloc_1299_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_1288_ = crate::leanh::lean_apply_2(
                    v_skipSuffixOfNonempty_x3f_1279_,
                    v___x_1287_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_1288_) == 0 {
                    v___x_1289_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1290_ = lean_nat_sub(v_it_1272_, v___x_1289_);
                    v___x_1291_ = l_String_Slice_posLE(v_s_1270_, v___x_1290_);
                    crate::leanh::lean_inc(v___x_1291_);
                    v___x_1292_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1292_, 0, v___x_1291_);
                    crate::leanh::lean_ctor_set(v___x_1292_, 1, v_it_1272_);
                    v___x_1293_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1293_, 0, v___x_1291_);
                    crate::leanh::lean_ctor_set(v___x_1293_, 1, v___x_1292_);
                    v___x_1294_ = crate::leanh::lean_apply_4(
                        v_lift_1271_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1276_,
                        v___x_1293_,
                    );
                    return v___x_1294_;
                } else {
                    v_val_1295_ = crate::leanh::lean_ctor_get(v___x_1288_, 0);
                    crate::leanh::lean_inc_n(v_val_1295_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1288_, 1);
                    v___x_1296_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1296_, 0, v_val_1295_);
                    crate::leanh::lean_ctor_set(v___x_1296_, 1, v_it_1272_);
                    v___x_1297_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1297_, 0, v_val_1295_);
                    crate::leanh::lean_ctor_set(v___x_1297_, 1, v___x_1296_);
                    v___x_1298_ = crate::leanh::lean_apply_4(
                        v_lift_1271_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
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
    mut v___y_1305_: *mut crate::leanh::LeanObject,
    mut v_inst_1306_: *mut crate::leanh::LeanObject,
    mut v_s_1307_: *mut crate::leanh::LeanObject,
    mut v_lift_1308_: *mut crate::leanh::LeanObject,
    mut v_it_1309_: *mut crate::leanh::LeanObject,
    mut v_acc_1310_: *mut crate::leanh::LeanObject,
    mut v_hP_1311_: *mut crate::leanh::LeanObject,
    mut v_recur_1312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1313_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1(v___y_1305_, v_inst_1306_, v_s_1307_, v_lift_1308_, v_it_1309_, v_acc_1310_, v_hP_1311_, v_recur_1312_);
    crate::leanh::lean_dec_ref(v_s_1307_);
    return v_res_1313_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0(
    mut v_inst_1314_: *mut crate::leanh::LeanObject,
    mut v_s_1315_: *mut crate::leanh::LeanObject,
    mut v_lift_1316_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1317_: *mut crate::leanh::LeanObject,
    mut v_Pl_1318_: *mut crate::leanh::LeanObject,
    mut v_it_1319_: *mut crate::leanh::LeanObject,
    mut v_init_1320_: *mut crate::leanh::LeanObject,
    mut v___y_1321_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1322_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__1___boxed as *mut core::ffi::c_void, 8, 4);
    crate::leanh::lean_closure_set(v___f_1322_, 0, v___y_1321_);
    crate::leanh::lean_closure_set(v___f_1322_, 1, v_inst_1314_);
    crate::leanh::lean_closure_set(v___f_1322_, 2, v_s_1315_);
    crate::leanh::lean_closure_set(v___f_1322_, 3, v_lift_1316_);
    v___x_1323_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1322_,
        v_it_1319_,
        v_init_1320_,
        crate::leanh::lean_box(0),
    );
    return v___x_1323_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg(
    mut v_s_1324_: *mut crate::leanh::LeanObject,
    mut v_inst_1325_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1326_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 8, 2);
    crate::leanh::lean_closure_set(v___f_1326_, 0, v_inst_1325_);
    crate::leanh::lean_closure_set(v___f_1326_, 1, v_s_1324_);
    return v___f_1326_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(
    mut v_00_u03c1_1327_: *mut crate::leanh::LeanObject,
    mut v_pat_1328_: *mut crate::leanh::LeanObject,
    mut v_s_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1331_ = crate::leanh::lean_alloc_closure(l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___redArg___lam__0 as *mut core::ffi::c_void, 8, 2);
    crate::leanh::lean_closure_set(v___f_1331_, 0, v_inst_1330_);
    crate::leanh::lean_closure_set(v___f_1331_, 1, v_s_1329_);
    return v___f_1331_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep___boxed(
    mut v_00_u03c1_1332_: *mut crate::leanh::LeanObject,
    mut v_pat_1333_: *mut crate::leanh::LeanObject,
    mut v_s_1334_: *mut crate::leanh::LeanObject,
    mut v_inst_1335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1336_ = l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_instIteratorLoopIdSearchStep(v_00_u03c1_1332_, v_pat_1333_, v_s_1334_, v_inst_1335_);
    crate::leanh::lean_dec(v_pat_1333_);
    return v_res_1336_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___redArg(
    mut v_pat_1337_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1338_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1338_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1338_, 1, v_pat_1337_);
    return v___x_1338_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(
    mut v_00_u03c1_1339_: *mut crate::leanh::LeanObject,
    mut v_pat_1340_: *mut crate::leanh::LeanObject,
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1342_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_Pattern_ToBackwardSearcher_DefaultBackwardSearcher_iter___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___x_1342_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1342_, 1, v_pat_1340_);
    return v___x_1342_;
}
pub unsafe fn l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation___boxed(
    mut v_00_u03c1_1343_: *mut crate::leanh::LeanObject,
    mut v_pat_1344_: *mut crate::leanh::LeanObject,
    mut v_inst_1345_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1346_ = l_String_Slice_Pattern_ToBackwardSearcher_defaultImplementation(
        v_00_u03c1_1343_,
        v_pat_1344_,
        v_inst_1345_,
    );
    crate::leanh::lean_dec_ref(v_inst_1345_);
    return v_res_1346_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Pattern_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Pattern_Basic(
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
pub unsafe fn initialize_Init_Data_String_Pattern_Basic(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Defs(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_IsEmpty(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Termination(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_OrderInstances(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Pattern_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Pattern_Basic(builtin);
}

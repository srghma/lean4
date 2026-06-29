// Lean compiler output
// Module: Init.Data.String.Iterate
// Imports: Init.Data.String.Basic Init.Data.String.FindPos Init.Data.Iterators.Combinators.FilterMap Init.Data.Iterators.Consumers.Loop Init.Omega Init.Data.Iterators.Consumers.Collect Init.Data.String.Lemmas.FindPos
use crate::r#gen::Init::Data::Iterators::Combinators::FilterMap::{
    initialize_Init_Data_Iterators_Combinators_FilterMap,
    runtime_initialize_Init_Data_Iterators_Combinators_FilterMap,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Collect::{
    initialize_Init_Data_Iterators_Consumers_Collect,
    runtime_initialize_Init_Data_Iterators_Consumers_Collect,
};
use crate::r#gen::Init::Data::Iterators::Consumers::Loop::{
    initialize_Init_Data_Iterators_Consumers_Loop,
    runtime_initialize_Init_Data_Iterators_Consumers_Loop,
};
use crate::r#gen::Init::Data::String::Basic::{
    initialize_Init_Data_String_Basic, runtime_initialize_Init_Data_String_Basic,
};
use crate::r#gen::Init::Data::String::FindPos::{
    initialize_Init_Data_String_FindPos, l_String_Slice_posLE,
    runtime_initialize_Init_Data_String_FindPos,
};
use crate::r#gen::Init::Data::String::Lemmas::FindPos::{
    initialize_Init_Data_String_Lemmas_FindPos, runtime_initialize_Init_Data_String_Lemmas_FindPos,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::WFExtrinsicFix::l_WellFounded_opaqueFix_u2083___redArg;
use crate::ffi::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::ffi::lean_string_get_byte_fast;
use crate::ffi::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
pub static l_String_Slice_instInhabitedByteIterator_default___closed__0_value:
    crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 1,
    m_capacity: 1,
    m_length: 0,
    m_data: [0],
};
static mut l_String_Slice_instInhabitedByteIterator_default___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instInhabitedByteIterator_default___closed__1_value:
    crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
            + 0) as u16,
        other: 3,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__0_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_instInhabitedByteIterator_default___closed__1:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instInhabitedByteIterator_default___closed__2_value:
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
        core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_instInhabitedByteIterator_default___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instInhabitedByteIterator_default: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instInhabitedByteIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_String_Slice_instInhabitedRevByteIterator___closed__0_value:
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
        core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
            as *mut crate::leanh::LeanObject,
        (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
    ],
};
static mut l_String_Slice_instInhabitedRevByteIterator___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedRevByteIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_String_Slice_instInhabitedRevByteIterator: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedRevByteIterator___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_String_Slice_instInhabitedPosIterator_default(
    mut v_s_909_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_910_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_910_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator_default___boxed(
    mut v_s_911_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_912_ = l_String_Slice_instInhabitedPosIterator_default(v_s_911_);
    crate::leanh::lean_dec_ref(v_s_911_);
    return v_res_912_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator(
    mut v_a_913_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_914_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_914_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator___boxed(
    mut v_a_915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_916_ = l_String_Slice_instInhabitedPosIterator(v_a_915_);
    crate::leanh::lean_dec_ref(v_a_915_);
    return v_res_916_;
}
pub unsafe fn l_String_Slice_positionsFrom___redArg(
    mut v_p_917_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_917_);
    return v_p_917_;
}
pub unsafe fn l_String_Slice_positionsFrom___redArg___boxed(
    mut v_p_918_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_919_ = l_String_Slice_positionsFrom___redArg(v_p_918_);
    crate::leanh::lean_dec(v_p_918_);
    return v_res_919_;
}
pub unsafe fn l_String_Slice_positionsFrom(
    mut v_s_920_: *mut crate::leanh::LeanObject,
    mut v_p_921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_921_);
    return v_p_921_;
}
pub unsafe fn l_String_Slice_positionsFrom___boxed(
    mut v_s_922_: *mut crate::leanh::LeanObject,
    mut v_p_923_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_924_ = l_String_Slice_positionsFrom(v_s_922_, v_p_923_);
    crate::leanh::lean_dec(v_p_923_);
    crate::leanh::lean_dec_ref(v_s_922_);
    return v_res_924_;
}
pub unsafe fn l_String_Slice_positions(
    mut v_s_925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_926_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_926_;
}
pub unsafe fn l_String_Slice_positions___boxed(
    mut v_s_927_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_928_ = l_String_Slice_positions(v_s_927_);
    crate::leanh::lean_dec_ref(v_s_927_);
    return v_res_928_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
    mut v_s_929_: *mut crate::leanh::LeanObject,
    mut v_inst_930_: *mut crate::leanh::LeanObject,
    mut v_x_931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    v_str_932_ = crate::leanh::lean_ctor_get(v_s_929_, 0);
    v_startInclusive_933_ = crate::leanh::lean_ctor_get(v_s_929_, 1);
    v_endExclusive_934_ = crate::leanh::lean_ctor_get(v_s_929_, 2);
    v___x_935_ = lean_nat_sub(v_endExclusive_934_, v_startInclusive_933_);
    v___x_936_ = lean_nat_dec_eq(v_x_931_, v___x_935_);
    crate::leanh::lean_dec(v___x_935_);
    if v___x_936_ == 0 {
        let mut v___x_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_937_ = lean_nat_add(v_startInclusive_933_, v_x_931_);
        v___x_938_ = lean_string_utf8_next_fast(v_str_932_, v___x_937_);
        crate::leanh::lean_dec(v___x_937_);
        v___x_939_ = lean_nat_sub(v___x_938_, v_startInclusive_933_);
        v___x_940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_940_, 0, v___x_939_);
        crate::leanh::lean_ctor_set(v___x_940_, 1, v_x_931_);
        v___x_941_ = crate::leanh::lean_apply_2(v_inst_930_, crate::leanh::lean_box(0), v___x_940_);
        return v___x_941_;
    } else {
        let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_x_931_);
        v___x_942_ = crate::leanh::lean_box(2);
        v___x_943_ = crate::leanh::lean_apply_2(v_inst_930_, crate::leanh::lean_box(0), v___x_942_);
        return v___x_943_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(
    mut v_s_944_: *mut crate::leanh::LeanObject,
    mut v_inst_945_: *mut crate::leanh::LeanObject,
    mut v_x_946_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_947_ = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
        v_s_944_,
        v_inst_945_,
        v_x_946_,
    );
    crate::leanh::lean_dec_ref(v_s_944_);
    return v_res_947_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(
    mut v_s_948_: *mut crate::leanh::LeanObject,
    mut v_inst_949_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_950_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_950_, 0, v_s_948_);
    crate::leanh::lean_closure_set(v___f_950_, 1, v_inst_949_);
    return v___f_950_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(
    mut v_m_951_: *mut crate::leanh::LeanObject,
    mut v_s_952_: *mut crate::leanh::LeanObject,
    mut v_inst_953_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_954_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_954_, 0, v_s_952_);
    crate::leanh::lean_closure_set(v___f_954_, 1, v_inst_953_);
    return v___f_954_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(
    mut v_m_955_: *mut crate::leanh::LeanObject,
    mut v_s_956_: *mut crate::leanh::LeanObject,
    mut v_inst_957_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_958_ = crate::leanh::lean_box(0);
    return v___x_958_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(
    mut v_m_959_: *mut crate::leanh::LeanObject,
    mut v_s_960_: *mut crate::leanh::LeanObject,
    mut v_inst_961_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_962_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(
            v_m_959_,
            v_s_960_,
            v_inst_961_,
        );
    crate::leanh::lean_dec(v_inst_961_);
    crate::leanh::lean_dec_ref(v_s_960_);
    return v_res_962_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(
    mut v_toPure_963_: *mut crate::leanh::LeanObject,
    mut v_recur_964_: *mut crate::leanh::LeanObject,
    mut v_it_965_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_966_) == 0 {
        let mut v_a_967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_965_);
        crate::leanh::lean_dec(v_recur_964_);
        v_a_967_ = crate::leanh::lean_ctor_get(v_____do__lift_966_, 0);
        crate::leanh::lean_inc(v_a_967_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_966_, 1);
        v___x_968_ = crate::leanh::lean_apply_2(v_toPure_963_, crate::leanh::lean_box(0), v_a_967_);
        return v___x_968_;
    } else {
        let mut v_a_969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_963_);
        v_a_969_ = crate::leanh::lean_ctor_get(v_____do__lift_966_, 0);
        crate::leanh::lean_inc(v_a_969_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_966_, 1);
        v___x_970_ = crate::leanh::lean_apply_4(
            v_recur_964_,
            v_it_965_,
            v_a_969_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_970_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(
    mut v_toPure_971_: *mut crate::leanh::LeanObject,
    mut v_recur_972_: *mut crate::leanh::LeanObject,
    mut v___y_973_: *mut crate::leanh::LeanObject,
    mut v_acc_974_: *mut crate::leanh::LeanObject,
    mut v_toBind_975_: *mut crate::leanh::LeanObject,
    mut v_s_976_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_976_) {
        0 => {
            let mut v_it_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_977_ = crate::leanh::lean_ctor_get(v_s_976_, 0);
            crate::leanh::lean_inc(v_it_977_);
            v_out_978_ = crate::leanh::lean_ctor_get(v_s_976_, 1);
            crate::leanh::lean_inc(v_out_978_);
            crate::leanh::lean_dec_ref_known(v_s_976_, 2);
            v___f_979_ = crate::leanh::lean_alloc_closure(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
            crate::leanh::lean_closure_set(v___f_979_, 0, v_toPure_971_);
            crate::leanh::lean_closure_set(v___f_979_, 1, v_recur_972_);
            crate::leanh::lean_closure_set(v___f_979_, 2, v_it_977_);
            v___x_980_ = crate::leanh::lean_apply_3(
                v___y_973_,
                v_out_978_,
                crate::leanh::lean_box(0),
                v_acc_974_,
            );
            v___x_981_ = crate::leanh::lean_apply_4(
                v_toBind_975_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_980_,
                v___f_979_,
            );
            return v___x_981_;
        }
        1 => {
            let mut v_it_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_975_);
            crate::leanh::lean_dec(v___y_973_);
            crate::leanh::lean_dec(v_toPure_971_);
            v_it_982_ = crate::leanh::lean_ctor_get(v_s_976_, 0);
            crate::leanh::lean_inc(v_it_982_);
            crate::leanh::lean_dec_ref_known(v_s_976_, 1);
            v___x_983_ = crate::leanh::lean_apply_4(
                v_recur_972_,
                v_it_982_,
                v_acc_974_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_983_;
        }
        _ => {
            let mut v___x_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_975_);
            crate::leanh::lean_dec(v___y_973_);
            crate::leanh::lean_dec(v_recur_972_);
            v___x_984_ =
                crate::leanh::lean_apply_2(v_toPure_971_, crate::leanh::lean_box(0), v_acc_974_);
            return v___x_984_;
        }
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
    mut v_s_985_: *mut crate::leanh::LeanObject,
    mut v_toPure_986_: *mut crate::leanh::LeanObject,
    mut v___y_987_: *mut crate::leanh::LeanObject,
    mut v_toBind_988_: *mut crate::leanh::LeanObject,
    mut v_toPure_989_: *mut crate::leanh::LeanObject,
    mut v_lift_990_: *mut crate::leanh::LeanObject,
    mut v_it_991_: *mut crate::leanh::LeanObject,
    mut v_acc_992_: *mut crate::leanh::LeanObject,
    mut v_hP_993_: *mut crate::leanh::LeanObject,
    mut v_recur_994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    v_str_995_ = crate::leanh::lean_ctor_get(v_s_985_, 0);
    v_startInclusive_996_ = crate::leanh::lean_ctor_get(v_s_985_, 1);
    v_endExclusive_997_ = crate::leanh::lean_ctor_get(v_s_985_, 2);
    v___f_998_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_998_, 0, v_toPure_986_);
    crate::leanh::lean_closure_set(v___f_998_, 1, v_recur_994_);
    crate::leanh::lean_closure_set(v___f_998_, 2, v___y_987_);
    crate::leanh::lean_closure_set(v___f_998_, 3, v_acc_992_);
    crate::leanh::lean_closure_set(v___f_998_, 4, v_toBind_988_);
    v___x_999_ = lean_nat_sub(v_endExclusive_997_, v_startInclusive_996_);
    v___x_1000_ = lean_nat_dec_eq(v_it_991_, v___x_999_);
    crate::leanh::lean_dec(v___x_999_);
    if v___x_1000_ == 0 {
        let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1001_ = lean_nat_add(v_startInclusive_996_, v_it_991_);
        v___x_1002_ = lean_string_utf8_next_fast(v_str_995_, v___x_1001_);
        crate::leanh::lean_dec(v___x_1001_);
        v___x_1003_ = lean_nat_sub(v___x_1002_, v_startInclusive_996_);
        v___x_1004_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1004_, 0, v___x_1003_);
        crate::leanh::lean_ctor_set(v___x_1004_, 1, v_it_991_);
        v___x_1005_ =
            crate::leanh::lean_apply_2(v_toPure_989_, crate::leanh::lean_box(0), v___x_1004_);
        v___x_1006_ = crate::leanh::lean_apply_4(
            v_lift_990_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_998_,
            v___x_1005_,
        );
        return v___x_1006_;
    } else {
        let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_it_991_);
        v___x_1007_ = crate::leanh::lean_box(2);
        v___x_1008_ =
            crate::leanh::lean_apply_2(v_toPure_989_, crate::leanh::lean_box(0), v___x_1007_);
        v___x_1009_ = crate::leanh::lean_apply_4(
            v_lift_990_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_998_,
            v___x_1008_,
        );
        return v___x_1009_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(
    mut v_s_1010_: *mut crate::leanh::LeanObject,
    mut v_toPure_1011_: *mut crate::leanh::LeanObject,
    mut v___y_1012_: *mut crate::leanh::LeanObject,
    mut v_toBind_1013_: *mut crate::leanh::LeanObject,
    mut v_toPure_1014_: *mut crate::leanh::LeanObject,
    mut v_lift_1015_: *mut crate::leanh::LeanObject,
    mut v_it_1016_: *mut crate::leanh::LeanObject,
    mut v_acc_1017_: *mut crate::leanh::LeanObject,
    mut v_hP_1018_: *mut crate::leanh::LeanObject,
    mut v_recur_1019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1020_ =
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
            v_s_1010_,
            v_toPure_1011_,
            v___y_1012_,
            v_toBind_1013_,
            v_toPure_1014_,
            v_lift_1015_,
            v_it_1016_,
            v_acc_1017_,
            v_hP_1018_,
            v_recur_1019_,
        );
    crate::leanh::lean_dec_ref(v_s_1010_);
    return v_res_1020_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(
    mut v_inst_1021_: *mut crate::leanh::LeanObject,
    mut v_s_1022_: *mut crate::leanh::LeanObject,
    mut v_toPure_1023_: *mut crate::leanh::LeanObject,
    mut v_lift_1024_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1025_: *mut crate::leanh::LeanObject,
    mut v_Pl_1026_: *mut crate::leanh::LeanObject,
    mut v_it_1027_: *mut crate::leanh::LeanObject,
    mut v_init_1028_: *mut crate::leanh::LeanObject,
    mut v___y_1029_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1030_ = crate::leanh::lean_ctor_get(v_inst_1021_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1030_);
    v_toBind_1031_ = crate::leanh::lean_ctor_get(v_inst_1021_, 1);
    crate::leanh::lean_inc(v_toBind_1031_);
    crate::leanh::lean_dec_ref(v_inst_1021_);
    v_toPure_1032_ = crate::leanh::lean_ctor_get(v_toApplicative_1030_, 1);
    crate::leanh::lean_inc(v_toPure_1032_);
    crate::leanh::lean_dec_ref(v_toApplicative_1030_);
    v___f_1033_ = crate::leanh::lean_alloc_closure(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 6);
    crate::leanh::lean_closure_set(v___f_1033_, 0, v_s_1022_);
    crate::leanh::lean_closure_set(v___f_1033_, 1, v_toPure_1032_);
    crate::leanh::lean_closure_set(v___f_1033_, 2, v___y_1029_);
    crate::leanh::lean_closure_set(v___f_1033_, 3, v_toBind_1031_);
    crate::leanh::lean_closure_set(v___f_1033_, 4, v_toPure_1023_);
    crate::leanh::lean_closure_set(v___f_1033_, 5, v_lift_1024_);
    v___x_1034_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1033_,
        v_it_1027_,
        v_init_1028_,
        crate::leanh::lean_box(0),
    );
    return v___x_1034_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
    mut v_s_1035_: *mut crate::leanh::LeanObject,
    mut v_inst_1036_: *mut crate::leanh::LeanObject,
    mut v_inst_1037_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1038_ = crate::leanh::lean_ctor_get(v_inst_1036_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1038_);
    crate::leanh::lean_dec_ref(v_inst_1036_);
    v_toPure_1039_ = crate::leanh::lean_ctor_get(v_toApplicative_1038_, 1);
    crate::leanh::lean_inc(v_toPure_1039_);
    crate::leanh::lean_dec_ref(v_toApplicative_1038_);
    v___f_1040_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1040_, 0, v_inst_1037_);
    crate::leanh::lean_closure_set(v___f_1040_, 1, v_s_1035_);
    crate::leanh::lean_closure_set(v___f_1040_, 2, v_toPure_1039_);
    return v___f_1040_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(
    mut v_m_1041_: *mut crate::leanh::LeanObject,
    mut v_n_1042_: *mut crate::leanh::LeanObject,
    mut v_s_1043_: *mut crate::leanh::LeanObject,
    mut v_inst_1044_: *mut crate::leanh::LeanObject,
    mut v_inst_1045_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
        v_s_1043_,
        v_inst_1044_,
        v_inst_1045_,
    );
    return v___x_1046_;
}
pub unsafe fn l_String_Slice_chars(
    mut v_s_1047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1048_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1048_;
}
pub unsafe fn l_String_Slice_chars___boxed(
    mut v_s_1049_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_String_Slice_chars(v_s_1049_);
    crate::leanh::lean_dec_ref(v_s_1049_);
    return v_res_1050_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
    mut v_s_1051_: *mut crate::leanh::LeanObject,
    mut v_a_1052_: *mut crate::leanh::LeanObject,
    mut v_b_1053_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1054_ = crate::leanh::lean_ctor_get(v_s_1051_, 0);
                v_startInclusive_1055_ = crate::leanh::lean_ctor_get(v_s_1051_, 1);
                v_endExclusive_1056_ = crate::leanh::lean_ctor_get(v_s_1051_, 2);
                v___x_1057_ = lean_nat_sub(v_endExclusive_1056_, v_startInclusive_1055_);
                v___x_1058_ = lean_nat_dec_eq(v_a_1052_, v___x_1057_);
                crate::leanh::lean_dec(v___x_1057_);
                if v___x_1058_ == 0 {
                    v___x_1059_ = lean_nat_add(v_startInclusive_1055_, v_a_1052_);
                    crate::leanh::lean_dec(v_a_1052_);
                    v___x_1060_ = lean_string_utf8_next_fast(v_str_1054_, v___x_1059_);
                    crate::leanh::lean_dec(v___x_1059_);
                    v___x_1061_ = lean_nat_sub(v___x_1060_, v_startInclusive_1055_);
                    v___x_1062_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1063_ = lean_nat_add(v_b_1053_, v___x_1062_);
                    crate::leanh::lean_dec(v_b_1053_);
                    v_a_1052_ = v___x_1061_;
                    v_b_1053_ = v___x_1063_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1052_);
                    return v_b_1053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(
    mut v_s_1065_: *mut crate::leanh::LeanObject,
    mut v_a_1066_: *mut crate::leanh::LeanObject,
    mut v_b_1067_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1065_, v_a_1066_, v_b_1067_,
    );
    crate::leanh::lean_dec_ref(v_s_1065_);
    return v_res_1068_;
}
pub unsafe fn l_String_Slice_length(
    mut v_s_1069_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1070_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1071_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1069_,
        v___x_1070_,
        v___x_1070_,
    );
    return v___x_1071_;
}
pub unsafe fn l_String_Slice_length___boxed(
    mut v_s_1072_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_String_Slice_length(v_s_1072_);
    crate::leanh::lean_dec_ref(v_s_1072_);
    return v_res_1073_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(
    mut v_s_1074_: *mut crate::leanh::LeanObject,
    mut v_inst_1075_: *mut crate::leanh::LeanObject,
    mut v_R_1076_: *mut crate::leanh::LeanObject,
    mut v_a_1077_: *mut crate::leanh::LeanObject,
    mut v_b_1078_: *mut crate::leanh::LeanObject,
    mut v_c_1079_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1074_, v_a_1077_, v_b_1078_,
    );
    return v___x_1080_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(
    mut v_s_1081_: *mut crate::leanh::LeanObject,
    mut v_inst_1082_: *mut crate::leanh::LeanObject,
    mut v_R_1083_: *mut crate::leanh::LeanObject,
    mut v_a_1084_: *mut crate::leanh::LeanObject,
    mut v_b_1085_: *mut crate::leanh::LeanObject,
    mut v_c_1086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(
        v_s_1081_,
        v_inst_1082_,
        v_R_1083_,
        v_a_1084_,
        v_b_1085_,
        v_c_1086_,
    );
    crate::leanh::lean_dec_ref(v_s_1081_);
    return v_res_1087_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator_default(
    mut v_s_1088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1089_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1089_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator_default___boxed(
    mut v_s_1090_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_String_Slice_instInhabitedRevPosIterator_default(v_s_1090_);
    crate::leanh::lean_dec_ref(v_s_1090_);
    return v_res_1091_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator(
    mut v_a_1092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1093_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1093_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator___boxed(
    mut v_a_1094_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_String_Slice_instInhabitedRevPosIterator(v_a_1094_);
    crate::leanh::lean_dec_ref(v_a_1094_);
    return v_res_1095_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___redArg(
    mut v_p_1096_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1096_);
    return v_p_1096_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___redArg___boxed(
    mut v_p_1097_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_String_Slice_revPositionsFrom___redArg(v_p_1097_);
    crate::leanh::lean_dec(v_p_1097_);
    return v_res_1098_;
}
pub unsafe fn l_String_Slice_revPositionsFrom(
    mut v_s_1099_: *mut crate::leanh::LeanObject,
    mut v_p_1100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1100_);
    return v_p_1100_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___boxed(
    mut v_s_1101_: *mut crate::leanh::LeanObject,
    mut v_p_1102_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_String_Slice_revPositionsFrom(v_s_1101_, v_p_1102_);
    crate::leanh::lean_dec(v_p_1102_);
    crate::leanh::lean_dec_ref(v_s_1101_);
    return v_res_1103_;
}
pub unsafe fn l_String_Slice_revPositions(
    mut v_s_1104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1105_ = crate::leanh::lean_ctor_get(v_s_1104_, 1);
    v_endExclusive_1106_ = crate::leanh::lean_ctor_get(v_s_1104_, 2);
    v___x_1107_ = lean_nat_sub(v_endExclusive_1106_, v_startInclusive_1105_);
    return v___x_1107_;
}
pub unsafe fn l_String_Slice_revPositions___boxed(
    mut v_s_1108_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_String_Slice_revPositions(v_s_1108_);
    crate::leanh::lean_dec_ref(v_s_1108_);
    return v_res_1109_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
    mut v_s_1110_: *mut crate::leanh::LeanObject,
    mut v_inst_1111_: *mut crate::leanh::LeanObject,
    mut v_x_1112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u8 = 0;
    v___x_1113_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1114_ = lean_nat_dec_eq(v_x_1112_, v___x_1113_);
    if v___x_1114_ == 0 {
        let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1115_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1116_ = lean_nat_sub(v_x_1112_, v___x_1115_);
        v_prevPos_1117_ = l_String_Slice_posLE(v_s_1110_, v___x_1116_);
        crate::leanh::lean_inc(v_prevPos_1117_);
        v___x_1118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1118_, 0, v_prevPos_1117_);
        crate::leanh::lean_ctor_set(v___x_1118_, 1, v_prevPos_1117_);
        v___x_1119_ =
            crate::leanh::lean_apply_2(v_inst_1111_, crate::leanh::lean_box(0), v___x_1118_);
        return v___x_1119_;
    } else {
        let mut v___x_1120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1120_ = crate::leanh::lean_box(2);
        v___x_1121_ =
            crate::leanh::lean_apply_2(v_inst_1111_, crate::leanh::lean_box(0), v___x_1120_);
        return v___x_1121_;
    }
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(
    mut v_s_1122_: *mut crate::leanh::LeanObject,
    mut v_inst_1123_: *mut crate::leanh::LeanObject,
    mut v_x_1124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1125_ =
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
            v_s_1122_,
            v_inst_1123_,
            v_x_1124_,
        );
    crate::leanh::lean_dec(v_x_1124_);
    crate::leanh::lean_dec_ref(v_s_1122_);
    return v_res_1125_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(
    mut v_s_1126_: *mut crate::leanh::LeanObject,
    mut v_inst_1127_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1128_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1128_, 0, v_s_1126_);
    crate::leanh::lean_closure_set(v___f_1128_, 1, v_inst_1127_);
    return v___f_1128_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(
    mut v_m_1129_: *mut crate::leanh::LeanObject,
    mut v_s_1130_: *mut crate::leanh::LeanObject,
    mut v_inst_1131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1132_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1132_, 0, v_s_1130_);
    crate::leanh::lean_closure_set(v___f_1132_, 1, v_inst_1131_);
    return v___f_1132_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(
    mut v_m_1133_: *mut crate::leanh::LeanObject,
    mut v_s_1134_: *mut crate::leanh::LeanObject,
    mut v_inst_1135_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1136_ = crate::leanh::lean_box(0);
    return v___x_1136_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(
    mut v_m_1137_: *mut crate::leanh::LeanObject,
    mut v_s_1138_: *mut crate::leanh::LeanObject,
    mut v_inst_1139_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1140_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(
            v_m_1137_,
            v_s_1138_,
            v_inst_1139_,
        );
    crate::leanh::lean_dec(v_inst_1139_);
    crate::leanh::lean_dec_ref(v_s_1138_);
    return v_res_1140_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
    mut v_toPure_1141_: *mut crate::leanh::LeanObject,
    mut v___y_1142_: *mut crate::leanh::LeanObject,
    mut v_toBind_1143_: *mut crate::leanh::LeanObject,
    mut v_s_1144_: *mut crate::leanh::LeanObject,
    mut v_toPure_1145_: *mut crate::leanh::LeanObject,
    mut v_lift_1146_: *mut crate::leanh::LeanObject,
    mut v_it_1147_: *mut crate::leanh::LeanObject,
    mut v_acc_1148_: *mut crate::leanh::LeanObject,
    mut v_hP_1149_: *mut crate::leanh::LeanObject,
    mut v_recur_1150_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v___f_1151_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1151_, 0, v_toPure_1141_);
    crate::leanh::lean_closure_set(v___f_1151_, 1, v_recur_1150_);
    crate::leanh::lean_closure_set(v___f_1151_, 2, v___y_1142_);
    crate::leanh::lean_closure_set(v___f_1151_, 3, v_acc_1148_);
    crate::leanh::lean_closure_set(v___f_1151_, 4, v_toBind_1143_);
    v___x_1152_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1153_ = lean_nat_dec_eq(v_it_1147_, v___x_1152_);
    if v___x_1153_ == 0 {
        let mut v___x_1154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1154_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1155_ = lean_nat_sub(v_it_1147_, v___x_1154_);
        v_prevPos_1156_ = l_String_Slice_posLE(v_s_1144_, v___x_1155_);
        crate::leanh::lean_inc(v_prevPos_1156_);
        v___x_1157_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_1157_, 0, v_prevPos_1156_);
        crate::leanh::lean_ctor_set(v___x_1157_, 1, v_prevPos_1156_);
        v___x_1158_ =
            crate::leanh::lean_apply_2(v_toPure_1145_, crate::leanh::lean_box(0), v___x_1157_);
        v___x_1159_ = crate::leanh::lean_apply_4(
            v_lift_1146_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_1151_,
            v___x_1158_,
        );
        return v___x_1159_;
    } else {
        let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1160_ = crate::leanh::lean_box(2);
        v___x_1161_ =
            crate::leanh::lean_apply_2(v_toPure_1145_, crate::leanh::lean_box(0), v___x_1160_);
        v___x_1162_ = crate::leanh::lean_apply_4(
            v_lift_1146_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___f_1151_,
            v___x_1161_,
        );
        return v___x_1162_;
    }
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(
    mut v_toPure_1163_: *mut crate::leanh::LeanObject,
    mut v___y_1164_: *mut crate::leanh::LeanObject,
    mut v_toBind_1165_: *mut crate::leanh::LeanObject,
    mut v_s_1166_: *mut crate::leanh::LeanObject,
    mut v_toPure_1167_: *mut crate::leanh::LeanObject,
    mut v_lift_1168_: *mut crate::leanh::LeanObject,
    mut v_it_1169_: *mut crate::leanh::LeanObject,
    mut v_acc_1170_: *mut crate::leanh::LeanObject,
    mut v_hP_1171_: *mut crate::leanh::LeanObject,
    mut v_recur_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ =
        l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
            v_toPure_1163_,
            v___y_1164_,
            v_toBind_1165_,
            v_s_1166_,
            v_toPure_1167_,
            v_lift_1168_,
            v_it_1169_,
            v_acc_1170_,
            v_hP_1171_,
            v_recur_1172_,
        );
    crate::leanh::lean_dec(v_it_1169_);
    crate::leanh::lean_dec_ref(v_s_1166_);
    return v_res_1173_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(
    mut v_inst_1174_: *mut crate::leanh::LeanObject,
    mut v_s_1175_: *mut crate::leanh::LeanObject,
    mut v_toPure_1176_: *mut crate::leanh::LeanObject,
    mut v_lift_1177_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1178_: *mut crate::leanh::LeanObject,
    mut v_Pl_1179_: *mut crate::leanh::LeanObject,
    mut v_it_1180_: *mut crate::leanh::LeanObject,
    mut v_init_1181_: *mut crate::leanh::LeanObject,
    mut v___y_1182_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1183_ = crate::leanh::lean_ctor_get(v_inst_1174_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1183_);
    v_toBind_1184_ = crate::leanh::lean_ctor_get(v_inst_1174_, 1);
    crate::leanh::lean_inc(v_toBind_1184_);
    crate::leanh::lean_dec_ref(v_inst_1174_);
    v_toPure_1185_ = crate::leanh::lean_ctor_get(v_toApplicative_1183_, 1);
    crate::leanh::lean_inc(v_toPure_1185_);
    crate::leanh::lean_dec_ref(v_toApplicative_1183_);
    v___f_1186_ = crate::leanh::lean_alloc_closure(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 6);
    crate::leanh::lean_closure_set(v___f_1186_, 0, v_toPure_1185_);
    crate::leanh::lean_closure_set(v___f_1186_, 1, v___y_1182_);
    crate::leanh::lean_closure_set(v___f_1186_, 2, v_toBind_1184_);
    crate::leanh::lean_closure_set(v___f_1186_, 3, v_s_1175_);
    crate::leanh::lean_closure_set(v___f_1186_, 4, v_toPure_1176_);
    crate::leanh::lean_closure_set(v___f_1186_, 5, v_lift_1177_);
    v___x_1187_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1186_,
        v_it_1180_,
        v_init_1181_,
        crate::leanh::lean_box(0),
    );
    return v___x_1187_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
    mut v_s_1188_: *mut crate::leanh::LeanObject,
    mut v_inst_1189_: *mut crate::leanh::LeanObject,
    mut v_inst_1190_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1191_ = crate::leanh::lean_ctor_get(v_inst_1189_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1191_);
    crate::leanh::lean_dec_ref(v_inst_1189_);
    v_toPure_1192_ = crate::leanh::lean_ctor_get(v_toApplicative_1191_, 1);
    crate::leanh::lean_inc(v_toPure_1192_);
    crate::leanh::lean_dec_ref(v_toApplicative_1191_);
    v___f_1193_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        9,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1193_, 0, v_inst_1190_);
    crate::leanh::lean_closure_set(v___f_1193_, 1, v_s_1188_);
    crate::leanh::lean_closure_set(v___f_1193_, 2, v_toPure_1192_);
    return v___f_1193_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(
    mut v_m_1194_: *mut crate::leanh::LeanObject,
    mut v_n_1195_: *mut crate::leanh::LeanObject,
    mut v_s_1196_: *mut crate::leanh::LeanObject,
    mut v_inst_1197_: *mut crate::leanh::LeanObject,
    mut v_inst_1198_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1199_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
        v_s_1196_,
        v_inst_1197_,
        v_inst_1198_,
    );
    return v___x_1199_;
}
pub unsafe fn l_String_Slice_revChars(
    mut v_s_1200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_String_Slice_revPositions(v_s_1200_);
    return v___x_1201_;
}
pub unsafe fn l_String_Slice_revChars___boxed(
    mut v_s_1202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_String_Slice_revChars(v_s_1202_);
    crate::leanh::lean_dec_ref(v_s_1202_);
    return v_res_1203_;
}
pub unsafe fn l_String_Slice_bytes(
    mut v_s_1213_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1214_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1215_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1215_, 0, v_s_1213_);
    crate::leanh::lean_ctor_set(v___x_1215_, 1, v___x_1214_);
    return v___x_1215_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(
    mut v_inst_1216_: *mut crate::leanh::LeanObject,
    mut v_x_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_str_1223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1218_ = crate::leanh::lean_ctor_get(v_x_1217_, 0);
                v_offset_1219_ = crate::leanh::lean_ctor_get(v_x_1217_, 1);
                v_isSharedCheck_1240_ = (!crate::leanh::lean_is_exclusive(v_x_1217_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1221_ = v_x_1217_;
                    v_isShared_1222_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_offset_1219_);
                    crate::leanh::lean_inc(v_s_1218_);
                    crate::leanh::lean_dec(v_x_1217_);
                    v___x_1221_ = crate::leanh::lean_box(0);
                    v_isShared_1222_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_str_1223_ = crate::leanh::lean_ctor_get(v_s_1218_, 0);
                crate::leanh::lean_inc_ref(v_str_1223_);
                v_startInclusive_1224_ = crate::leanh::lean_ctor_get(v_s_1218_, 1);
                crate::leanh::lean_inc(v_startInclusive_1224_);
                v_endExclusive_1225_ = crate::leanh::lean_ctor_get(v_s_1218_, 2);
                v___x_1226_ = lean_nat_sub(v_endExclusive_1225_, v_startInclusive_1224_);
                v___x_1227_ = lean_nat_dec_lt(v_offset_1219_, v___x_1226_);
                crate::leanh::lean_dec(v___x_1226_);
                if v___x_1227_ == 0 {
                    crate::leanh::lean_dec(v_startInclusive_1224_);
                    crate::leanh::lean_dec_ref(v_str_1223_);
                    crate::leanh::lean_del_object(v___x_1221_);
                    crate::leanh::lean_dec(v_offset_1219_);
                    crate::leanh::lean_dec_ref(v_s_1218_);
                    v___x_1228_ = crate::leanh::lean_box(2);
                    v___x_1229_ = crate::leanh::lean_apply_2(
                        v_inst_1216_,
                        crate::leanh::lean_box(0),
                        v___x_1228_,
                    );
                    return v___x_1229_;
                } else {
                    v___x_1230_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1231_ = lean_nat_add(v_offset_1219_, v___x_1230_);
                    if v_isShared_1222_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1221_, 1, v___x_1231_);
                        v___x_1233_ = v___x_1221_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1239_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_s_1218_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1231_);
                        v___x_1233_ = v_reuseFailAlloc_1239_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1234_ = lean_nat_add(v_startInclusive_1224_, v_offset_1219_);
                crate::leanh::lean_dec(v_offset_1219_);
                crate::leanh::lean_dec(v_startInclusive_1224_);
                v___x_1235_ = lean_string_get_byte_fast(v_str_1223_, v___x_1234_);
                crate::leanh::lean_dec_ref(v_str_1223_);
                v___x_1236_ = crate::leanh::lean_box((v___x_1235_) as usize);
                v___x_1237_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1237_, 0, v___x_1233_);
                crate::leanh::lean_ctor_set(v___x_1237_, 1, v___x_1236_);
                v___x_1238_ = crate::leanh::lean_apply_2(
                    v_inst_1216_,
                    crate::leanh::lean_box(0),
                    v___x_1237_,
                );
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(
    mut v_inst_1241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1242_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1242_, 0, v_inst_1241_);
    return v___f_1242_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure(
    mut v_m_1243_: *mut crate::leanh::LeanObject,
    mut v_inst_1244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1245_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1245_, 0, v_inst_1244_);
    return v___f_1245_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(
    mut v_m_1246_: *mut crate::leanh::LeanObject,
    mut v_inst_1247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1248_ = crate::leanh::lean_box(0);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(
    mut v_m_1249_: *mut crate::leanh::LeanObject,
    mut v_inst_1250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1251_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(
            v_m_1249_,
            v_inst_1250_,
        );
    crate::leanh::lean_dec(v_inst_1250_);
    return v_res_1251_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(
    mut v_toPure_1252_: *mut crate::leanh::LeanObject,
    mut v_recur_1253_: *mut crate::leanh::LeanObject,
    mut v_it_1254_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1255_) == 0 {
        let mut v_a_1256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_1254_);
        crate::leanh::lean_dec(v_recur_1253_);
        v_a_1256_ = crate::leanh::lean_ctor_get(v_____do__lift_1255_, 0);
        crate::leanh::lean_inc(v_a_1256_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1255_, 1);
        v___x_1257_ =
            crate::leanh::lean_apply_2(v_toPure_1252_, crate::leanh::lean_box(0), v_a_1256_);
        return v___x_1257_;
    } else {
        let mut v_a_1258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1252_);
        v_a_1258_ = crate::leanh::lean_ctor_get(v_____do__lift_1255_, 0);
        crate::leanh::lean_inc(v_a_1258_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1255_, 1);
        v___x_1259_ = crate::leanh::lean_apply_4(
            v_recur_1253_,
            v_it_1254_,
            v_a_1258_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1259_;
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(
    mut v_toPure_1260_: *mut crate::leanh::LeanObject,
    mut v_recur_1261_: *mut crate::leanh::LeanObject,
    mut v___y_1262_: *mut crate::leanh::LeanObject,
    mut v_acc_1263_: *mut crate::leanh::LeanObject,
    mut v_toBind_1264_: *mut crate::leanh::LeanObject,
    mut v_s_1265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1265_) {
        0 => {
            let mut v_it_1266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1266_ = crate::leanh::lean_ctor_get(v_s_1265_, 0);
            crate::leanh::lean_inc(v_it_1266_);
            v_out_1267_ = crate::leanh::lean_ctor_get(v_s_1265_, 1);
            crate::leanh::lean_inc(v_out_1267_);
            crate::leanh::lean_dec_ref_known(v_s_1265_, 2);
            v___f_1268_ = crate::leanh::lean_alloc_closure(
                l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_1268_, 0, v_toPure_1260_);
            crate::leanh::lean_closure_set(v___f_1268_, 1, v_recur_1261_);
            crate::leanh::lean_closure_set(v___f_1268_, 2, v_it_1266_);
            v___x_1269_ = crate::leanh::lean_apply_3(
                v___y_1262_,
                v_out_1267_,
                crate::leanh::lean_box(0),
                v_acc_1263_,
            );
            v___x_1270_ = crate::leanh::lean_apply_4(
                v_toBind_1264_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1269_,
                v___f_1268_,
            );
            return v___x_1270_;
        }
        1 => {
            let mut v_it_1271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1264_);
            crate::leanh::lean_dec(v___y_1262_);
            crate::leanh::lean_dec(v_toPure_1260_);
            v_it_1271_ = crate::leanh::lean_ctor_get(v_s_1265_, 0);
            crate::leanh::lean_inc(v_it_1271_);
            crate::leanh::lean_dec_ref_known(v_s_1265_, 1);
            v___x_1272_ = crate::leanh::lean_apply_4(
                v_recur_1261_,
                v_it_1271_,
                v_acc_1263_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1272_;
        }
        _ => {
            let mut v___x_1273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1264_);
            crate::leanh::lean_dec(v___y_1262_);
            crate::leanh::lean_dec(v_recur_1261_);
            v___x_1273_ =
                crate::leanh::lean_apply_2(v_toPure_1260_, crate::leanh::lean_box(0), v_acc_1263_);
            return v___x_1273_;
        }
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(
    mut v_toPure_1274_: *mut crate::leanh::LeanObject,
    mut v___y_1275_: *mut crate::leanh::LeanObject,
    mut v_toBind_1276_: *mut crate::leanh::LeanObject,
    mut v_toPure_1277_: *mut crate::leanh::LeanObject,
    mut v_lift_1278_: *mut crate::leanh::LeanObject,
    mut v_it_1279_: *mut crate::leanh::LeanObject,
    mut v_acc_1280_: *mut crate::leanh::LeanObject,
    mut v_hP_1281_: *mut crate::leanh::LeanObject,
    mut v_recur_1282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1287_: u8 = 0;
    let mut v_str_1288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut v___x_1303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1283_ = crate::leanh::lean_ctor_get(v_it_1279_, 0);
                v_offset_1284_ = crate::leanh::lean_ctor_get(v_it_1279_, 1);
                v_isSharedCheck_1308_ = (!crate::leanh::lean_is_exclusive(v_it_1279_)) as u8;
                if v_isSharedCheck_1308_ == 0 {
                    v___x_1286_ = v_it_1279_;
                    v_isShared_1287_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_offset_1284_);
                    crate::leanh::lean_inc(v_s_1283_);
                    crate::leanh::lean_dec(v_it_1279_);
                    v___x_1286_ = crate::leanh::lean_box(0);
                    v_isShared_1287_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_str_1288_ = crate::leanh::lean_ctor_get(v_s_1283_, 0);
                crate::leanh::lean_inc_ref(v_str_1288_);
                v_startInclusive_1289_ = crate::leanh::lean_ctor_get(v_s_1283_, 1);
                crate::leanh::lean_inc(v_startInclusive_1289_);
                v_endExclusive_1290_ = crate::leanh::lean_ctor_get(v_s_1283_, 2);
                v___f_1291_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1291_, 0, v_toPure_1274_);
                crate::leanh::lean_closure_set(v___f_1291_, 1, v_recur_1282_);
                crate::leanh::lean_closure_set(v___f_1291_, 2, v___y_1275_);
                crate::leanh::lean_closure_set(v___f_1291_, 3, v_acc_1280_);
                crate::leanh::lean_closure_set(v___f_1291_, 4, v_toBind_1276_);
                v___x_1292_ = lean_nat_sub(v_endExclusive_1290_, v_startInclusive_1289_);
                v___x_1293_ = lean_nat_dec_lt(v_offset_1284_, v___x_1292_);
                crate::leanh::lean_dec(v___x_1292_);
                if v___x_1293_ == 0 {
                    crate::leanh::lean_dec(v_startInclusive_1289_);
                    crate::leanh::lean_dec_ref(v_str_1288_);
                    crate::leanh::lean_del_object(v___x_1286_);
                    crate::leanh::lean_dec(v_offset_1284_);
                    crate::leanh::lean_dec_ref(v_s_1283_);
                    v___x_1294_ = crate::leanh::lean_box(2);
                    v___x_1295_ = crate::leanh::lean_apply_2(
                        v_toPure_1277_,
                        crate::leanh::lean_box(0),
                        v___x_1294_,
                    );
                    v___x_1296_ = crate::leanh::lean_apply_4(
                        v_lift_1278_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1291_,
                        v___x_1295_,
                    );
                    return v___x_1296_;
                } else {
                    v___x_1297_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_1298_ = lean_nat_add(v_offset_1284_, v___x_1297_);
                    if v_isShared_1287_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1286_, 1, v___x_1298_);
                        v___x_1300_ = v___x_1286_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1307_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_s_1283_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1298_);
                        v___x_1300_ = v_reuseFailAlloc_1307_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1301_ = lean_nat_add(v_startInclusive_1289_, v_offset_1284_);
                crate::leanh::lean_dec(v_offset_1284_);
                crate::leanh::lean_dec(v_startInclusive_1289_);
                v___x_1302_ = lean_string_get_byte_fast(v_str_1288_, v___x_1301_);
                crate::leanh::lean_dec_ref(v_str_1288_);
                v___x_1303_ = crate::leanh::lean_box((v___x_1302_) as usize);
                v___x_1304_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1304_, 0, v___x_1300_);
                crate::leanh::lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                v___x_1305_ = crate::leanh::lean_apply_2(
                    v_toPure_1277_,
                    crate::leanh::lean_box(0),
                    v___x_1304_,
                );
                v___x_1306_ = crate::leanh::lean_apply_4(
                    v_lift_1278_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1291_,
                    v___x_1305_,
                );
                return v___x_1306_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(
    mut v_inst_1309_: *mut crate::leanh::LeanObject,
    mut v_toPure_1310_: *mut crate::leanh::LeanObject,
    mut v_lift_1311_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1312_: *mut crate::leanh::LeanObject,
    mut v_Pl_1313_: *mut crate::leanh::LeanObject,
    mut v_it_1314_: *mut crate::leanh::LeanObject,
    mut v_init_1315_: *mut crate::leanh::LeanObject,
    mut v___y_1316_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1317_ = crate::leanh::lean_ctor_get(v_inst_1309_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1317_);
    v_toBind_1318_ = crate::leanh::lean_ctor_get(v_inst_1309_, 1);
    crate::leanh::lean_inc(v_toBind_1318_);
    crate::leanh::lean_dec_ref(v_inst_1309_);
    v_toPure_1319_ = crate::leanh::lean_ctor_get(v_toApplicative_1317_, 1);
    crate::leanh::lean_inc(v_toPure_1319_);
    crate::leanh::lean_dec_ref(v_toApplicative_1317_);
    v___f_1320_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1320_, 0, v_toPure_1319_);
    crate::leanh::lean_closure_set(v___f_1320_, 1, v___y_1316_);
    crate::leanh::lean_closure_set(v___f_1320_, 2, v_toBind_1318_);
    crate::leanh::lean_closure_set(v___f_1320_, 3, v_toPure_1310_);
    crate::leanh::lean_closure_set(v___f_1320_, 4, v_lift_1311_);
    v___x_1321_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1320_,
        v_it_1314_,
        v_init_1315_,
        crate::leanh::lean_box(0),
    );
    return v___x_1321_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(
    mut v_inst_1322_: *mut crate::leanh::LeanObject,
    mut v_inst_1323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1324_ = crate::leanh::lean_ctor_get(v_inst_1322_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1324_);
    crate::leanh::lean_dec_ref(v_inst_1322_);
    v_toPure_1325_ = crate::leanh::lean_ctor_get(v_toApplicative_1324_, 1);
    crate::leanh::lean_inc(v_toPure_1325_);
    crate::leanh::lean_dec_ref(v_toApplicative_1324_);
    v___f_1326_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1326_, 0, v_inst_1323_);
    crate::leanh::lean_closure_set(v___f_1326_, 1, v_toPure_1325_);
    return v___f_1326_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(
    mut v_m_1327_: *mut crate::leanh::LeanObject,
    mut v_n_1328_: *mut crate::leanh::LeanObject,
    mut v_inst_1329_: *mut crate::leanh::LeanObject,
    mut v_inst_1330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(
        v_inst_1329_,
        v_inst_1330_,
    );
    return v___x_1331_;
}
pub unsafe fn l_String_Slice_revBytes(
    mut v_s_1332_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_startInclusive_1333_ = crate::leanh::lean_ctor_get(v_s_1332_, 1);
    v_endExclusive_1334_ = crate::leanh::lean_ctor_get(v_s_1332_, 2);
    v___x_1335_ = lean_nat_sub(v_endExclusive_1334_, v_startInclusive_1333_);
    v___x_1336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1336_, 0, v_s_1332_);
    crate::leanh::lean_ctor_set(v___x_1336_, 1, v___x_1335_);
    return v___x_1336_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(
    mut v_inst_1341_: *mut crate::leanh::LeanObject,
    mut v_x_1342_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v_str_1350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_1353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1343_ = crate::leanh::lean_ctor_get(v_x_1342_, 0);
                v_offset_1344_ = crate::leanh::lean_ctor_get(v_x_1342_, 1);
                v_isSharedCheck_1364_ = (!crate::leanh::lean_is_exclusive(v_x_1342_)) as u8;
                if v_isSharedCheck_1364_ == 0 {
                    v___x_1346_ = v_x_1342_;
                    v_isShared_1347_ = v_isSharedCheck_1364_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_offset_1344_);
                    crate::leanh::lean_inc(v_s_1343_);
                    crate::leanh::lean_dec(v_x_1342_);
                    v___x_1346_ = crate::leanh::lean_box(0);
                    v_isShared_1347_ = v_isSharedCheck_1364_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1348_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1349_ = lean_nat_dec_eq(v_offset_1344_, v___x_1348_);
                if v___x_1349_ == 0 {
                    v_str_1350_ = crate::leanh::lean_ctor_get(v_s_1343_, 0);
                    crate::leanh::lean_inc_ref(v_str_1350_);
                    v_startInclusive_1351_ = crate::leanh::lean_ctor_get(v_s_1343_, 1);
                    crate::leanh::lean_inc(v_startInclusive_1351_);
                    v___x_1352_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_nextOffset_1353_ = lean_nat_sub(v_offset_1344_, v___x_1352_);
                    crate::leanh::lean_dec(v_offset_1344_);
                    crate::leanh::lean_inc(v_nextOffset_1353_);
                    if v_isShared_1347_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1346_, 1, v_nextOffset_1353_);
                        v___x_1355_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1361_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_s_1343_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_nextOffset_1353_);
                        v___x_1355_ = v_reuseFailAlloc_1361_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1346_);
                    crate::leanh::lean_dec(v_offset_1344_);
                    crate::leanh::lean_dec_ref(v_s_1343_);
                    v___x_1362_ = crate::leanh::lean_box(2);
                    v___x_1363_ = crate::leanh::lean_apply_2(
                        v_inst_1341_,
                        crate::leanh::lean_box(0),
                        v___x_1362_,
                    );
                    return v___x_1363_;
                }
            }
            2 => {
                v___x_1356_ = lean_nat_add(v_startInclusive_1351_, v_nextOffset_1353_);
                crate::leanh::lean_dec(v_nextOffset_1353_);
                crate::leanh::lean_dec(v_startInclusive_1351_);
                v___x_1357_ = lean_string_get_byte_fast(v_str_1350_, v___x_1356_);
                crate::leanh::lean_dec_ref(v_str_1350_);
                v___x_1358_ = crate::leanh::lean_box((v___x_1357_) as usize);
                v___x_1359_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1359_, 0, v___x_1355_);
                crate::leanh::lean_ctor_set(v___x_1359_, 1, v___x_1358_);
                v___x_1360_ = crate::leanh::lean_apply_2(
                    v_inst_1341_,
                    crate::leanh::lean_box(0),
                    v___x_1359_,
                );
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(
    mut v_inst_1365_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1366_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1366_, 0, v_inst_1365_);
    return v___f_1366_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(
    mut v_m_1367_: *mut crate::leanh::LeanObject,
    mut v_inst_1368_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1369_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1369_, 0, v_inst_1368_);
    return v___f_1369_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(
    mut v_m_1370_: *mut crate::leanh::LeanObject,
    mut v_inst_1371_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1372_ = crate::leanh::lean_box(0);
    return v___x_1372_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(
    mut v_m_1373_: *mut crate::leanh::LeanObject,
    mut v_inst_1374_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(
            v_m_1373_,
            v_inst_1374_,
        );
    crate::leanh::lean_dec(v_inst_1374_);
    return v_res_1375_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(
    mut v_toPure_1376_: *mut crate::leanh::LeanObject,
    mut v_recur_1377_: *mut crate::leanh::LeanObject,
    mut v_it_1378_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1379_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1379_) == 0 {
        let mut v_a_1380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v_it_1378_);
        crate::leanh::lean_dec(v_recur_1377_);
        v_a_1380_ = crate::leanh::lean_ctor_get(v_____do__lift_1379_, 0);
        crate::leanh::lean_inc(v_a_1380_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1379_, 1);
        v___x_1381_ =
            crate::leanh::lean_apply_2(v_toPure_1376_, crate::leanh::lean_box(0), v_a_1380_);
        return v___x_1381_;
    } else {
        let mut v_a_1382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1376_);
        v_a_1382_ = crate::leanh::lean_ctor_get(v_____do__lift_1379_, 0);
        crate::leanh::lean_inc(v_a_1382_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1379_, 1);
        v___x_1383_ = crate::leanh::lean_apply_4(
            v_recur_1377_,
            v_it_1378_,
            v_a_1382_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1383_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(
    mut v_toPure_1384_: *mut crate::leanh::LeanObject,
    mut v_recur_1385_: *mut crate::leanh::LeanObject,
    mut v___y_1386_: *mut crate::leanh::LeanObject,
    mut v_acc_1387_: *mut crate::leanh::LeanObject,
    mut v_toBind_1388_: *mut crate::leanh::LeanObject,
    mut v_s_1389_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    match crate::leanh::lean_obj_tag(v_s_1389_) {
        0 => {
            let mut v_it_1390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v_out_1391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___f_1392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v_it_1390_ = crate::leanh::lean_ctor_get(v_s_1389_, 0);
            crate::leanh::lean_inc(v_it_1390_);
            v_out_1391_ = crate::leanh::lean_ctor_get(v_s_1389_, 1);
            crate::leanh::lean_inc(v_out_1391_);
            crate::leanh::lean_dec_ref_known(v_s_1389_, 2);
            v___f_1392_ = crate::leanh::lean_alloc_closure(
                l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            crate::leanh::lean_closure_set(v___f_1392_, 0, v_toPure_1384_);
            crate::leanh::lean_closure_set(v___f_1392_, 1, v_recur_1385_);
            crate::leanh::lean_closure_set(v___f_1392_, 2, v_it_1390_);
            v___x_1393_ = crate::leanh::lean_apply_3(
                v___y_1386_,
                v_out_1391_,
                crate::leanh::lean_box(0),
                v_acc_1387_,
            );
            v___x_1394_ = crate::leanh::lean_apply_4(
                v_toBind_1388_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
                v___x_1393_,
                v___f_1392_,
            );
            return v___x_1394_;
        }
        1 => {
            let mut v_it_1395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1388_);
            crate::leanh::lean_dec(v___y_1386_);
            crate::leanh::lean_dec(v_toPure_1384_);
            v_it_1395_ = crate::leanh::lean_ctor_get(v_s_1389_, 0);
            crate::leanh::lean_inc(v_it_1395_);
            crate::leanh::lean_dec_ref_known(v_s_1389_, 1);
            v___x_1396_ = crate::leanh::lean_apply_4(
                v_recur_1385_,
                v_it_1395_,
                v_acc_1387_,
                crate::leanh::lean_box(0),
                crate::leanh::lean_box(0),
            );
            return v___x_1396_;
        }
        _ => {
            let mut v___x_1397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec(v_toBind_1388_);
            crate::leanh::lean_dec(v___y_1386_);
            crate::leanh::lean_dec(v_recur_1385_);
            v___x_1397_ =
                crate::leanh::lean_apply_2(v_toPure_1384_, crate::leanh::lean_box(0), v_acc_1387_);
            return v___x_1397_;
        }
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(
    mut v_toPure_1398_: *mut crate::leanh::LeanObject,
    mut v___y_1399_: *mut crate::leanh::LeanObject,
    mut v_toBind_1400_: *mut crate::leanh::LeanObject,
    mut v_toPure_1401_: *mut crate::leanh::LeanObject,
    mut v_lift_1402_: *mut crate::leanh::LeanObject,
    mut v_it_1403_: *mut crate::leanh::LeanObject,
    mut v_acc_1404_: *mut crate::leanh::LeanObject,
    mut v_hP_1405_: *mut crate::leanh::LeanObject,
    mut v_recur_1406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_s_1407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_offset_1408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___f_1412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_str_1415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_1418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1407_ = crate::leanh::lean_ctor_get(v_it_1403_, 0);
                v_offset_1408_ = crate::leanh::lean_ctor_get(v_it_1403_, 1);
                v_isSharedCheck_1431_ = (!crate::leanh::lean_is_exclusive(v_it_1403_)) as u8;
                if v_isSharedCheck_1431_ == 0 {
                    v___x_1410_ = v_it_1403_;
                    v_isShared_1411_ = v_isSharedCheck_1431_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_offset_1408_);
                    crate::leanh::lean_inc(v_s_1407_);
                    crate::leanh::lean_dec(v_it_1403_);
                    v___x_1410_ = crate::leanh::lean_box(0);
                    v_isShared_1411_ = v_isSharedCheck_1431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1412_ = crate::leanh::lean_alloc_closure(
                    l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                crate::leanh::lean_closure_set(v___f_1412_, 0, v_toPure_1398_);
                crate::leanh::lean_closure_set(v___f_1412_, 1, v_recur_1406_);
                crate::leanh::lean_closure_set(v___f_1412_, 2, v___y_1399_);
                crate::leanh::lean_closure_set(v___f_1412_, 3, v_acc_1404_);
                crate::leanh::lean_closure_set(v___f_1412_, 4, v_toBind_1400_);
                v___x_1413_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_1414_ = lean_nat_dec_eq(v_offset_1408_, v___x_1413_);
                if v___x_1414_ == 0 {
                    v_str_1415_ = crate::leanh::lean_ctor_get(v_s_1407_, 0);
                    crate::leanh::lean_inc_ref(v_str_1415_);
                    v_startInclusive_1416_ = crate::leanh::lean_ctor_get(v_s_1407_, 1);
                    crate::leanh::lean_inc(v_startInclusive_1416_);
                    v___x_1417_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_nextOffset_1418_ = lean_nat_sub(v_offset_1408_, v___x_1417_);
                    crate::leanh::lean_dec(v_offset_1408_);
                    crate::leanh::lean_inc(v_nextOffset_1418_);
                    if v_isShared_1411_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1410_, 1, v_nextOffset_1418_);
                        v___x_1420_ = v___x_1410_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1427_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_s_1407_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_nextOffset_1418_);
                        v___x_1420_ = v_reuseFailAlloc_1427_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1410_);
                    crate::leanh::lean_dec(v_offset_1408_);
                    crate::leanh::lean_dec_ref(v_s_1407_);
                    v___x_1428_ = crate::leanh::lean_box(2);
                    v___x_1429_ = crate::leanh::lean_apply_2(
                        v_toPure_1401_,
                        crate::leanh::lean_box(0),
                        v___x_1428_,
                    );
                    v___x_1430_ = crate::leanh::lean_apply_4(
                        v_lift_1402_,
                        crate::leanh::lean_box(0),
                        crate::leanh::lean_box(0),
                        v___f_1412_,
                        v___x_1429_,
                    );
                    return v___x_1430_;
                }
            }
            2 => {
                v___x_1421_ = lean_nat_add(v_startInclusive_1416_, v_nextOffset_1418_);
                crate::leanh::lean_dec(v_nextOffset_1418_);
                crate::leanh::lean_dec(v_startInclusive_1416_);
                v___x_1422_ = lean_string_get_byte_fast(v_str_1415_, v___x_1421_);
                crate::leanh::lean_dec_ref(v_str_1415_);
                v___x_1423_ = crate::leanh::lean_box((v___x_1422_) as usize);
                v___x_1424_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1424_, 0, v___x_1420_);
                crate::leanh::lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                v___x_1425_ = crate::leanh::lean_apply_2(
                    v_toPure_1401_,
                    crate::leanh::lean_box(0),
                    v___x_1424_,
                );
                v___x_1426_ = crate::leanh::lean_apply_4(
                    v_lift_1402_,
                    crate::leanh::lean_box(0),
                    crate::leanh::lean_box(0),
                    v___f_1412_,
                    v___x_1425_,
                );
                return v___x_1426_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3(
    mut v_inst_1432_: *mut crate::leanh::LeanObject,
    mut v_toPure_1433_: *mut crate::leanh::LeanObject,
    mut v_lift_1434_: *mut crate::leanh::LeanObject,
    mut v_00_u03b3_1435_: *mut crate::leanh::LeanObject,
    mut v_Pl_1436_: *mut crate::leanh::LeanObject,
    mut v_it_1437_: *mut crate::leanh::LeanObject,
    mut v_init_1438_: *mut crate::leanh::LeanObject,
    mut v___y_1439_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1440_ = crate::leanh::lean_ctor_get(v_inst_1432_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1440_);
    v_toBind_1441_ = crate::leanh::lean_ctor_get(v_inst_1432_, 1);
    crate::leanh::lean_inc(v_toBind_1441_);
    crate::leanh::lean_dec_ref(v_inst_1432_);
    v_toPure_1442_ = crate::leanh::lean_ctor_get(v_toApplicative_1440_, 1);
    crate::leanh::lean_inc(v_toPure_1442_);
    crate::leanh::lean_dec_ref(v_toApplicative_1440_);
    v___f_1443_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1443_, 0, v_toPure_1442_);
    crate::leanh::lean_closure_set(v___f_1443_, 1, v___y_1439_);
    crate::leanh::lean_closure_set(v___f_1443_, 2, v_toBind_1441_);
    crate::leanh::lean_closure_set(v___f_1443_, 3, v_toPure_1433_);
    crate::leanh::lean_closure_set(v___f_1443_, 4, v_lift_1434_);
    v___x_1444_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1443_,
        v_it_1437_,
        v_init_1438_,
        crate::leanh::lean_box(0),
    );
    return v___x_1444_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(
    mut v_inst_1445_: *mut crate::leanh::LeanObject,
    mut v_inst_1446_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1447_ = crate::leanh::lean_ctor_get(v_inst_1445_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1447_);
    crate::leanh::lean_dec_ref(v_inst_1445_);
    v_toPure_1448_ = crate::leanh::lean_ctor_get(v_toApplicative_1447_, 1);
    crate::leanh::lean_inc(v_toPure_1448_);
    crate::leanh::lean_dec_ref(v_toApplicative_1447_);
    v___f_1449_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1449_, 0, v_inst_1446_);
    crate::leanh::lean_closure_set(v___f_1449_, 1, v_toPure_1448_);
    return v___f_1449_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(
    mut v_m_1450_: *mut crate::leanh::LeanObject,
    mut v_n_1451_: *mut crate::leanh::LeanObject,
    mut v_inst_1452_: *mut crate::leanh::LeanObject,
    mut v_inst_1453_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1454_ = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(
        v_inst_1452_,
        v_inst_1453_,
    );
    return v___x_1454_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(
    mut v_toPure_1455_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1456_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1457_ = crate::leanh::lean_apply_2(
        v_toPure_1455_,
        crate::leanh::lean_box(0),
        v_____do__lift_1456_,
    );
    return v___x_1457_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(
    mut v_toPure_1458_: *mut crate::leanh::LeanObject,
    mut v_recur_1459_: *mut crate::leanh::LeanObject,
    mut v___x_1460_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_1461_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_1461_) == 0 {
        let mut v_a_1462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v___x_1460_);
        crate::leanh::lean_dec(v_recur_1459_);
        v_a_1462_ = crate::leanh::lean_ctor_get(v_____do__lift_1461_, 0);
        crate::leanh::lean_inc(v_a_1462_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1461_, 1);
        v___x_1463_ =
            crate::leanh::lean_apply_2(v_toPure_1458_, crate::leanh::lean_box(0), v_a_1462_);
        return v___x_1463_;
    } else {
        let mut v_a_1464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_toPure_1458_);
        v_a_1464_ = crate::leanh::lean_ctor_get(v_____do__lift_1461_, 0);
        crate::leanh::lean_inc(v_a_1464_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_1461_, 1);
        v___x_1465_ = crate::leanh::lean_apply_4(
            v_recur_1459_,
            v___x_1460_,
            v_a_1464_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1465_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(
    mut v_s_1466_: *mut crate::leanh::LeanObject,
    mut v_toPure_1467_: *mut crate::leanh::LeanObject,
    mut v_f_1468_: *mut crate::leanh::LeanObject,
    mut v_toBind_1469_: *mut crate::leanh::LeanObject,
    mut v___f_1470_: *mut crate::leanh::LeanObject,
    mut v_it_1471_: *mut crate::leanh::LeanObject,
    mut v_acc_1472_: *mut crate::leanh::LeanObject,
    mut v_hP_1473_: *mut crate::leanh::LeanObject,
    mut v_recur_1474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    v_str_1475_ = crate::leanh::lean_ctor_get(v_s_1466_, 0);
    v_startInclusive_1476_ = crate::leanh::lean_ctor_get(v_s_1466_, 1);
    v_endExclusive_1477_ = crate::leanh::lean_ctor_get(v_s_1466_, 2);
    v___x_1478_ = lean_nat_sub(v_endExclusive_1477_, v_startInclusive_1476_);
    v___x_1479_ = lean_nat_dec_eq(v_it_1471_, v___x_1478_);
    crate::leanh::lean_dec(v___x_1478_);
    if v___x_1479_ == 0 {
        let mut v___x_1480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: u32 = 0;
        let mut v___x_1485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1480_ = lean_nat_add(v_startInclusive_1476_, v_it_1471_);
        v___x_1481_ = lean_string_utf8_next_fast(v_str_1475_, v___x_1480_);
        v___x_1482_ = lean_nat_sub(v___x_1481_, v_startInclusive_1476_);
        v___f_1483_ = crate::leanh::lean_alloc_closure(
            l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1483_, 0, v_toPure_1467_);
        crate::leanh::lean_closure_set(v___f_1483_, 1, v_recur_1474_);
        crate::leanh::lean_closure_set(v___f_1483_, 2, v___x_1482_);
        v___x_1484_ = lean_string_utf8_get_fast(v_str_1475_, v___x_1480_);
        crate::leanh::lean_dec(v___x_1480_);
        v___x_1485_ = crate::leanh::lean_box_uint32(v___x_1484_);
        v___x_1486_ = crate::leanh::lean_apply_2(v_f_1468_, v___x_1485_, v_acc_1472_);
        crate::leanh::lean_inc(v_toBind_1469_);
        v___x_1487_ = crate::leanh::lean_apply_4(
            v_toBind_1469_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1486_,
            v___f_1470_,
        );
        v___x_1488_ = crate::leanh::lean_apply_4(
            v_toBind_1469_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1487_,
            v___f_1483_,
        );
        return v___x_1488_;
    } else {
        let mut v___x_1489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_recur_1474_);
        crate::leanh::lean_dec(v___f_1470_);
        crate::leanh::lean_dec(v_toBind_1469_);
        crate::leanh::lean_dec(v_f_1468_);
        v___x_1489_ =
            crate::leanh::lean_apply_2(v_toPure_1467_, crate::leanh::lean_box(0), v_acc_1472_);
        return v___x_1489_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(
    mut v_s_1490_: *mut crate::leanh::LeanObject,
    mut v_toPure_1491_: *mut crate::leanh::LeanObject,
    mut v_f_1492_: *mut crate::leanh::LeanObject,
    mut v_toBind_1493_: *mut crate::leanh::LeanObject,
    mut v___f_1494_: *mut crate::leanh::LeanObject,
    mut v_it_1495_: *mut crate::leanh::LeanObject,
    mut v_acc_1496_: *mut crate::leanh::LeanObject,
    mut v_hP_1497_: *mut crate::leanh::LeanObject,
    mut v_recur_1498_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1499_ = l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(
        v_s_1490_,
        v_toPure_1491_,
        v_f_1492_,
        v_toBind_1493_,
        v___f_1494_,
        v_it_1495_,
        v_acc_1496_,
        v_hP_1497_,
        v_recur_1498_,
    );
    crate::leanh::lean_dec(v_it_1495_);
    crate::leanh::lean_dec_ref(v_s_1490_);
    return v_res_1499_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(
    mut v_inst_1500_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1501_: *mut crate::leanh::LeanObject,
    mut v_s_1502_: *mut crate::leanh::LeanObject,
    mut v_b_1503_: *mut crate::leanh::LeanObject,
    mut v_f_1504_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1505_ = crate::leanh::lean_ctor_get(v_inst_1500_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1505_);
    v_toBind_1506_ = crate::leanh::lean_ctor_get(v_inst_1500_, 1);
    crate::leanh::lean_inc(v_toBind_1506_);
    crate::leanh::lean_dec_ref(v_inst_1500_);
    v_toPure_1507_ = crate::leanh::lean_ctor_get(v_toApplicative_1505_, 1);
    crate::leanh::lean_inc_n(v_toPure_1507_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1505_);
    v___x_1508_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_1509_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1509_, 0, v_toPure_1507_);
    v___f_1510_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        5,
    );
    crate::leanh::lean_closure_set(v___f_1510_, 0, v_s_1502_);
    crate::leanh::lean_closure_set(v___f_1510_, 1, v_toPure_1507_);
    crate::leanh::lean_closure_set(v___f_1510_, 2, v_f_1504_);
    crate::leanh::lean_closure_set(v___f_1510_, 3, v_toBind_1506_);
    crate::leanh::lean_closure_set(v___f_1510_, 4, v___f_1509_);
    v___x_1511_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1510_,
        v___x_1508_,
        v_b_1503_,
        crate::leanh::lean_box(0),
    );
    return v___x_1511_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(
    mut v_inst_1512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1513_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1513_, 0, v_inst_1512_);
    return v___f_1513_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad(
    mut v_m_1514_: *mut crate::leanh::LeanObject,
    mut v_inst_1515_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1516_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1516_, 0, v_inst_1515_);
    return v___f_1516_;
}
pub unsafe fn l_String_Slice_foldl___redArg___lam__0(
    mut v_s_1517_: *mut crate::leanh::LeanObject,
    mut v_f_1518_: *mut crate::leanh::LeanObject,
    mut v_it_1519_: *mut crate::leanh::LeanObject,
    mut v_acc_1520_: *mut crate::leanh::LeanObject,
    mut v_hP_1521_: *mut crate::leanh::LeanObject,
    mut v_recur_1522_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_str_1523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    v_str_1523_ = crate::leanh::lean_ctor_get(v_s_1517_, 0);
    v_startInclusive_1524_ = crate::leanh::lean_ctor_get(v_s_1517_, 1);
    v_endExclusive_1525_ = crate::leanh::lean_ctor_get(v_s_1517_, 2);
    v___x_1526_ = lean_nat_sub(v_endExclusive_1525_, v_startInclusive_1524_);
    v___x_1527_ = lean_nat_dec_eq(v_it_1519_, v___x_1526_);
    crate::leanh::lean_dec(v___x_1526_);
    if v___x_1527_ == 0 {
        let mut v___x_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: u32 = 0;
        let mut v___x_1532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1528_ = lean_nat_add(v_startInclusive_1524_, v_it_1519_);
        v___x_1529_ = lean_string_utf8_next_fast(v_str_1523_, v___x_1528_);
        v___x_1530_ = lean_nat_sub(v___x_1529_, v_startInclusive_1524_);
        v___x_1531_ = lean_string_utf8_get_fast(v_str_1523_, v___x_1528_);
        crate::leanh::lean_dec(v___x_1528_);
        v___x_1532_ = crate::leanh::lean_box_uint32(v___x_1531_);
        v___x_1533_ = crate::leanh::lean_apply_2(v_f_1518_, v_acc_1520_, v___x_1532_);
        v___x_1534_ = crate::leanh::lean_apply_4(
            v_recur_1522_,
            v___x_1530_,
            v___x_1533_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1534_;
    } else {
        crate::leanh::lean_dec(v_recur_1522_);
        crate::leanh::lean_dec(v_f_1518_);
        return v_acc_1520_;
    }
}
pub unsafe fn l_String_Slice_foldl___redArg___lam__0___boxed(
    mut v_s_1535_: *mut crate::leanh::LeanObject,
    mut v_f_1536_: *mut crate::leanh::LeanObject,
    mut v_it_1537_: *mut crate::leanh::LeanObject,
    mut v_acc_1538_: *mut crate::leanh::LeanObject,
    mut v_hP_1539_: *mut crate::leanh::LeanObject,
    mut v_recur_1540_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_String_Slice_foldl___redArg___lam__0(
        v_s_1535_,
        v_f_1536_,
        v_it_1537_,
        v_acc_1538_,
        v_hP_1539_,
        v_recur_1540_,
    );
    crate::leanh::lean_dec(v_it_1537_);
    crate::leanh::lean_dec_ref(v_s_1535_);
    return v_res_1541_;
}
pub unsafe fn l_String_Slice_foldl___redArg(
    mut v_f_1542_: *mut crate::leanh::LeanObject,
    mut v_init_1543_: *mut crate::leanh::LeanObject,
    mut v_s_1544_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1545_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1545_, 0, v_s_1544_);
    crate::leanh::lean_closure_set(v___f_1545_, 1, v_f_1542_);
    v___x_1546_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1547_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1545_,
        v___x_1546_,
        v_init_1543_,
        crate::leanh::lean_box(0),
    );
    return v___x_1547_;
}
pub unsafe fn l_String_Slice_foldl(
    mut v_00_u03b1_1548_: *mut crate::leanh::LeanObject,
    mut v_f_1549_: *mut crate::leanh::LeanObject,
    mut v_init_1550_: *mut crate::leanh::LeanObject,
    mut v_s_1551_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1552_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1552_, 0, v_s_1551_);
    crate::leanh::lean_closure_set(v___f_1552_, 1, v_f_1549_);
    v___x_1553_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1554_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1552_,
        v___x_1553_,
        v_init_1550_,
        crate::leanh::lean_box(0),
    );
    return v___x_1554_;
}
pub unsafe fn l_String_Slice_foldr___redArg___lam__0(
    mut v_s_1555_: *mut crate::leanh::LeanObject,
    mut v_f_1556_: *mut crate::leanh::LeanObject,
    mut v_it_1557_: *mut crate::leanh::LeanObject,
    mut v_acc_1558_: *mut crate::leanh::LeanObject,
    mut v_hP_1559_: *mut crate::leanh::LeanObject,
    mut v_recur_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    v___x_1561_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1562_ = lean_nat_dec_eq(v_it_1557_, v___x_1561_);
    if v___x_1562_ == 0 {
        let mut v_str_1563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_1564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: u32 = 0;
        let mut v___x_1570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_str_1563_ = crate::leanh::lean_ctor_get(v_s_1555_, 0);
        v_startInclusive_1564_ = crate::leanh::lean_ctor_get(v_s_1555_, 1);
        v___x_1565_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1566_ = lean_nat_sub(v_it_1557_, v___x_1565_);
        v_prevPos_1567_ = l_String_Slice_posLE(v_s_1555_, v___x_1566_);
        v___x_1568_ = lean_nat_add(v_startInclusive_1564_, v_prevPos_1567_);
        v___x_1569_ = lean_string_utf8_get_fast(v_str_1563_, v___x_1568_);
        crate::leanh::lean_dec(v___x_1568_);
        v___x_1570_ = crate::leanh::lean_box_uint32(v___x_1569_);
        v___x_1571_ = crate::leanh::lean_apply_2(v_f_1556_, v___x_1570_, v_acc_1558_);
        v___x_1572_ = crate::leanh::lean_apply_4(
            v_recur_1560_,
            v_prevPos_1567_,
            v___x_1571_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1572_;
    } else {
        crate::leanh::lean_dec(v_recur_1560_);
        crate::leanh::lean_dec(v_f_1556_);
        return v_acc_1558_;
    }
}
pub unsafe fn l_String_Slice_foldr___redArg___lam__0___boxed(
    mut v_s_1573_: *mut crate::leanh::LeanObject,
    mut v_f_1574_: *mut crate::leanh::LeanObject,
    mut v_it_1575_: *mut crate::leanh::LeanObject,
    mut v_acc_1576_: *mut crate::leanh::LeanObject,
    mut v_hP_1577_: *mut crate::leanh::LeanObject,
    mut v_recur_1578_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_String_Slice_foldr___redArg___lam__0(
        v_s_1573_,
        v_f_1574_,
        v_it_1575_,
        v_acc_1576_,
        v_hP_1577_,
        v_recur_1578_,
    );
    crate::leanh::lean_dec(v_it_1575_);
    crate::leanh::lean_dec_ref(v_s_1573_);
    return v_res_1579_;
}
pub unsafe fn l_String_Slice_foldr___redArg(
    mut v_f_1580_: *mut crate::leanh::LeanObject,
    mut v_init_1581_: *mut crate::leanh::LeanObject,
    mut v_s_1582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_1582_);
    v___f_1583_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1583_, 0, v_s_1582_);
    crate::leanh::lean_closure_set(v___f_1583_, 1, v_f_1580_);
    v___x_1584_ = l_String_Slice_revPositions(v_s_1582_);
    crate::leanh::lean_dec_ref(v_s_1582_);
    v___x_1585_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1583_,
        v___x_1584_,
        v_init_1581_,
        crate::leanh::lean_box(0),
    );
    return v___x_1585_;
}
pub unsafe fn l_String_Slice_foldr(
    mut v_00_u03b1_1586_: *mut crate::leanh::LeanObject,
    mut v_f_1587_: *mut crate::leanh::LeanObject,
    mut v_init_1588_: *mut crate::leanh::LeanObject,
    mut v_s_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc_ref(v_s_1589_);
    v___f_1590_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    crate::leanh::lean_closure_set(v___f_1590_, 0, v_s_1589_);
    crate::leanh::lean_closure_set(v___f_1590_, 1, v_f_1587_);
    v___x_1591_ = l_String_Slice_revPositions(v_s_1589_);
    crate::leanh::lean_dec_ref(v_s_1589_);
    v___x_1592_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1590_,
        v___x_1591_,
        v_init_1588_,
        crate::leanh::lean_box(0),
    );
    return v___x_1592_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___redArg(
    mut v_x_1593_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1593_);
    return v_x_1593_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___redArg___boxed(
    mut v_x_1594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1595_ = l_String_Internal_ofToSliceWithProof___redArg(v_x_1594_);
    crate::leanh::lean_dec(v_x_1594_);
    return v_res_1595_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof(
    mut v_s_1596_: *mut crate::leanh::LeanObject,
    mut v_x_1597_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_1597_);
    return v_x_1597_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___boxed(
    mut v_s_1598_: *mut crate::leanh::LeanObject,
    mut v_x_1599_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_String_Internal_ofToSliceWithProof(v_s_1598_, v_x_1599_);
    crate::leanh::lean_dec(v_x_1599_);
    crate::leanh::lean_dec_ref(v_s_1598_);
    return v_res_1600_;
}
pub unsafe fn l_String_positionsFrom___redArg(
    mut v_p_1601_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1601_);
    return v_p_1601_;
}
pub unsafe fn l_String_positionsFrom___redArg___boxed(
    mut v_p_1602_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_String_positionsFrom___redArg(v_p_1602_);
    crate::leanh::lean_dec(v_p_1602_);
    return v_res_1603_;
}
pub unsafe fn l_String_positionsFrom(
    mut v_s_1604_: *mut crate::leanh::LeanObject,
    mut v_p_1605_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1605_);
    return v_p_1605_;
}
pub unsafe fn l_String_positionsFrom___boxed(
    mut v_s_1606_: *mut crate::leanh::LeanObject,
    mut v_p_1607_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_String_positionsFrom(v_s_1606_, v_p_1607_);
    crate::leanh::lean_dec(v_p_1607_);
    crate::leanh::lean_dec_ref(v_s_1606_);
    return v_res_1608_;
}
pub unsafe fn l_String_positions(
    mut v_s_1609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1610_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1610_;
}
pub unsafe fn l_String_positions___boxed(
    mut v_s_1611_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_String_positions(v_s_1611_);
    crate::leanh::lean_dec_ref(v_s_1611_);
    return v_res_1612_;
}
pub unsafe fn l_String_chars(
    mut v_s_1613_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1614_ = crate::leanh::lean_unsigned_to_nat(0);
    return v___x_1614_;
}
pub unsafe fn l_String_chars___boxed(
    mut v_s_1615_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_String_chars(v_s_1615_);
    crate::leanh::lean_dec_ref(v_s_1615_);
    return v_res_1616_;
}
pub unsafe fn l_String_revPositionsFrom___redArg(
    mut v_p_1617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1617_);
    return v_p_1617_;
}
pub unsafe fn l_String_revPositionsFrom___redArg___boxed(
    mut v_p_1618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_String_revPositionsFrom___redArg(v_p_1618_);
    crate::leanh::lean_dec(v_p_1618_);
    return v_res_1619_;
}
pub unsafe fn l_String_revPositionsFrom(
    mut v_s_1620_: *mut crate::leanh::LeanObject,
    mut v_p_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_p_1621_);
    return v_p_1621_;
}
pub unsafe fn l_String_revPositionsFrom___boxed(
    mut v_s_1622_: *mut crate::leanh::LeanObject,
    mut v_p_1623_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_String_revPositionsFrom(v_s_1622_, v_p_1623_);
    crate::leanh::lean_dec(v_p_1623_);
    crate::leanh::lean_dec_ref(v_s_1622_);
    return v_res_1624_;
}
pub unsafe fn l_String_revPositions(
    mut v_s_1625_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = lean_string_utf8_byte_size(v_s_1625_);
    return v___x_1626_;
}
pub unsafe fn l_String_revPositions___boxed(
    mut v_s_1627_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_String_revPositions(v_s_1627_);
    crate::leanh::lean_dec_ref(v_s_1627_);
    return v_res_1628_;
}
pub unsafe fn l_String_revChars(
    mut v_s_1629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1630_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1631_ = lean_string_utf8_byte_size(v_s_1629_);
    v___x_1632_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1632_, 0, v_s_1629_);
    crate::leanh::lean_ctor_set(v___x_1632_, 1, v___x_1630_);
    crate::leanh::lean_ctor_set(v___x_1632_, 2, v___x_1631_);
    v___x_1633_ = l_String_Slice_revPositions(v___x_1632_);
    crate::leanh::lean_dec_ref_known(v___x_1632_, 3);
    return v___x_1633_;
}
pub unsafe fn l_String_byteIterator(
    mut v_s_1634_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1635_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1636_ = lean_string_utf8_byte_size(v_s_1634_);
    v___x_1637_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1637_, 0, v_s_1634_);
    crate::leanh::lean_ctor_set(v___x_1637_, 1, v___x_1635_);
    crate::leanh::lean_ctor_set(v___x_1637_, 2, v___x_1636_);
    v___x_1638_ = l_String_Slice_bytes(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_String_revBytes(
    mut v_s_1639_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1640_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1641_ = lean_string_utf8_byte_size(v_s_1639_);
    v___x_1642_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1642_, 0, v_s_1639_);
    crate::leanh::lean_ctor_set(v___x_1642_, 1, v___x_1640_);
    crate::leanh::lean_ctor_set(v___x_1642_, 2, v___x_1641_);
    v___x_1643_ = l_String_Slice_revBytes(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__2(
    mut v___x_1644_: *mut crate::leanh::LeanObject,
    mut v_s_1645_: *mut crate::leanh::LeanObject,
    mut v_toPure_1646_: *mut crate::leanh::LeanObject,
    mut v_f_1647_: *mut crate::leanh::LeanObject,
    mut v_toBind_1648_: *mut crate::leanh::LeanObject,
    mut v___f_1649_: *mut crate::leanh::LeanObject,
    mut v_it_1650_: *mut crate::leanh::LeanObject,
    mut v_acc_1651_: *mut crate::leanh::LeanObject,
    mut v_hP_1652_: *mut crate::leanh::LeanObject,
    mut v_recur_1653_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1654_: u8 = 0;
    v___x_1654_ = lean_nat_dec_eq(v_it_1650_, v___x_1644_);
    if v___x_1654_ == 0 {
        let mut v___x_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_1656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: u32 = 0;
        let mut v___x_1658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1655_ = lean_string_utf8_next_fast(v_s_1645_, v_it_1650_);
        v___f_1656_ = crate::leanh::lean_alloc_closure(
            l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            3,
        );
        crate::leanh::lean_closure_set(v___f_1656_, 0, v_toPure_1646_);
        crate::leanh::lean_closure_set(v___f_1656_, 1, v_recur_1653_);
        crate::leanh::lean_closure_set(v___f_1656_, 2, v___x_1655_);
        v___x_1657_ = lean_string_utf8_get_fast(v_s_1645_, v_it_1650_);
        v___x_1658_ = crate::leanh::lean_box_uint32(v___x_1657_);
        v___x_1659_ = crate::leanh::lean_apply_2(v_f_1647_, v___x_1658_, v_acc_1651_);
        crate::leanh::lean_inc(v_toBind_1648_);
        v___x_1660_ = crate::leanh::lean_apply_4(
            v_toBind_1648_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1659_,
            v___f_1649_,
        );
        v___x_1661_ = crate::leanh::lean_apply_4(
            v_toBind_1648_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_1660_,
            v___f_1656_,
        );
        return v___x_1661_;
    } else {
        let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_recur_1653_);
        crate::leanh::lean_dec(v___f_1649_);
        crate::leanh::lean_dec(v_toBind_1648_);
        crate::leanh::lean_dec(v_f_1647_);
        v___x_1662_ =
            crate::leanh::lean_apply_2(v_toPure_1646_, crate::leanh::lean_box(0), v_acc_1651_);
        return v___x_1662_;
    }
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__2___boxed(
    mut v___x_1663_: *mut crate::leanh::LeanObject,
    mut v_s_1664_: *mut crate::leanh::LeanObject,
    mut v_toPure_1665_: *mut crate::leanh::LeanObject,
    mut v_f_1666_: *mut crate::leanh::LeanObject,
    mut v_toBind_1667_: *mut crate::leanh::LeanObject,
    mut v___f_1668_: *mut crate::leanh::LeanObject,
    mut v_it_1669_: *mut crate::leanh::LeanObject,
    mut v_acc_1670_: *mut crate::leanh::LeanObject,
    mut v_hP_1671_: *mut crate::leanh::LeanObject,
    mut v_recur_1672_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1673_ = l_String_instForInCharOfMonad___redArg___lam__2(
        v___x_1663_,
        v_s_1664_,
        v_toPure_1665_,
        v_f_1666_,
        v_toBind_1667_,
        v___f_1668_,
        v_it_1669_,
        v_acc_1670_,
        v_hP_1671_,
        v_recur_1672_,
    );
    crate::leanh::lean_dec(v_it_1669_);
    crate::leanh::lean_dec_ref(v_s_1664_);
    crate::leanh::lean_dec(v___x_1663_);
    return v_res_1673_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__0(
    mut v_inst_1674_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_1675_: *mut crate::leanh::LeanObject,
    mut v_s_1676_: *mut crate::leanh::LeanObject,
    mut v_b_1677_: *mut crate::leanh::LeanObject,
    mut v_f_1678_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toApplicative_1679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_1679_ = crate::leanh::lean_ctor_get(v_inst_1674_, 0);
    crate::leanh::lean_inc_ref(v_toApplicative_1679_);
    v_toBind_1680_ = crate::leanh::lean_ctor_get(v_inst_1674_, 1);
    crate::leanh::lean_inc(v_toBind_1680_);
    crate::leanh::lean_dec_ref(v_inst_1674_);
    v_toPure_1681_ = crate::leanh::lean_ctor_get(v_toApplicative_1679_, 1);
    crate::leanh::lean_inc_n(v_toPure_1681_, 2);
    crate::leanh::lean_dec_ref(v_toApplicative_1679_);
    v___x_1682_ = lean_string_utf8_byte_size(v_s_1676_);
    v___x_1683_ = crate::leanh::lean_unsigned_to_nat(0);
    v___f_1684_ = crate::leanh::lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1684_, 0, v_toPure_1681_);
    v___f_1685_ = crate::leanh::lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    crate::leanh::lean_closure_set(v___f_1685_, 0, v___x_1682_);
    crate::leanh::lean_closure_set(v___f_1685_, 1, v_s_1676_);
    crate::leanh::lean_closure_set(v___f_1685_, 2, v_toPure_1681_);
    crate::leanh::lean_closure_set(v___f_1685_, 3, v_f_1678_);
    crate::leanh::lean_closure_set(v___f_1685_, 4, v_toBind_1680_);
    crate::leanh::lean_closure_set(v___f_1685_, 5, v___f_1684_);
    v___x_1686_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1685_,
        v___x_1683_,
        v_b_1677_,
        crate::leanh::lean_box(0),
    );
    return v___x_1686_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg(
    mut v_inst_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1688_ = crate::leanh::lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1688_, 0, v_inst_1687_);
    return v___f_1688_;
}
pub unsafe fn l_String_instForInCharOfMonad(
    mut v_m_1689_: *mut crate::leanh::LeanObject,
    mut v_inst_1690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1691_ = crate::leanh::lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1691_, 0, v_inst_1690_);
    return v___f_1691_;
}
pub unsafe fn l_String_foldl___redArg___lam__0(
    mut v___x_1692_: *mut crate::leanh::LeanObject,
    mut v_s_1693_: *mut crate::leanh::LeanObject,
    mut v_f_1694_: *mut crate::leanh::LeanObject,
    mut v_it_1695_: *mut crate::leanh::LeanObject,
    mut v_acc_1696_: *mut crate::leanh::LeanObject,
    mut v_hP_1697_: *mut crate::leanh::LeanObject,
    mut v_recur_1698_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1699_: u8 = 0;
    v___x_1699_ = lean_nat_dec_eq(v_it_1695_, v___x_1692_);
    if v___x_1699_ == 0 {
        let mut v___x_1700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: u32 = 0;
        let mut v___x_1702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1700_ = lean_string_utf8_next_fast(v_s_1693_, v_it_1695_);
        v___x_1701_ = lean_string_utf8_get_fast(v_s_1693_, v_it_1695_);
        v___x_1702_ = crate::leanh::lean_box_uint32(v___x_1701_);
        v___x_1703_ = crate::leanh::lean_apply_2(v_f_1694_, v_acc_1696_, v___x_1702_);
        v___x_1704_ = crate::leanh::lean_apply_4(
            v_recur_1698_,
            v___x_1700_,
            v___x_1703_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1704_;
    } else {
        crate::leanh::lean_dec(v_recur_1698_);
        crate::leanh::lean_dec(v_f_1694_);
        return v_acc_1696_;
    }
}
pub unsafe fn l_String_foldl___redArg___lam__0___boxed(
    mut v___x_1705_: *mut crate::leanh::LeanObject,
    mut v_s_1706_: *mut crate::leanh::LeanObject,
    mut v_f_1707_: *mut crate::leanh::LeanObject,
    mut v_it_1708_: *mut crate::leanh::LeanObject,
    mut v_acc_1709_: *mut crate::leanh::LeanObject,
    mut v_hP_1710_: *mut crate::leanh::LeanObject,
    mut v_recur_1711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_String_foldl___redArg___lam__0(
        v___x_1705_,
        v_s_1706_,
        v_f_1707_,
        v_it_1708_,
        v_acc_1709_,
        v_hP_1710_,
        v_recur_1711_,
    );
    crate::leanh::lean_dec(v_it_1708_);
    crate::leanh::lean_dec_ref(v_s_1706_);
    crate::leanh::lean_dec(v___x_1705_);
    return v_res_1712_;
}
pub unsafe fn l_String_foldl___redArg(
    mut v_f_1713_: *mut crate::leanh::LeanObject,
    mut v_init_1714_: *mut crate::leanh::LeanObject,
    mut v_s_1715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_string_utf8_byte_size(v_s_1715_);
    v___f_1717_ = crate::leanh::lean_alloc_closure(
        l_String_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1717_, 0, v___x_1716_);
    crate::leanh::lean_closure_set(v___f_1717_, 1, v_s_1715_);
    crate::leanh::lean_closure_set(v___f_1717_, 2, v_f_1713_);
    v___x_1718_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1719_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1717_,
        v___x_1718_,
        v_init_1714_,
        crate::leanh::lean_box(0),
    );
    return v___x_1719_;
}
pub unsafe fn l_String_foldl(
    mut v_00_u03b1_1720_: *mut crate::leanh::LeanObject,
    mut v_f_1721_: *mut crate::leanh::LeanObject,
    mut v_init_1722_: *mut crate::leanh::LeanObject,
    mut v_s_1723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1724_ = lean_string_utf8_byte_size(v_s_1723_);
    v___f_1725_ = crate::leanh::lean_alloc_closure(
        l_String_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1725_, 0, v___x_1724_);
    crate::leanh::lean_closure_set(v___f_1725_, 1, v_s_1723_);
    crate::leanh::lean_closure_set(v___f_1725_, 2, v_f_1721_);
    v___x_1726_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1727_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1725_,
        v___x_1726_,
        v_init_1722_,
        crate::leanh::lean_box(0),
    );
    return v___x_1727_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
    mut v_f_1728_: *mut crate::leanh::LeanObject,
    mut v___x_1729_: *mut crate::leanh::LeanObject,
    mut v_s_1730_: *mut crate::leanh::LeanObject,
    mut v_a_1731_: *mut crate::leanh::LeanObject,
    mut v_b_1732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_startInclusive_1733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: u32 = 0;
    let mut v___x_1738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1733_ = crate::leanh::lean_ctor_get(v___x_1729_, 1);
                v_endExclusive_1734_ = crate::leanh::lean_ctor_get(v___x_1729_, 2);
                v___x_1735_ = lean_nat_sub(v_endExclusive_1734_, v_startInclusive_1733_);
                v___x_1736_ = lean_nat_dec_eq(v_a_1731_, v___x_1735_);
                crate::leanh::lean_dec(v___x_1735_);
                if v___x_1736_ == 0 {
                    v___x_1737_ = lean_string_utf8_get_fast(v_s_1730_, v_a_1731_);
                    v___x_1738_ = lean_string_utf8_next_fast(v_s_1730_, v_a_1731_);
                    crate::leanh::lean_dec(v_a_1731_);
                    v___x_1739_ = crate::leanh::lean_box_uint32(v___x_1737_);
                    crate::leanh::lean_inc_ref(v_f_1728_);
                    v___x_1740_ = crate::leanh::lean_apply_2(v_f_1728_, v_b_1732_, v___x_1739_);
                    v_a_1731_ = v___x_1738_;
                    v_b_1732_ = v___x_1740_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1731_);
                    crate::leanh::lean_dec_ref(v_f_1728_);
                    return v_b_1732_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(
    mut v_f_1742_: *mut crate::leanh::LeanObject,
    mut v___x_1743_: *mut crate::leanh::LeanObject,
    mut v_s_1744_: *mut crate::leanh::LeanObject,
    mut v_a_1745_: *mut crate::leanh::LeanObject,
    mut v_b_1746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
        v_f_1742_,
        v___x_1743_,
        v_s_1744_,
        v_a_1745_,
        v_b_1746_,
    );
    crate::leanh::lean_dec_ref(v_s_1744_);
    crate::leanh::lean_dec_ref(v___x_1743_);
    return v_res_1747_;
}
pub unsafe fn lean_string_foldl(
    mut v_f_1748_: *mut crate::leanh::LeanObject,
    mut v_init_1749_: *mut crate::leanh::LeanObject,
    mut v_s_1750_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1751_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1752_ = lean_string_utf8_byte_size(v_s_1750_);
    crate::leanh::lean_inc_ref(v_s_1750_);
    v___x_1753_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1753_, 0, v_s_1750_);
    crate::leanh::lean_ctor_set(v___x_1753_, 1, v___x_1751_);
    crate::leanh::lean_ctor_set(v___x_1753_, 2, v___x_1752_);
    v___x_1754_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
        v_f_1748_,
        v___x_1753_,
        v_s_1750_,
        v___x_1751_,
        v_init_1749_,
    );
    crate::leanh::lean_dec_ref(v_s_1750_);
    crate::leanh::lean_dec_ref_known(v___x_1753_, 3);
    return v___x_1754_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(
    mut v_f_1755_: *mut crate::leanh::LeanObject,
    mut v___x_1756_: *mut crate::leanh::LeanObject,
    mut v_s_1757_: *mut crate::leanh::LeanObject,
    mut v_inst_1758_: *mut crate::leanh::LeanObject,
    mut v_R_1759_: *mut crate::leanh::LeanObject,
    mut v_a_1760_: *mut crate::leanh::LeanObject,
    mut v_b_1761_: *mut crate::leanh::LeanObject,
    mut v_c_1762_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1763_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
        v_f_1755_,
        v___x_1756_,
        v_s_1757_,
        v_a_1760_,
        v_b_1761_,
    );
    return v___x_1763_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___boxed(
    mut v_f_1764_: *mut crate::leanh::LeanObject,
    mut v___x_1765_: *mut crate::leanh::LeanObject,
    mut v_s_1766_: *mut crate::leanh::LeanObject,
    mut v_inst_1767_: *mut crate::leanh::LeanObject,
    mut v_R_1768_: *mut crate::leanh::LeanObject,
    mut v_a_1769_: *mut crate::leanh::LeanObject,
    mut v_b_1770_: *mut crate::leanh::LeanObject,
    mut v_c_1771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1772_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(
        v_f_1764_,
        v___x_1765_,
        v_s_1766_,
        v_inst_1767_,
        v_R_1768_,
        v_a_1769_,
        v_b_1770_,
        v_c_1771_,
    );
    crate::leanh::lean_dec_ref(v_s_1766_);
    crate::leanh::lean_dec_ref(v___x_1765_);
    return v_res_1772_;
}
pub unsafe fn l_String_foldr___redArg___lam__0(
    mut v___x_1773_: *mut crate::leanh::LeanObject,
    mut v___x_1774_: *mut crate::leanh::LeanObject,
    mut v_s_1775_: *mut crate::leanh::LeanObject,
    mut v_f_1776_: *mut crate::leanh::LeanObject,
    mut v_it_1777_: *mut crate::leanh::LeanObject,
    mut v_acc_1778_: *mut crate::leanh::LeanObject,
    mut v_hP_1779_: *mut crate::leanh::LeanObject,
    mut v_recur_1780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1781_: u8 = 0;
    v___x_1781_ = lean_nat_dec_eq(v_it_1777_, v___x_1773_);
    if v___x_1781_ == 0 {
        let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: u32 = 0;
        let mut v___x_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_1782_ = crate::leanh::lean_unsigned_to_nat(1);
        v___x_1783_ = lean_nat_sub(v_it_1777_, v___x_1782_);
        v_prevPos_1784_ = l_String_Slice_posLE(v___x_1774_, v___x_1783_);
        v___x_1785_ = lean_string_utf8_get_fast(v_s_1775_, v_prevPos_1784_);
        v___x_1786_ = crate::leanh::lean_box_uint32(v___x_1785_);
        v___x_1787_ = crate::leanh::lean_apply_2(v_f_1776_, v___x_1786_, v_acc_1778_);
        v___x_1788_ = crate::leanh::lean_apply_4(
            v_recur_1780_,
            v_prevPos_1784_,
            v___x_1787_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
        );
        return v___x_1788_;
    } else {
        crate::leanh::lean_dec(v_recur_1780_);
        crate::leanh::lean_dec(v_f_1776_);
        return v_acc_1778_;
    }
}
pub unsafe fn l_String_foldr___redArg___lam__0___boxed(
    mut v___x_1789_: *mut crate::leanh::LeanObject,
    mut v___x_1790_: *mut crate::leanh::LeanObject,
    mut v_s_1791_: *mut crate::leanh::LeanObject,
    mut v_f_1792_: *mut crate::leanh::LeanObject,
    mut v_it_1793_: *mut crate::leanh::LeanObject,
    mut v_acc_1794_: *mut crate::leanh::LeanObject,
    mut v_hP_1795_: *mut crate::leanh::LeanObject,
    mut v_recur_1796_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1797_ = l_String_foldr___redArg___lam__0(
        v___x_1789_,
        v___x_1790_,
        v_s_1791_,
        v_f_1792_,
        v_it_1793_,
        v_acc_1794_,
        v_hP_1795_,
        v_recur_1796_,
    );
    crate::leanh::lean_dec(v_it_1793_);
    crate::leanh::lean_dec_ref(v_s_1791_);
    crate::leanh::lean_dec_ref(v___x_1790_);
    crate::leanh::lean_dec(v___x_1789_);
    return v_res_1797_;
}
pub unsafe fn l_String_foldr___redArg(
    mut v_f_1798_: *mut crate::leanh::LeanObject,
    mut v_init_1799_: *mut crate::leanh::LeanObject,
    mut v_s_1800_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1801_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1802_ = lean_string_utf8_byte_size(v_s_1800_);
    crate::leanh::lean_inc_ref(v_s_1800_);
    v___x_1803_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1803_, 0, v_s_1800_);
    crate::leanh::lean_ctor_set(v___x_1803_, 1, v___x_1801_);
    crate::leanh::lean_ctor_set(v___x_1803_, 2, v___x_1802_);
    crate::leanh::lean_inc_ref(v___x_1803_);
    v___f_1804_ = crate::leanh::lean_alloc_closure(
        l_String_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1804_, 0, v___x_1801_);
    crate::leanh::lean_closure_set(v___f_1804_, 1, v___x_1803_);
    crate::leanh::lean_closure_set(v___f_1804_, 2, v_s_1800_);
    crate::leanh::lean_closure_set(v___f_1804_, 3, v_f_1798_);
    v___x_1805_ = l_String_Slice_revPositions(v___x_1803_);
    crate::leanh::lean_dec_ref_known(v___x_1803_, 3);
    v___x_1806_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1804_,
        v___x_1805_,
        v_init_1799_,
        crate::leanh::lean_box(0),
    );
    return v___x_1806_;
}
pub unsafe fn l_String_foldr(
    mut v_00_u03b1_1807_: *mut crate::leanh::LeanObject,
    mut v_f_1808_: *mut crate::leanh::LeanObject,
    mut v_init_1809_: *mut crate::leanh::LeanObject,
    mut v_s_1810_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1811_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1812_ = lean_string_utf8_byte_size(v_s_1810_);
    crate::leanh::lean_inc_ref(v_s_1810_);
    v___x_1813_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1813_, 0, v_s_1810_);
    crate::leanh::lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    crate::leanh::lean_ctor_set(v___x_1813_, 2, v___x_1812_);
    crate::leanh::lean_inc_ref(v___x_1813_);
    v___f_1814_ = crate::leanh::lean_alloc_closure(
        l_String_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    crate::leanh::lean_closure_set(v___f_1814_, 0, v___x_1811_);
    crate::leanh::lean_closure_set(v___f_1814_, 1, v___x_1813_);
    crate::leanh::lean_closure_set(v___f_1814_, 2, v_s_1810_);
    crate::leanh::lean_closure_set(v___f_1814_, 3, v_f_1808_);
    v___x_1815_ = l_String_Slice_revPositions(v___x_1813_);
    crate::leanh::lean_dec_ref_known(v___x_1813_, 3);
    v___x_1816_ = l_WellFounded_opaqueFix_u2083___redArg(
        v___f_1814_,
        v___x_1815_,
        v_init_1809_,
        crate::leanh::lean_box(0),
    );
    return v___x_1816_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iterate(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
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
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
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
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iterate(
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
pub unsafe fn initialize_Init_Data_String_Iterate(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
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
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
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
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iterate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_String_Iterate(builtin);
}

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
use crate::lean_imports_rs::Init::Data::String::Basic::{
    lean_string_utf8_get_fast, lean_string_utf8_next_fast,
};
use crate::lean_imports_rs::Init::Data::String::PosRaw::lean_string_get_byte_fast;
use crate::lean_imports_rs::Init::Prelude::{
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_sub, lean_string_utf8_byte_size,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_2,
    lean_apply_3, lean_apply_4, lean_box, lean_box_uint32, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_String_Slice_instInhabitedByteIterator_default___closed__0_value: LeanStringObject<1> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_String_Slice_instInhabitedByteIterator_default___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__0_value)
        as *mut LeanObject;
pub static l_String_Slice_instInhabitedByteIterator_default___closed__1_value: LeanCtorObject<3> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 0) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__0_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_String_Slice_instInhabitedByteIterator_default___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
        as *mut LeanObject;
pub static l_String_Slice_instInhabitedByteIterator_default___closed__2_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_String_Slice_instInhabitedByteIterator_default___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut LeanObject;
pub static mut l_String_Slice_instInhabitedByteIterator_default: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut LeanObject;
pub static mut l_String_Slice_instInhabitedByteIterator: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__2_value)
        as *mut LeanObject;
pub static l_String_Slice_instInhabitedRevByteIterator___closed__0_value: LeanCtorObject<2> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_String_Slice_instInhabitedByteIterator_default___closed__1_value)
                as *mut LeanObject,
            (((0 as usize) << 1) | 1) as *mut LeanObject,
        ],
    };
static mut l_String_Slice_instInhabitedRevByteIterator___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedRevByteIterator___closed__0_value)
        as *mut LeanObject;
pub static mut l_String_Slice_instInhabitedRevByteIterator: *mut LeanObject =
    core::ptr::addr_of!(l_String_Slice_instInhabitedRevByteIterator___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_String_Slice_instInhabitedPosIterator_default(
    mut v_s_909_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_910_: *mut LeanObject = core::ptr::null_mut();
    v___x_910_ = lean_unsigned_to_nat(0);
    return v___x_910_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator_default___boxed(
    mut v_s_911_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_912_: *mut LeanObject = core::ptr::null_mut();
    v_res_912_ = l_String_Slice_instInhabitedPosIterator_default(v_s_911_);
    lean_dec_ref(v_s_911_);
    return v_res_912_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator(
    mut v_a_913_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_914_: *mut LeanObject = core::ptr::null_mut();
    v___x_914_ = lean_unsigned_to_nat(0);
    return v___x_914_;
}
pub unsafe fn l_String_Slice_instInhabitedPosIterator___boxed(
    mut v_a_915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_916_: *mut LeanObject = core::ptr::null_mut();
    v_res_916_ = l_String_Slice_instInhabitedPosIterator(v_a_915_);
    lean_dec_ref(v_a_915_);
    return v_res_916_;
}
pub unsafe fn l_String_Slice_positionsFrom___redArg(
    mut v_p_917_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_917_);
    return v_p_917_;
}
pub unsafe fn l_String_Slice_positionsFrom___redArg___boxed(
    mut v_p_918_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_919_: *mut LeanObject = core::ptr::null_mut();
    v_res_919_ = l_String_Slice_positionsFrom___redArg(v_p_918_);
    lean_dec(v_p_918_);
    return v_res_919_;
}
pub unsafe fn l_String_Slice_positionsFrom(
    mut v_s_920_: *mut LeanObject,
    mut v_p_921_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_921_);
    return v_p_921_;
}
pub unsafe fn l_String_Slice_positionsFrom___boxed(
    mut v_s_922_: *mut LeanObject,
    mut v_p_923_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_924_: *mut LeanObject = core::ptr::null_mut();
    v_res_924_ = l_String_Slice_positionsFrom(v_s_922_, v_p_923_);
    lean_dec(v_p_923_);
    lean_dec_ref(v_s_922_);
    return v_res_924_;
}
pub unsafe fn l_String_Slice_positions(mut v_s_925_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_926_: *mut LeanObject = core::ptr::null_mut();
    v___x_926_ = lean_unsigned_to_nat(0);
    return v___x_926_;
}
pub unsafe fn l_String_Slice_positions___boxed(mut v_s_927_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_928_: *mut LeanObject = core::ptr::null_mut();
    v_res_928_ = l_String_Slice_positions(v_s_927_);
    lean_dec_ref(v_s_927_);
    return v_res_928_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
    mut v_s_929_: *mut LeanObject,
    mut v_inst_930_: *mut LeanObject,
    mut v_x_931_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    v_str_932_ = lean_ctor_get(v_s_929_, 0);
    v_startInclusive_933_ = lean_ctor_get(v_s_929_, 1);
    v_endExclusive_934_ = lean_ctor_get(v_s_929_, 2);
    v___x_935_ = lean_nat_sub(v_endExclusive_934_, v_startInclusive_933_);
    v___x_936_ = lean_nat_dec_eq(v_x_931_, v___x_935_);
    lean_dec(v___x_935_);
    if v___x_936_ == 0 {
        let mut v___x_937_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_938_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_939_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_940_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_941_: *mut LeanObject = core::ptr::null_mut();
        v___x_937_ = lean_nat_add(v_startInclusive_933_, v_x_931_);
        v___x_938_ = lean_string_utf8_next_fast(v_str_932_, v___x_937_);
        lean_dec(v___x_937_);
        v___x_939_ = lean_nat_sub(v___x_938_, v_startInclusive_933_);
        v___x_940_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_940_, 0, v___x_939_);
        lean_ctor_set(v___x_940_, 1, v_x_931_);
        v___x_941_ = lean_apply_2(v_inst_930_, lean_box(0), v___x_940_);
        return v___x_941_;
    } else {
        let mut v___x_942_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_943_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_x_931_);
        v___x_942_ = lean_box(2);
        v___x_943_ = lean_apply_2(v_inst_930_, lean_box(0), v___x_942_);
        return v___x_943_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(
    mut v_s_944_: *mut LeanObject,
    mut v_inst_945_: *mut LeanObject,
    mut v_x_946_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_947_: *mut LeanObject = core::ptr::null_mut();
    v_res_947_ = l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
        v_s_944_,
        v_inst_945_,
        v_x_946_,
    );
    lean_dec_ref(v_s_944_);
    return v_res_947_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(
    mut v_s_948_: *mut LeanObject,
    mut v_inst_949_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_950_: *mut LeanObject = core::ptr::null_mut();
    v___f_950_ = lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_950_, 0, v_s_948_);
    lean_closure_set(v___f_950_, 1, v_inst_949_);
    return v___f_950_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure(
    mut v_m_951_: *mut LeanObject,
    mut v_s_952_: *mut LeanObject,
    mut v_inst_953_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_954_: *mut LeanObject = core::ptr::null_mut();
    v___f_954_ = lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_954_, 0, v_s_952_);
    lean_closure_set(v___f_954_, 1, v_inst_953_);
    return v___f_954_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(
    mut v_m_955_: *mut LeanObject,
    mut v_s_956_: *mut LeanObject,
    mut v_inst_957_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_958_: *mut LeanObject = core::ptr::null_mut();
    v___x_958_ = lean_box(0);
    return v___x_958_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation___boxed(
    mut v_m_959_: *mut LeanObject,
    mut v_s_960_: *mut LeanObject,
    mut v_inst_961_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_962_: *mut LeanObject = core::ptr::null_mut();
    v_res_962_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_PosIterator_finitenessRelation(
            v_m_959_,
            v_s_960_,
            v_inst_961_,
        );
    lean_dec(v_inst_961_);
    lean_dec_ref(v_s_960_);
    return v_res_962_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(
    mut v_toPure_963_: *mut LeanObject,
    mut v_recur_964_: *mut LeanObject,
    mut v_it_965_: *mut LeanObject,
    mut v_____do__lift_966_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_966_) == 0 {
        let mut v_a_967_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_968_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_965_);
        lean_dec(v_recur_964_);
        v_a_967_ = lean_ctor_get(v_____do__lift_966_, 0);
        lean_inc(v_a_967_);
        lean_dec_ref_known(v_____do__lift_966_, 1);
        v___x_968_ = lean_apply_2(v_toPure_963_, lean_box(0), v_a_967_);
        return v___x_968_;
    } else {
        let mut v_a_969_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_970_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_963_);
        v_a_969_ = lean_ctor_get(v_____do__lift_966_, 0);
        lean_inc(v_a_969_);
        lean_dec_ref_known(v_____do__lift_966_, 1);
        v___x_970_ = lean_apply_4(v_recur_964_, v_it_965_, v_a_969_, lean_box(0), lean_box(0));
        return v___x_970_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1(
    mut v_toPure_971_: *mut LeanObject,
    mut v_recur_972_: *mut LeanObject,
    mut v___y_973_: *mut LeanObject,
    mut v_acc_974_: *mut LeanObject,
    mut v_toBind_975_: *mut LeanObject,
    mut v_s_976_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_976_) {
        0 => {
            let mut v_it_977_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_978_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_979_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_980_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_981_: *mut LeanObject = core::ptr::null_mut();
            v_it_977_ = lean_ctor_get(v_s_976_, 0);
            lean_inc(v_it_977_);
            v_out_978_ = lean_ctor_get(v_s_976_, 1);
            lean_inc(v_out_978_);
            lean_dec_ref_known(v_s_976_, 2);
            v___f_979_ = lean_alloc_closure(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0 as *mut core::ffi::c_void, 4, 3);
            lean_closure_set(v___f_979_, 0, v_toPure_971_);
            lean_closure_set(v___f_979_, 1, v_recur_972_);
            lean_closure_set(v___f_979_, 2, v_it_977_);
            v___x_980_ = lean_apply_3(v___y_973_, v_out_978_, lean_box(0), v_acc_974_);
            v___x_981_ = lean_apply_4(
                v_toBind_975_,
                lean_box(0),
                lean_box(0),
                v___x_980_,
                v___f_979_,
            );
            return v___x_981_;
        }
        1 => {
            let mut v_it_982_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_983_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_975_);
            lean_dec(v___y_973_);
            lean_dec(v_toPure_971_);
            v_it_982_ = lean_ctor_get(v_s_976_, 0);
            lean_inc(v_it_982_);
            lean_dec_ref_known(v_s_976_, 1);
            v___x_983_ = lean_apply_4(
                v_recur_972_,
                v_it_982_,
                v_acc_974_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_983_;
        }
        _ => {
            let mut v___x_984_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_975_);
            lean_dec(v___y_973_);
            lean_dec(v_recur_972_);
            v___x_984_ = lean_apply_2(v_toPure_971_, lean_box(0), v_acc_974_);
            return v___x_984_;
        }
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
    mut v_s_985_: *mut LeanObject,
    mut v_toPure_986_: *mut LeanObject,
    mut v___y_987_: *mut LeanObject,
    mut v_toBind_988_: *mut LeanObject,
    mut v_toPure_989_: *mut LeanObject,
    mut v_lift_990_: *mut LeanObject,
    mut v_it_991_: *mut LeanObject,
    mut v_acc_992_: *mut LeanObject,
    mut v_hP_993_: *mut LeanObject,
    mut v_recur_994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: u8 = 0;
    v_str_995_ = lean_ctor_get(v_s_985_, 0);
    v_startInclusive_996_ = lean_ctor_get(v_s_985_, 1);
    v_endExclusive_997_ = lean_ctor_get(v_s_985_, 2);
    v___f_998_ = lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_998_, 0, v_toPure_986_);
    lean_closure_set(v___f_998_, 1, v_recur_994_);
    lean_closure_set(v___f_998_, 2, v___y_987_);
    lean_closure_set(v___f_998_, 3, v_acc_992_);
    lean_closure_set(v___f_998_, 4, v_toBind_988_);
    v___x_999_ = lean_nat_sub(v_endExclusive_997_, v_startInclusive_996_);
    v___x_1000_ = lean_nat_dec_eq(v_it_991_, v___x_999_);
    lean_dec(v___x_999_);
    if v___x_1000_ == 0 {
        let mut v___x_1001_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1002_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1003_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1004_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1005_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1006_: *mut LeanObject = core::ptr::null_mut();
        v___x_1001_ = lean_nat_add(v_startInclusive_996_, v_it_991_);
        v___x_1002_ = lean_string_utf8_next_fast(v_str_995_, v___x_1001_);
        lean_dec(v___x_1001_);
        v___x_1003_ = lean_nat_sub(v___x_1002_, v_startInclusive_996_);
        v___x_1004_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1004_, 0, v___x_1003_);
        lean_ctor_set(v___x_1004_, 1, v_it_991_);
        v___x_1005_ = lean_apply_2(v_toPure_989_, lean_box(0), v___x_1004_);
        v___x_1006_ = lean_apply_4(
            v_lift_990_,
            lean_box(0),
            lean_box(0),
            v___f_998_,
            v___x_1005_,
        );
        return v___x_1006_;
    } else {
        let mut v___x_1007_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1008_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1009_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_it_991_);
        v___x_1007_ = lean_box(2);
        v___x_1008_ = lean_apply_2(v_toPure_989_, lean_box(0), v___x_1007_);
        v___x_1009_ = lean_apply_4(
            v_lift_990_,
            lean_box(0),
            lean_box(0),
            v___f_998_,
            v___x_1008_,
        );
        return v___x_1009_;
    }
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(
    mut v_s_1010_: *mut LeanObject,
    mut v_toPure_1011_: *mut LeanObject,
    mut v___y_1012_: *mut LeanObject,
    mut v_toBind_1013_: *mut LeanObject,
    mut v_toPure_1014_: *mut LeanObject,
    mut v_lift_1015_: *mut LeanObject,
    mut v_it_1016_: *mut LeanObject,
    mut v_acc_1017_: *mut LeanObject,
    mut v_hP_1018_: *mut LeanObject,
    mut v_recur_1019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1020_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_s_1010_);
    return v_res_1020_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3(
    mut v_inst_1021_: *mut LeanObject,
    mut v_s_1022_: *mut LeanObject,
    mut v_toPure_1023_: *mut LeanObject,
    mut v_lift_1024_: *mut LeanObject,
    mut v_00_u03b3_1025_: *mut LeanObject,
    mut v_Pl_1026_: *mut LeanObject,
    mut v_it_1027_: *mut LeanObject,
    mut v_init_1028_: *mut LeanObject,
    mut v___y_1029_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1034_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1030_ = lean_ctor_get(v_inst_1021_, 0);
    lean_inc_ref(v_toApplicative_1030_);
    v_toBind_1031_ = lean_ctor_get(v_inst_1021_, 1);
    lean_inc(v_toBind_1031_);
    lean_dec_ref(v_inst_1021_);
    v_toPure_1032_ = lean_ctor_get(v_toApplicative_1030_, 1);
    lean_inc(v_toPure_1032_);
    lean_dec_ref(v_toApplicative_1030_);
    v___f_1033_ = lean_alloc_closure(l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 6);
    lean_closure_set(v___f_1033_, 0, v_s_1022_);
    lean_closure_set(v___f_1033_, 1, v_toPure_1032_);
    lean_closure_set(v___f_1033_, 2, v___y_1029_);
    lean_closure_set(v___f_1033_, 3, v_toBind_1031_);
    lean_closure_set(v___f_1033_, 4, v_toPure_1023_);
    lean_closure_set(v___f_1033_, 5, v_lift_1024_);
    v___x_1034_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1033_, v_it_1027_, v_init_1028_, lean_box(0));
    return v___x_1034_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
    mut v_s_1035_: *mut LeanObject,
    mut v_inst_1036_: *mut LeanObject,
    mut v_inst_1037_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1040_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1038_ = lean_ctor_get(v_inst_1036_, 0);
    lean_inc_ref(v_toApplicative_1038_);
    lean_dec_ref(v_inst_1036_);
    v_toPure_1039_ = lean_ctor_get(v_toApplicative_1038_, 1);
    lean_inc(v_toPure_1039_);
    lean_dec_ref(v_toApplicative_1038_);
    v___f_1040_ = lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_1040_, 0, v_inst_1037_);
    lean_closure_set(v___f_1040_, 1, v_s_1035_);
    lean_closure_set(v___f_1040_, 2, v_toPure_1039_);
    return v___f_1040_;
}
pub unsafe fn l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(
    mut v_m_1041_: *mut LeanObject,
    mut v_n_1042_: *mut LeanObject,
    mut v_s_1043_: *mut LeanObject,
    mut v_inst_1044_: *mut LeanObject,
    mut v_inst_1045_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1046_: *mut LeanObject = core::ptr::null_mut();
    v___x_1046_ = l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
        v_s_1043_,
        v_inst_1044_,
        v_inst_1045_,
    );
    return v___x_1046_;
}
pub unsafe fn l_String_Slice_chars(mut v_s_1047_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1048_: *mut LeanObject = core::ptr::null_mut();
    v___x_1048_ = lean_unsigned_to_nat(0);
    return v___x_1048_;
}
pub unsafe fn l_String_Slice_chars___boxed(mut v_s_1049_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1050_: *mut LeanObject = core::ptr::null_mut();
    v_res_1050_ = l_String_Slice_chars(v_s_1049_);
    lean_dec_ref(v_s_1049_);
    return v_res_1050_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
    mut v_s_1051_: *mut LeanObject,
    mut v_a_1052_: *mut LeanObject,
    mut v_b_1053_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1058_: u8 = 0;
    let mut v___x_1059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1063_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_str_1054_ = lean_ctor_get(v_s_1051_, 0);
                v_startInclusive_1055_ = lean_ctor_get(v_s_1051_, 1);
                v_endExclusive_1056_ = lean_ctor_get(v_s_1051_, 2);
                v___x_1057_ = lean_nat_sub(v_endExclusive_1056_, v_startInclusive_1055_);
                v___x_1058_ = lean_nat_dec_eq(v_a_1052_, v___x_1057_);
                lean_dec(v___x_1057_);
                if v___x_1058_ == 0 {
                    v___x_1059_ = lean_nat_add(v_startInclusive_1055_, v_a_1052_);
                    lean_dec(v_a_1052_);
                    v___x_1060_ = lean_string_utf8_next_fast(v_str_1054_, v___x_1059_);
                    lean_dec(v___x_1059_);
                    v___x_1061_ = lean_nat_sub(v___x_1060_, v_startInclusive_1055_);
                    v___x_1062_ = lean_unsigned_to_nat(1);
                    v___x_1063_ = lean_nat_add(v_b_1053_, v___x_1062_);
                    lean_dec(v_b_1053_);
                    v_a_1052_ = v___x_1061_;
                    v_b_1053_ = v___x_1063_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1052_);
                    return v_b_1053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg___boxed(
    mut v_s_1065_: *mut LeanObject,
    mut v_a_1066_: *mut LeanObject,
    mut v_b_1067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1068_: *mut LeanObject = core::ptr::null_mut();
    v_res_1068_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1065_, v_a_1066_, v_b_1067_,
    );
    lean_dec_ref(v_s_1065_);
    return v_res_1068_;
}
pub unsafe fn l_String_Slice_length(mut v_s_1069_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut LeanObject = core::ptr::null_mut();
    v___x_1070_ = lean_unsigned_to_nat(0);
    v___x_1071_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1069_,
        v___x_1070_,
        v___x_1070_,
    );
    return v___x_1071_;
}
pub unsafe fn l_String_Slice_length___boxed(mut v_s_1072_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1073_: *mut LeanObject = core::ptr::null_mut();
    v_res_1073_ = l_String_Slice_length(v_s_1072_);
    lean_dec_ref(v_s_1072_);
    return v_res_1073_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(
    mut v_s_1074_: *mut LeanObject,
    mut v_inst_1075_: *mut LeanObject,
    mut v_R_1076_: *mut LeanObject,
    mut v_a_1077_: *mut LeanObject,
    mut v_b_1078_: *mut LeanObject,
    mut v_c_1079_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1080_: *mut LeanObject = core::ptr::null_mut();
    v___x_1080_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___redArg(
        v_s_1074_, v_a_1077_, v_b_1078_,
    );
    return v___x_1080_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0___boxed(
    mut v_s_1081_: *mut LeanObject,
    mut v_inst_1082_: *mut LeanObject,
    mut v_R_1083_: *mut LeanObject,
    mut v_a_1084_: *mut LeanObject,
    mut v_b_1085_: *mut LeanObject,
    mut v_c_1086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1087_: *mut LeanObject = core::ptr::null_mut();
    v_res_1087_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_length_spec__0(
        v_s_1081_,
        v_inst_1082_,
        v_R_1083_,
        v_a_1084_,
        v_b_1085_,
        v_c_1086_,
    );
    lean_dec_ref(v_s_1081_);
    return v_res_1087_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator_default(
    mut v_s_1088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1089_: *mut LeanObject = core::ptr::null_mut();
    v___x_1089_ = lean_unsigned_to_nat(0);
    return v___x_1089_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator_default___boxed(
    mut v_s_1090_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1091_: *mut LeanObject = core::ptr::null_mut();
    v_res_1091_ = l_String_Slice_instInhabitedRevPosIterator_default(v_s_1090_);
    lean_dec_ref(v_s_1090_);
    return v_res_1091_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator(
    mut v_a_1092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1093_: *mut LeanObject = core::ptr::null_mut();
    v___x_1093_ = lean_unsigned_to_nat(0);
    return v___x_1093_;
}
pub unsafe fn l_String_Slice_instInhabitedRevPosIterator___boxed(
    mut v_a_1094_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1095_: *mut LeanObject = core::ptr::null_mut();
    v_res_1095_ = l_String_Slice_instInhabitedRevPosIterator(v_a_1094_);
    lean_dec_ref(v_a_1094_);
    return v_res_1095_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___redArg(
    mut v_p_1096_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_1096_);
    return v_p_1096_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___redArg___boxed(
    mut v_p_1097_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1098_: *mut LeanObject = core::ptr::null_mut();
    v_res_1098_ = l_String_Slice_revPositionsFrom___redArg(v_p_1097_);
    lean_dec(v_p_1097_);
    return v_res_1098_;
}
pub unsafe fn l_String_Slice_revPositionsFrom(
    mut v_s_1099_: *mut LeanObject,
    mut v_p_1100_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_1100_);
    return v_p_1100_;
}
pub unsafe fn l_String_Slice_revPositionsFrom___boxed(
    mut v_s_1101_: *mut LeanObject,
    mut v_p_1102_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1103_: *mut LeanObject = core::ptr::null_mut();
    v_res_1103_ = l_String_Slice_revPositionsFrom(v_s_1101_, v_p_1102_);
    lean_dec(v_p_1102_);
    lean_dec_ref(v_s_1101_);
    return v_res_1103_;
}
pub unsafe fn l_String_Slice_revPositions(mut v_s_1104_: *mut LeanObject) -> *mut LeanObject {
    let mut v_startInclusive_1105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1107_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_1105_ = lean_ctor_get(v_s_1104_, 1);
    v_endExclusive_1106_ = lean_ctor_get(v_s_1104_, 2);
    v___x_1107_ = lean_nat_sub(v_endExclusive_1106_, v_startInclusive_1105_);
    return v___x_1107_;
}
pub unsafe fn l_String_Slice_revPositions___boxed(
    mut v_s_1108_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1109_: *mut LeanObject = core::ptr::null_mut();
    v_res_1109_ = l_String_Slice_revPositions(v_s_1108_);
    lean_dec_ref(v_s_1108_);
    return v_res_1109_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
    mut v_s_1110_: *mut LeanObject,
    mut v_inst_1111_: *mut LeanObject,
    mut v_x_1112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: u8 = 0;
    v___x_1113_ = lean_unsigned_to_nat(0);
    v___x_1114_ = lean_nat_dec_eq(v_x_1112_, v___x_1113_);
    if v___x_1114_ == 0 {
        let mut v___x_1115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1116_: *mut LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1119_: *mut LeanObject = core::ptr::null_mut();
        v___x_1115_ = lean_unsigned_to_nat(1);
        v___x_1116_ = lean_nat_sub(v_x_1112_, v___x_1115_);
        v_prevPos_1117_ = l_String_Slice_posLE(v_s_1110_, v___x_1116_);
        lean_inc(v_prevPos_1117_);
        v___x_1118_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1118_, 0, v_prevPos_1117_);
        lean_ctor_set(v___x_1118_, 1, v_prevPos_1117_);
        v___x_1119_ = lean_apply_2(v_inst_1111_, lean_box(0), v___x_1118_);
        return v___x_1119_;
    } else {
        let mut v___x_1120_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1121_: *mut LeanObject = core::ptr::null_mut();
        v___x_1120_ = lean_box(2);
        v___x_1121_ = lean_apply_2(v_inst_1111_, lean_box(0), v___x_1120_);
        return v___x_1121_;
    }
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed(
    mut v_s_1122_: *mut LeanObject,
    mut v_inst_1123_: *mut LeanObject,
    mut v_x_1124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1125_: *mut LeanObject = core::ptr::null_mut();
    v_res_1125_ =
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0(
            v_s_1122_,
            v_inst_1123_,
            v_x_1124_,
        );
    lean_dec(v_x_1124_);
    lean_dec_ref(v_s_1122_);
    return v_res_1125_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg(
    mut v_s_1126_: *mut LeanObject,
    mut v_inst_1127_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1128_: *mut LeanObject = core::ptr::null_mut();
    v___f_1128_ = lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1128_, 0, v_s_1126_);
    lean_closure_set(v___f_1128_, 1, v_inst_1127_);
    return v___f_1128_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure(
    mut v_m_1129_: *mut LeanObject,
    mut v_s_1130_: *mut LeanObject,
    mut v_inst_1131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1132_: *mut LeanObject = core::ptr::null_mut();
    v___f_1132_ = lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorSubtypePosNeEndPosOfPure___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_1132_, 0, v_s_1130_);
    lean_closure_set(v___f_1132_, 1, v_inst_1131_);
    return v___f_1132_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(
    mut v_m_1133_: *mut LeanObject,
    mut v_s_1134_: *mut LeanObject,
    mut v_inst_1135_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1136_: *mut LeanObject = core::ptr::null_mut();
    v___x_1136_ = lean_box(0);
    return v___x_1136_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation___boxed(
    mut v_m_1137_: *mut LeanObject,
    mut v_s_1138_: *mut LeanObject,
    mut v_inst_1139_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1140_: *mut LeanObject = core::ptr::null_mut();
    v_res_1140_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_RevPosIterator_finitenessRelation(
            v_m_1137_,
            v_s_1138_,
            v_inst_1139_,
        );
    lean_dec(v_inst_1139_);
    lean_dec_ref(v_s_1138_);
    return v_res_1140_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2(
    mut v_toPure_1141_: *mut LeanObject,
    mut v___y_1142_: *mut LeanObject,
    mut v_toBind_1143_: *mut LeanObject,
    mut v_s_1144_: *mut LeanObject,
    mut v_toPure_1145_: *mut LeanObject,
    mut v_lift_1146_: *mut LeanObject,
    mut v_it_1147_: *mut LeanObject,
    mut v_acc_1148_: *mut LeanObject,
    mut v_hP_1149_: *mut LeanObject,
    mut v_recur_1150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1153_: u8 = 0;
    v___f_1151_ = lean_alloc_closure(
        l_String_Slice_PosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__1
            as *mut core::ffi::c_void,
        6,
        5,
    );
    lean_closure_set(v___f_1151_, 0, v_toPure_1141_);
    lean_closure_set(v___f_1151_, 1, v_recur_1150_);
    lean_closure_set(v___f_1151_, 2, v___y_1142_);
    lean_closure_set(v___f_1151_, 3, v_acc_1148_);
    lean_closure_set(v___f_1151_, 4, v_toBind_1143_);
    v___x_1152_ = lean_unsigned_to_nat(0);
    v___x_1153_ = lean_nat_dec_eq(v_it_1147_, v___x_1152_);
    if v___x_1153_ == 0 {
        let mut v___x_1154_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1155_: *mut LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1156_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1157_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1158_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1159_: *mut LeanObject = core::ptr::null_mut();
        v___x_1154_ = lean_unsigned_to_nat(1);
        v___x_1155_ = lean_nat_sub(v_it_1147_, v___x_1154_);
        v_prevPos_1156_ = l_String_Slice_posLE(v_s_1144_, v___x_1155_);
        lean_inc(v_prevPos_1156_);
        v___x_1157_ = lean_alloc_ctor(0, 2, (0) as u32);
        lean_ctor_set(v___x_1157_, 0, v_prevPos_1156_);
        lean_ctor_set(v___x_1157_, 1, v_prevPos_1156_);
        v___x_1158_ = lean_apply_2(v_toPure_1145_, lean_box(0), v___x_1157_);
        v___x_1159_ = lean_apply_4(
            v_lift_1146_,
            lean_box(0),
            lean_box(0),
            v___f_1151_,
            v___x_1158_,
        );
        return v___x_1159_;
    } else {
        let mut v___x_1160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1162_: *mut LeanObject = core::ptr::null_mut();
        v___x_1160_ = lean_box(2);
        v___x_1161_ = lean_apply_2(v_toPure_1145_, lean_box(0), v___x_1160_);
        v___x_1162_ = lean_apply_4(
            v_lift_1146_,
            lean_box(0),
            lean_box(0),
            v___f_1151_,
            v___x_1161_,
        );
        return v___x_1162_;
    }
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed(
    mut v_toPure_1163_: *mut LeanObject,
    mut v___y_1164_: *mut LeanObject,
    mut v_toBind_1165_: *mut LeanObject,
    mut v_s_1166_: *mut LeanObject,
    mut v_toPure_1167_: *mut LeanObject,
    mut v_lift_1168_: *mut LeanObject,
    mut v_it_1169_: *mut LeanObject,
    mut v_acc_1170_: *mut LeanObject,
    mut v_hP_1171_: *mut LeanObject,
    mut v_recur_1172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1173_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_1169_);
    lean_dec_ref(v_s_1166_);
    return v_res_1173_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0(
    mut v_inst_1174_: *mut LeanObject,
    mut v_s_1175_: *mut LeanObject,
    mut v_toPure_1176_: *mut LeanObject,
    mut v_lift_1177_: *mut LeanObject,
    mut v_00_u03b3_1178_: *mut LeanObject,
    mut v_Pl_1179_: *mut LeanObject,
    mut v_it_1180_: *mut LeanObject,
    mut v_init_1181_: *mut LeanObject,
    mut v___y_1182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1187_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1183_ = lean_ctor_get(v_inst_1174_, 0);
    lean_inc_ref(v_toApplicative_1183_);
    v_toBind_1184_ = lean_ctor_get(v_inst_1174_, 1);
    lean_inc(v_toBind_1184_);
    lean_dec_ref(v_inst_1174_);
    v_toPure_1185_ = lean_ctor_get(v_toApplicative_1183_, 1);
    lean_inc(v_toPure_1185_);
    lean_dec_ref(v_toApplicative_1183_);
    v___f_1186_ = lean_alloc_closure(l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void, 10, 6);
    lean_closure_set(v___f_1186_, 0, v_toPure_1185_);
    lean_closure_set(v___f_1186_, 1, v___y_1182_);
    lean_closure_set(v___f_1186_, 2, v_toBind_1184_);
    lean_closure_set(v___f_1186_, 3, v_s_1175_);
    lean_closure_set(v___f_1186_, 4, v_toPure_1176_);
    lean_closure_set(v___f_1186_, 5, v_lift_1177_);
    v___x_1187_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1186_, v_it_1180_, v_init_1181_, lean_box(0));
    return v___x_1187_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
    mut v_s_1188_: *mut LeanObject,
    mut v_inst_1189_: *mut LeanObject,
    mut v_inst_1190_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1193_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1191_ = lean_ctor_get(v_inst_1189_, 0);
    lean_inc_ref(v_toApplicative_1191_);
    lean_dec_ref(v_inst_1189_);
    v_toPure_1192_ = lean_ctor_get(v_toApplicative_1191_, 1);
    lean_inc(v_toPure_1192_);
    lean_dec_ref(v_toApplicative_1191_);
    v___f_1193_ = lean_alloc_closure(
        l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        9,
        3,
    );
    lean_closure_set(v___f_1193_, 0, v_inst_1190_);
    lean_closure_set(v___f_1193_, 1, v_s_1188_);
    lean_closure_set(v___f_1193_, 2, v_toPure_1192_);
    return v___f_1193_;
}
pub unsafe fn l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad(
    mut v_m_1194_: *mut LeanObject,
    mut v_n_1195_: *mut LeanObject,
    mut v_s_1196_: *mut LeanObject,
    mut v_inst_1197_: *mut LeanObject,
    mut v_inst_1198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1199_: *mut LeanObject = core::ptr::null_mut();
    v___x_1199_ = l_String_Slice_RevPosIterator_instIteratorLoopSubtypePosNeEndPosOfMonad___redArg(
        v_s_1196_,
        v_inst_1197_,
        v_inst_1198_,
    );
    return v___x_1199_;
}
pub unsafe fn l_String_Slice_revChars(mut v_s_1200_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1201_: *mut LeanObject = core::ptr::null_mut();
    v___x_1201_ = l_String_Slice_revPositions(v_s_1200_);
    return v___x_1201_;
}
pub unsafe fn l_String_Slice_revChars___boxed(mut v_s_1202_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1203_: *mut LeanObject = core::ptr::null_mut();
    v_res_1203_ = l_String_Slice_revChars(v_s_1202_);
    lean_dec_ref(v_s_1202_);
    return v_res_1203_;
}
pub unsafe fn l_String_Slice_bytes(mut v_s_1213_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1215_: *mut LeanObject = core::ptr::null_mut();
    v___x_1214_ = lean_unsigned_to_nat(0);
    v___x_1215_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1215_, 0, v_s_1213_);
    lean_ctor_set(v___x_1215_, 1, v___x_1214_);
    return v___x_1215_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0(
    mut v_inst_1216_: *mut LeanObject,
    mut v_x_1217_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1222_: u8 = 0;
    let mut v_str_1223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1227_: u8 = 0;
    let mut v___x_1228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: u8 = 0;
    let mut v___x_1236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1240_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1218_ = lean_ctor_get(v_x_1217_, 0);
                v_offset_1219_ = lean_ctor_get(v_x_1217_, 1);
                v_isSharedCheck_1240_ = (!lean_is_exclusive(v_x_1217_)) as u8;
                if v_isSharedCheck_1240_ == 0 {
                    v___x_1221_ = v_x_1217_;
                    v_isShared_1222_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_offset_1219_);
                    lean_inc(v_s_1218_);
                    lean_dec(v_x_1217_);
                    v___x_1221_ = lean_box(0);
                    v_isShared_1222_ = v_isSharedCheck_1240_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_str_1223_ = lean_ctor_get(v_s_1218_, 0);
                lean_inc_ref(v_str_1223_);
                v_startInclusive_1224_ = lean_ctor_get(v_s_1218_, 1);
                lean_inc(v_startInclusive_1224_);
                v_endExclusive_1225_ = lean_ctor_get(v_s_1218_, 2);
                v___x_1226_ = lean_nat_sub(v_endExclusive_1225_, v_startInclusive_1224_);
                v___x_1227_ = lean_nat_dec_lt(v_offset_1219_, v___x_1226_);
                lean_dec(v___x_1226_);
                if v___x_1227_ == 0 {
                    lean_dec(v_startInclusive_1224_);
                    lean_dec_ref(v_str_1223_);
                    lean_del_object(v___x_1221_);
                    lean_dec(v_offset_1219_);
                    lean_dec_ref(v_s_1218_);
                    v___x_1228_ = lean_box(2);
                    v___x_1229_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1228_);
                    return v___x_1229_;
                } else {
                    v___x_1230_ = lean_unsigned_to_nat(1);
                    v___x_1231_ = lean_nat_add(v_offset_1219_, v___x_1230_);
                    if v_isShared_1222_ == 0 {
                        lean_ctor_set(v___x_1221_, 1, v___x_1231_);
                        v___x_1233_ = v___x_1221_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1239_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1239_, 0, v_s_1218_);
                        lean_ctor_set(v_reuseFailAlloc_1239_, 1, v___x_1231_);
                        v___x_1233_ = v_reuseFailAlloc_1239_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1234_ = lean_nat_add(v_startInclusive_1224_, v_offset_1219_);
                lean_dec(v_offset_1219_);
                lean_dec(v_startInclusive_1224_);
                v___x_1235_ = lean_string_get_byte_fast(v_str_1223_, v___x_1234_);
                lean_dec_ref(v_str_1223_);
                v___x_1236_ = lean_box((v___x_1235_) as usize);
                v___x_1237_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1237_, 0, v___x_1233_);
                lean_ctor_set(v___x_1237_, 1, v___x_1236_);
                v___x_1238_ = lean_apply_2(v_inst_1216_, lean_box(0), v___x_1237_);
                return v___x_1238_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg(
    mut v_inst_1241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1242_: *mut LeanObject = core::ptr::null_mut();
    v___f_1242_ = lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1242_, 0, v_inst_1241_);
    return v___f_1242_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorUInt8OfPure(
    mut v_m_1243_: *mut LeanObject,
    mut v_inst_1244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1245_: *mut LeanObject = core::ptr::null_mut();
    v___f_1245_ = lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1245_, 0, v_inst_1244_);
    return v___f_1245_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(
    mut v_m_1246_: *mut LeanObject,
    mut v_inst_1247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1248_: *mut LeanObject = core::ptr::null_mut();
    v___x_1248_ = lean_box(0);
    return v___x_1248_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation___boxed(
    mut v_m_1249_: *mut LeanObject,
    mut v_inst_1250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1251_: *mut LeanObject = core::ptr::null_mut();
    v_res_1251_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_ByteIterator_finitenessRelation(
            v_m_1249_,
            v_inst_1250_,
        );
    lean_dec(v_inst_1250_);
    return v_res_1251_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(
    mut v_toPure_1252_: *mut LeanObject,
    mut v_recur_1253_: *mut LeanObject,
    mut v_it_1254_: *mut LeanObject,
    mut v_____do__lift_1255_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1255_) == 0 {
        let mut v_a_1256_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1257_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_1254_);
        lean_dec(v_recur_1253_);
        v_a_1256_ = lean_ctor_get(v_____do__lift_1255_, 0);
        lean_inc(v_a_1256_);
        lean_dec_ref_known(v_____do__lift_1255_, 1);
        v___x_1257_ = lean_apply_2(v_toPure_1252_, lean_box(0), v_a_1256_);
        return v___x_1257_;
    } else {
        let mut v_a_1258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1259_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1252_);
        v_a_1258_ = lean_ctor_get(v_____do__lift_1255_, 0);
        lean_inc(v_a_1258_);
        lean_dec_ref_known(v_____do__lift_1255_, 1);
        v___x_1259_ = lean_apply_4(
            v_recur_1253_,
            v_it_1254_,
            v_a_1258_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1259_;
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(
    mut v_toPure_1260_: *mut LeanObject,
    mut v_recur_1261_: *mut LeanObject,
    mut v___y_1262_: *mut LeanObject,
    mut v_acc_1263_: *mut LeanObject,
    mut v_toBind_1264_: *mut LeanObject,
    mut v_s_1265_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_1265_) {
        0 => {
            let mut v_it_1266_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1267_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1268_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1269_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1270_: *mut LeanObject = core::ptr::null_mut();
            v_it_1266_ = lean_ctor_get(v_s_1265_, 0);
            lean_inc(v_it_1266_);
            v_out_1267_ = lean_ctor_get(v_s_1265_, 1);
            lean_inc(v_out_1267_);
            lean_dec_ref_known(v_s_1265_, 2);
            v___f_1268_ = lean_alloc_closure(
                l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_1268_, 0, v_toPure_1260_);
            lean_closure_set(v___f_1268_, 1, v_recur_1261_);
            lean_closure_set(v___f_1268_, 2, v_it_1266_);
            v___x_1269_ = lean_apply_3(v___y_1262_, v_out_1267_, lean_box(0), v_acc_1263_);
            v___x_1270_ = lean_apply_4(
                v_toBind_1264_,
                lean_box(0),
                lean_box(0),
                v___x_1269_,
                v___f_1268_,
            );
            return v___x_1270_;
        }
        1 => {
            let mut v_it_1271_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1272_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1264_);
            lean_dec(v___y_1262_);
            lean_dec(v_toPure_1260_);
            v_it_1271_ = lean_ctor_get(v_s_1265_, 0);
            lean_inc(v_it_1271_);
            lean_dec_ref_known(v_s_1265_, 1);
            v___x_1272_ = lean_apply_4(
                v_recur_1261_,
                v_it_1271_,
                v_acc_1263_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1272_;
        }
        _ => {
            let mut v___x_1273_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1264_);
            lean_dec(v___y_1262_);
            lean_dec(v_recur_1261_);
            v___x_1273_ = lean_apply_2(v_toPure_1260_, lean_box(0), v_acc_1263_);
            return v___x_1273_;
        }
    }
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(
    mut v_toPure_1274_: *mut LeanObject,
    mut v___y_1275_: *mut LeanObject,
    mut v_toBind_1276_: *mut LeanObject,
    mut v_toPure_1277_: *mut LeanObject,
    mut v_lift_1278_: *mut LeanObject,
    mut v_it_1279_: *mut LeanObject,
    mut v_acc_1280_: *mut LeanObject,
    mut v_hP_1281_: *mut LeanObject,
    mut v_recur_1282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1287_: u8 = 0;
    let mut v_str_1288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1293_: u8 = 0;
    let mut v___x_1294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1297_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1302_: u8 = 0;
    let mut v___x_1303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1308_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1283_ = lean_ctor_get(v_it_1279_, 0);
                v_offset_1284_ = lean_ctor_get(v_it_1279_, 1);
                v_isSharedCheck_1308_ = (!lean_is_exclusive(v_it_1279_)) as u8;
                if v_isSharedCheck_1308_ == 0 {
                    v___x_1286_ = v_it_1279_;
                    v_isShared_1287_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_offset_1284_);
                    lean_inc(v_s_1283_);
                    lean_dec(v_it_1279_);
                    v___x_1286_ = lean_box(0);
                    v_isShared_1287_ = v_isSharedCheck_1308_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_str_1288_ = lean_ctor_get(v_s_1283_, 0);
                lean_inc_ref(v_str_1288_);
                v_startInclusive_1289_ = lean_ctor_get(v_s_1283_, 1);
                lean_inc(v_startInclusive_1289_);
                v_endExclusive_1290_ = lean_ctor_get(v_s_1283_, 2);
                v___f_1291_ = lean_alloc_closure(
                    l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___f_1291_, 0, v_toPure_1274_);
                lean_closure_set(v___f_1291_, 1, v_recur_1282_);
                lean_closure_set(v___f_1291_, 2, v___y_1275_);
                lean_closure_set(v___f_1291_, 3, v_acc_1280_);
                lean_closure_set(v___f_1291_, 4, v_toBind_1276_);
                v___x_1292_ = lean_nat_sub(v_endExclusive_1290_, v_startInclusive_1289_);
                v___x_1293_ = lean_nat_dec_lt(v_offset_1284_, v___x_1292_);
                lean_dec(v___x_1292_);
                if v___x_1293_ == 0 {
                    lean_dec(v_startInclusive_1289_);
                    lean_dec_ref(v_str_1288_);
                    lean_del_object(v___x_1286_);
                    lean_dec(v_offset_1284_);
                    lean_dec_ref(v_s_1283_);
                    v___x_1294_ = lean_box(2);
                    v___x_1295_ = lean_apply_2(v_toPure_1277_, lean_box(0), v___x_1294_);
                    v___x_1296_ = lean_apply_4(
                        v_lift_1278_,
                        lean_box(0),
                        lean_box(0),
                        v___f_1291_,
                        v___x_1295_,
                    );
                    return v___x_1296_;
                } else {
                    v___x_1297_ = lean_unsigned_to_nat(1);
                    v___x_1298_ = lean_nat_add(v_offset_1284_, v___x_1297_);
                    if v_isShared_1287_ == 0 {
                        lean_ctor_set(v___x_1286_, 1, v___x_1298_);
                        v___x_1300_ = v___x_1286_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1307_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1307_, 0, v_s_1283_);
                        lean_ctor_set(v_reuseFailAlloc_1307_, 1, v___x_1298_);
                        v___x_1300_ = v_reuseFailAlloc_1307_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_1301_ = lean_nat_add(v_startInclusive_1289_, v_offset_1284_);
                lean_dec(v_offset_1284_);
                lean_dec(v_startInclusive_1289_);
                v___x_1302_ = lean_string_get_byte_fast(v_str_1288_, v___x_1301_);
                lean_dec_ref(v_str_1288_);
                v___x_1303_ = lean_box((v___x_1302_) as usize);
                v___x_1304_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1304_, 0, v___x_1300_);
                lean_ctor_set(v___x_1304_, 1, v___x_1303_);
                v___x_1305_ = lean_apply_2(v_toPure_1277_, lean_box(0), v___x_1304_);
                v___x_1306_ = lean_apply_4(
                    v_lift_1278_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1309_: *mut LeanObject,
    mut v_toPure_1310_: *mut LeanObject,
    mut v_lift_1311_: *mut LeanObject,
    mut v_00_u03b3_1312_: *mut LeanObject,
    mut v_Pl_1313_: *mut LeanObject,
    mut v_it_1314_: *mut LeanObject,
    mut v_init_1315_: *mut LeanObject,
    mut v___y_1316_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1321_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1317_ = lean_ctor_get(v_inst_1309_, 0);
    lean_inc_ref(v_toApplicative_1317_);
    v_toBind_1318_ = lean_ctor_get(v_inst_1309_, 1);
    lean_inc(v_toBind_1318_);
    lean_dec_ref(v_inst_1309_);
    v_toPure_1319_ = lean_ctor_get(v_toApplicative_1317_, 1);
    lean_inc(v_toPure_1319_);
    lean_dec_ref(v_toApplicative_1317_);
    v___f_1320_ = lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_1320_, 0, v_toPure_1319_);
    lean_closure_set(v___f_1320_, 1, v___y_1316_);
    lean_closure_set(v___f_1320_, 2, v_toBind_1318_);
    lean_closure_set(v___f_1320_, 3, v_toPure_1310_);
    lean_closure_set(v___f_1320_, 4, v_lift_1311_);
    v___x_1321_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1320_, v_it_1314_, v_init_1315_, lean_box(0));
    return v___x_1321_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(
    mut v_inst_1322_: *mut LeanObject,
    mut v_inst_1323_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1326_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1324_ = lean_ctor_get(v_inst_1322_, 0);
    lean_inc_ref(v_toApplicative_1324_);
    lean_dec_ref(v_inst_1322_);
    v_toPure_1325_ = lean_ctor_get(v_toApplicative_1324_, 1);
    lean_inc(v_toPure_1325_);
    lean_dec_ref(v_toApplicative_1324_);
    v___f_1326_ = lean_alloc_closure(
        l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_1326_, 0, v_inst_1323_);
    lean_closure_set(v___f_1326_, 1, v_toPure_1325_);
    return v___f_1326_;
}
pub unsafe fn l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad(
    mut v_m_1327_: *mut LeanObject,
    mut v_n_1328_: *mut LeanObject,
    mut v_inst_1329_: *mut LeanObject,
    mut v_inst_1330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1331_: *mut LeanObject = core::ptr::null_mut();
    v___x_1331_ = l_String_Slice_ByteIterator_instIteratorLoopUInt8OfMonad___redArg(
        v_inst_1329_,
        v_inst_1330_,
    );
    return v___x_1331_;
}
pub unsafe fn l_String_Slice_revBytes(mut v_s_1332_: *mut LeanObject) -> *mut LeanObject {
    let mut v_startInclusive_1333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1336_: *mut LeanObject = core::ptr::null_mut();
    v_startInclusive_1333_ = lean_ctor_get(v_s_1332_, 1);
    v_endExclusive_1334_ = lean_ctor_get(v_s_1332_, 2);
    v___x_1335_ = lean_nat_sub(v_endExclusive_1334_, v_startInclusive_1333_);
    v___x_1336_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_1336_, 0, v_s_1332_);
    lean_ctor_set(v___x_1336_, 1, v___x_1335_);
    return v___x_1336_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0(
    mut v_inst_1341_: *mut LeanObject,
    mut v_x_1342_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1347_: u8 = 0;
    let mut v___x_1348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1349_: u8 = 0;
    let mut v_str_1350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_1353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1357_: u8 = 0;
    let mut v___x_1358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1364_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1343_ = lean_ctor_get(v_x_1342_, 0);
                v_offset_1344_ = lean_ctor_get(v_x_1342_, 1);
                v_isSharedCheck_1364_ = (!lean_is_exclusive(v_x_1342_)) as u8;
                if v_isSharedCheck_1364_ == 0 {
                    v___x_1346_ = v_x_1342_;
                    v_isShared_1347_ = v_isSharedCheck_1364_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_offset_1344_);
                    lean_inc(v_s_1343_);
                    lean_dec(v_x_1342_);
                    v___x_1346_ = lean_box(0);
                    v_isShared_1347_ = v_isSharedCheck_1364_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_1348_ = lean_unsigned_to_nat(0);
                v___x_1349_ = lean_nat_dec_eq(v_offset_1344_, v___x_1348_);
                if v___x_1349_ == 0 {
                    v_str_1350_ = lean_ctor_get(v_s_1343_, 0);
                    lean_inc_ref(v_str_1350_);
                    v_startInclusive_1351_ = lean_ctor_get(v_s_1343_, 1);
                    lean_inc(v_startInclusive_1351_);
                    v___x_1352_ = lean_unsigned_to_nat(1);
                    v_nextOffset_1353_ = lean_nat_sub(v_offset_1344_, v___x_1352_);
                    lean_dec(v_offset_1344_);
                    lean_inc(v_nextOffset_1353_);
                    if v_isShared_1347_ == 0 {
                        lean_ctor_set(v___x_1346_, 1, v_nextOffset_1353_);
                        v___x_1355_ = v___x_1346_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1361_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1361_, 0, v_s_1343_);
                        lean_ctor_set(v_reuseFailAlloc_1361_, 1, v_nextOffset_1353_);
                        v___x_1355_ = v_reuseFailAlloc_1361_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1346_);
                    lean_dec(v_offset_1344_);
                    lean_dec_ref(v_s_1343_);
                    v___x_1362_ = lean_box(2);
                    v___x_1363_ = lean_apply_2(v_inst_1341_, lean_box(0), v___x_1362_);
                    return v___x_1363_;
                }
            }
            2 => {
                v___x_1356_ = lean_nat_add(v_startInclusive_1351_, v_nextOffset_1353_);
                lean_dec(v_nextOffset_1353_);
                lean_dec(v_startInclusive_1351_);
                v___x_1357_ = lean_string_get_byte_fast(v_str_1350_, v___x_1356_);
                lean_dec_ref(v_str_1350_);
                v___x_1358_ = lean_box((v___x_1357_) as usize);
                v___x_1359_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1359_, 0, v___x_1355_);
                lean_ctor_set(v___x_1359_, 1, v___x_1358_);
                v___x_1360_ = lean_apply_2(v_inst_1341_, lean_box(0), v___x_1359_);
                return v___x_1360_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg(
    mut v_inst_1365_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1366_: *mut LeanObject = core::ptr::null_mut();
    v___f_1366_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1366_, 0, v_inst_1365_);
    return v___f_1366_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorUInt8OfPure(
    mut v_m_1367_: *mut LeanObject,
    mut v_inst_1368_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1369_: *mut LeanObject = core::ptr::null_mut();
    v___f_1369_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorUInt8OfPure___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1369_, 0, v_inst_1368_);
    return v___f_1369_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(
    mut v_m_1370_: *mut LeanObject,
    mut v_inst_1371_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1372_: *mut LeanObject = core::ptr::null_mut();
    v___x_1372_ = lean_box(0);
    return v___x_1372_;
}
pub unsafe fn l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation___boxed(
    mut v_m_1373_: *mut LeanObject,
    mut v_inst_1374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1375_: *mut LeanObject = core::ptr::null_mut();
    v_res_1375_ =
        l___private_Init_Data_String_Iterate_0__String_Slice_RevByteIterator_finitenessRelation(
            v_m_1373_,
            v_inst_1374_,
        );
    lean_dec(v_inst_1374_);
    return v_res_1375_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0(
    mut v_toPure_1376_: *mut LeanObject,
    mut v_recur_1377_: *mut LeanObject,
    mut v_it_1378_: *mut LeanObject,
    mut v_____do__lift_1379_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1379_) == 0 {
        let mut v_a_1380_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1381_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref(v_it_1378_);
        lean_dec(v_recur_1377_);
        v_a_1380_ = lean_ctor_get(v_____do__lift_1379_, 0);
        lean_inc(v_a_1380_);
        lean_dec_ref_known(v_____do__lift_1379_, 1);
        v___x_1381_ = lean_apply_2(v_toPure_1376_, lean_box(0), v_a_1380_);
        return v___x_1381_;
    } else {
        let mut v_a_1382_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1383_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1376_);
        v_a_1382_ = lean_ctor_get(v_____do__lift_1379_, 0);
        lean_inc(v_a_1382_);
        lean_dec_ref_known(v_____do__lift_1379_, 1);
        v___x_1383_ = lean_apply_4(
            v_recur_1377_,
            v_it_1378_,
            v_a_1382_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1383_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1(
    mut v_toPure_1384_: *mut LeanObject,
    mut v_recur_1385_: *mut LeanObject,
    mut v___y_1386_: *mut LeanObject,
    mut v_acc_1387_: *mut LeanObject,
    mut v_toBind_1388_: *mut LeanObject,
    mut v_s_1389_: *mut LeanObject,
) -> *mut LeanObject {
    match lean_obj_tag(v_s_1389_) {
        0 => {
            let mut v_it_1390_: *mut LeanObject = core::ptr::null_mut();
            let mut v_out_1391_: *mut LeanObject = core::ptr::null_mut();
            let mut v___f_1392_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1393_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1394_: *mut LeanObject = core::ptr::null_mut();
            v_it_1390_ = lean_ctor_get(v_s_1389_, 0);
            lean_inc(v_it_1390_);
            v_out_1391_ = lean_ctor_get(v_s_1389_, 1);
            lean_inc(v_out_1391_);
            lean_dec_ref_known(v_s_1389_, 2);
            v___f_1392_ = lean_alloc_closure(
                l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__0
                    as *mut core::ffi::c_void,
                4,
                3,
            );
            lean_closure_set(v___f_1392_, 0, v_toPure_1384_);
            lean_closure_set(v___f_1392_, 1, v_recur_1385_);
            lean_closure_set(v___f_1392_, 2, v_it_1390_);
            v___x_1393_ = lean_apply_3(v___y_1386_, v_out_1391_, lean_box(0), v_acc_1387_);
            v___x_1394_ = lean_apply_4(
                v_toBind_1388_,
                lean_box(0),
                lean_box(0),
                v___x_1393_,
                v___f_1392_,
            );
            return v___x_1394_;
        }
        1 => {
            let mut v_it_1395_: *mut LeanObject = core::ptr::null_mut();
            let mut v___x_1396_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1388_);
            lean_dec(v___y_1386_);
            lean_dec(v_toPure_1384_);
            v_it_1395_ = lean_ctor_get(v_s_1389_, 0);
            lean_inc(v_it_1395_);
            lean_dec_ref_known(v_s_1389_, 1);
            v___x_1396_ = lean_apply_4(
                v_recur_1385_,
                v_it_1395_,
                v_acc_1387_,
                lean_box(0),
                lean_box(0),
            );
            return v___x_1396_;
        }
        _ => {
            let mut v___x_1397_: *mut LeanObject = core::ptr::null_mut();
            lean_dec(v_toBind_1388_);
            lean_dec(v___y_1386_);
            lean_dec(v_recur_1385_);
            v___x_1397_ = lean_apply_2(v_toPure_1384_, lean_box(0), v_acc_1387_);
            return v___x_1397_;
        }
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2(
    mut v_toPure_1398_: *mut LeanObject,
    mut v___y_1399_: *mut LeanObject,
    mut v_toBind_1400_: *mut LeanObject,
    mut v_toPure_1401_: *mut LeanObject,
    mut v_lift_1402_: *mut LeanObject,
    mut v_it_1403_: *mut LeanObject,
    mut v_acc_1404_: *mut LeanObject,
    mut v_hP_1405_: *mut LeanObject,
    mut v_recur_1406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_s_1407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_offset_1408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1411_: u8 = 0;
    let mut v___f_1412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1414_: u8 = 0;
    let mut v_str_1415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextOffset_1418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1420_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1422_: u8 = 0;
    let mut v___x_1423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_s_1407_ = lean_ctor_get(v_it_1403_, 0);
                v_offset_1408_ = lean_ctor_get(v_it_1403_, 1);
                v_isSharedCheck_1431_ = (!lean_is_exclusive(v_it_1403_)) as u8;
                if v_isSharedCheck_1431_ == 0 {
                    v___x_1410_ = v_it_1403_;
                    v_isShared_1411_ = v_isSharedCheck_1431_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_offset_1408_);
                    lean_inc(v_s_1407_);
                    lean_dec(v_it_1403_);
                    v___x_1410_ = lean_box(0);
                    v_isShared_1411_ = v_isSharedCheck_1431_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_1412_ = lean_alloc_closure(
                    l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__1
                        as *mut core::ffi::c_void,
                    6,
                    5,
                );
                lean_closure_set(v___f_1412_, 0, v_toPure_1398_);
                lean_closure_set(v___f_1412_, 1, v_recur_1406_);
                lean_closure_set(v___f_1412_, 2, v___y_1399_);
                lean_closure_set(v___f_1412_, 3, v_acc_1404_);
                lean_closure_set(v___f_1412_, 4, v_toBind_1400_);
                v___x_1413_ = lean_unsigned_to_nat(0);
                v___x_1414_ = lean_nat_dec_eq(v_offset_1408_, v___x_1413_);
                if v___x_1414_ == 0 {
                    v_str_1415_ = lean_ctor_get(v_s_1407_, 0);
                    lean_inc_ref(v_str_1415_);
                    v_startInclusive_1416_ = lean_ctor_get(v_s_1407_, 1);
                    lean_inc(v_startInclusive_1416_);
                    v___x_1417_ = lean_unsigned_to_nat(1);
                    v_nextOffset_1418_ = lean_nat_sub(v_offset_1408_, v___x_1417_);
                    lean_dec(v_offset_1408_);
                    lean_inc(v_nextOffset_1418_);
                    if v_isShared_1411_ == 0 {
                        lean_ctor_set(v___x_1410_, 1, v_nextOffset_1418_);
                        v___x_1420_ = v___x_1410_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1427_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1427_, 0, v_s_1407_);
                        lean_ctor_set(v_reuseFailAlloc_1427_, 1, v_nextOffset_1418_);
                        v___x_1420_ = v_reuseFailAlloc_1427_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_1410_);
                    lean_dec(v_offset_1408_);
                    lean_dec_ref(v_s_1407_);
                    v___x_1428_ = lean_box(2);
                    v___x_1429_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1428_);
                    v___x_1430_ = lean_apply_4(
                        v_lift_1402_,
                        lean_box(0),
                        lean_box(0),
                        v___f_1412_,
                        v___x_1429_,
                    );
                    return v___x_1430_;
                }
            }
            2 => {
                v___x_1421_ = lean_nat_add(v_startInclusive_1416_, v_nextOffset_1418_);
                lean_dec(v_nextOffset_1418_);
                lean_dec(v_startInclusive_1416_);
                v___x_1422_ = lean_string_get_byte_fast(v_str_1415_, v___x_1421_);
                lean_dec_ref(v_str_1415_);
                v___x_1423_ = lean_box((v___x_1422_) as usize);
                v___x_1424_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_1424_, 0, v___x_1420_);
                lean_ctor_set(v___x_1424_, 1, v___x_1423_);
                v___x_1425_ = lean_apply_2(v_toPure_1401_, lean_box(0), v___x_1424_);
                v___x_1426_ = lean_apply_4(
                    v_lift_1402_,
                    lean_box(0),
                    lean_box(0),
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
    mut v_inst_1432_: *mut LeanObject,
    mut v_toPure_1433_: *mut LeanObject,
    mut v_lift_1434_: *mut LeanObject,
    mut v_00_u03b3_1435_: *mut LeanObject,
    mut v_Pl_1436_: *mut LeanObject,
    mut v_it_1437_: *mut LeanObject,
    mut v_init_1438_: *mut LeanObject,
    mut v___y_1439_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1444_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1440_ = lean_ctor_get(v_inst_1432_, 0);
    lean_inc_ref(v_toApplicative_1440_);
    v_toBind_1441_ = lean_ctor_get(v_inst_1432_, 1);
    lean_inc(v_toBind_1441_);
    lean_dec_ref(v_inst_1432_);
    v_toPure_1442_ = lean_ctor_get(v_toApplicative_1440_, 1);
    lean_inc(v_toPure_1442_);
    lean_dec_ref(v_toApplicative_1440_);
    v___f_1443_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__2
            as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_1443_, 0, v_toPure_1442_);
    lean_closure_set(v___f_1443_, 1, v___y_1439_);
    lean_closure_set(v___f_1443_, 2, v_toBind_1441_);
    lean_closure_set(v___f_1443_, 3, v_toPure_1433_);
    lean_closure_set(v___f_1443_, 4, v_lift_1434_);
    v___x_1444_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1443_, v_it_1437_, v_init_1438_, lean_box(0));
    return v___x_1444_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(
    mut v_inst_1445_: *mut LeanObject,
    mut v_inst_1446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1447_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1449_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1447_ = lean_ctor_get(v_inst_1445_, 0);
    lean_inc_ref(v_toApplicative_1447_);
    lean_dec_ref(v_inst_1445_);
    v_toPure_1448_ = lean_ctor_get(v_toApplicative_1447_, 1);
    lean_inc(v_toPure_1448_);
    lean_dec_ref(v_toApplicative_1447_);
    v___f_1449_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        8,
        2,
    );
    lean_closure_set(v___f_1449_, 0, v_inst_1446_);
    lean_closure_set(v___f_1449_, 1, v_toPure_1448_);
    return v___f_1449_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad(
    mut v_m_1450_: *mut LeanObject,
    mut v_n_1451_: *mut LeanObject,
    mut v_inst_1452_: *mut LeanObject,
    mut v_inst_1453_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1454_: *mut LeanObject = core::ptr::null_mut();
    v___x_1454_ = l_String_Slice_RevByteIterator_instIteratorLoopUInt8OfMonad___redArg(
        v_inst_1452_,
        v_inst_1453_,
    );
    return v___x_1454_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0(
    mut v_toPure_1455_: *mut LeanObject,
    mut v_____do__lift_1456_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1457_: *mut LeanObject = core::ptr::null_mut();
    v___x_1457_ = lean_apply_2(v_toPure_1455_, lean_box(0), v_____do__lift_1456_);
    return v___x_1457_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1(
    mut v_toPure_1458_: *mut LeanObject,
    mut v_recur_1459_: *mut LeanObject,
    mut v___x_1460_: *mut LeanObject,
    mut v_____do__lift_1461_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_1461_) == 0 {
        let mut v_a_1462_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1463_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v___x_1460_);
        lean_dec(v_recur_1459_);
        v_a_1462_ = lean_ctor_get(v_____do__lift_1461_, 0);
        lean_inc(v_a_1462_);
        lean_dec_ref_known(v_____do__lift_1461_, 1);
        v___x_1463_ = lean_apply_2(v_toPure_1458_, lean_box(0), v_a_1462_);
        return v___x_1463_;
    } else {
        let mut v_a_1464_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1465_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_toPure_1458_);
        v_a_1464_ = lean_ctor_get(v_____do__lift_1461_, 0);
        lean_inc(v_a_1464_);
        lean_dec_ref_known(v_____do__lift_1461_, 1);
        v___x_1465_ = lean_apply_4(
            v_recur_1459_,
            v___x_1460_,
            v_a_1464_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1465_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2(
    mut v_s_1466_: *mut LeanObject,
    mut v_toPure_1467_: *mut LeanObject,
    mut v_f_1468_: *mut LeanObject,
    mut v_toBind_1469_: *mut LeanObject,
    mut v___f_1470_: *mut LeanObject,
    mut v_it_1471_: *mut LeanObject,
    mut v_acc_1472_: *mut LeanObject,
    mut v_hP_1473_: *mut LeanObject,
    mut v_recur_1474_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1479_: u8 = 0;
    v_str_1475_ = lean_ctor_get(v_s_1466_, 0);
    v_startInclusive_1476_ = lean_ctor_get(v_s_1466_, 1);
    v_endExclusive_1477_ = lean_ctor_get(v_s_1466_, 2);
    v___x_1478_ = lean_nat_sub(v_endExclusive_1477_, v_startInclusive_1476_);
    v___x_1479_ = lean_nat_dec_eq(v_it_1471_, v___x_1478_);
    lean_dec(v___x_1478_);
    if v___x_1479_ == 0 {
        let mut v___x_1480_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1481_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1482_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1483_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1484_: u32 = 0;
        let mut v___x_1485_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1486_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1487_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1488_: *mut LeanObject = core::ptr::null_mut();
        v___x_1480_ = lean_nat_add(v_startInclusive_1476_, v_it_1471_);
        v___x_1481_ = lean_string_utf8_next_fast(v_str_1475_, v___x_1480_);
        v___x_1482_ = lean_nat_sub(v___x_1481_, v_startInclusive_1476_);
        v___f_1483_ = lean_alloc_closure(
            l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1483_, 0, v_toPure_1467_);
        lean_closure_set(v___f_1483_, 1, v_recur_1474_);
        lean_closure_set(v___f_1483_, 2, v___x_1482_);
        v___x_1484_ = lean_string_utf8_get_fast(v_str_1475_, v___x_1480_);
        lean_dec(v___x_1480_);
        v___x_1485_ = lean_box_uint32(v___x_1484_);
        v___x_1486_ = lean_apply_2(v_f_1468_, v___x_1485_, v_acc_1472_);
        lean_inc(v_toBind_1469_);
        v___x_1487_ = lean_apply_4(
            v_toBind_1469_,
            lean_box(0),
            lean_box(0),
            v___x_1486_,
            v___f_1470_,
        );
        v___x_1488_ = lean_apply_4(
            v_toBind_1469_,
            lean_box(0),
            lean_box(0),
            v___x_1487_,
            v___f_1483_,
        );
        return v___x_1488_;
    } else {
        let mut v___x_1489_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_recur_1474_);
        lean_dec(v___f_1470_);
        lean_dec(v_toBind_1469_);
        lean_dec(v_f_1468_);
        v___x_1489_ = lean_apply_2(v_toPure_1467_, lean_box(0), v_acc_1472_);
        return v___x_1489_;
    }
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed(
    mut v_s_1490_: *mut LeanObject,
    mut v_toPure_1491_: *mut LeanObject,
    mut v_f_1492_: *mut LeanObject,
    mut v_toBind_1493_: *mut LeanObject,
    mut v___f_1494_: *mut LeanObject,
    mut v_it_1495_: *mut LeanObject,
    mut v_acc_1496_: *mut LeanObject,
    mut v_hP_1497_: *mut LeanObject,
    mut v_recur_1498_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1499_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_1495_);
    lean_dec_ref(v_s_1490_);
    return v_res_1499_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3(
    mut v_inst_1500_: *mut LeanObject,
    mut v_00_u03b2_1501_: *mut LeanObject,
    mut v_s_1502_: *mut LeanObject,
    mut v_b_1503_: *mut LeanObject,
    mut v_f_1504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1511_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1505_ = lean_ctor_get(v_inst_1500_, 0);
    lean_inc_ref(v_toApplicative_1505_);
    v_toBind_1506_ = lean_ctor_get(v_inst_1500_, 1);
    lean_inc(v_toBind_1506_);
    lean_dec_ref(v_inst_1500_);
    v_toPure_1507_ = lean_ctor_get(v_toApplicative_1505_, 1);
    lean_inc_n(v_toPure_1507_, 2);
    lean_dec_ref(v_toApplicative_1505_);
    v___x_1508_ = lean_unsigned_to_nat(0);
    v___f_1509_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1509_, 0, v_toPure_1507_);
    v___f_1510_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__2___boxed
            as *mut core::ffi::c_void,
        9,
        5,
    );
    lean_closure_set(v___f_1510_, 0, v_s_1502_);
    lean_closure_set(v___f_1510_, 1, v_toPure_1507_);
    lean_closure_set(v___f_1510_, 2, v_f_1504_);
    lean_closure_set(v___f_1510_, 3, v_toBind_1506_);
    lean_closure_set(v___f_1510_, 4, v___f_1509_);
    v___x_1511_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1510_, v___x_1508_, v_b_1503_, lean_box(0));
    return v___x_1511_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg(
    mut v_inst_1512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1513_: *mut LeanObject = core::ptr::null_mut();
    v___f_1513_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1513_, 0, v_inst_1512_);
    return v___f_1513_;
}
pub unsafe fn l_String_Slice_RevByteIterator_instForInCharOfMonad(
    mut v_m_1514_: *mut LeanObject,
    mut v_inst_1515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1516_: *mut LeanObject = core::ptr::null_mut();
    v___f_1516_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__3
            as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1516_, 0, v_inst_1515_);
    return v___f_1516_;
}
pub unsafe fn l_String_Slice_foldl___redArg___lam__0(
    mut v_s_1517_: *mut LeanObject,
    mut v_f_1518_: *mut LeanObject,
    mut v_it_1519_: *mut LeanObject,
    mut v_acc_1520_: *mut LeanObject,
    mut v_hP_1521_: *mut LeanObject,
    mut v_recur_1522_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_str_1523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_startInclusive_1524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1525_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: u8 = 0;
    v_str_1523_ = lean_ctor_get(v_s_1517_, 0);
    v_startInclusive_1524_ = lean_ctor_get(v_s_1517_, 1);
    v_endExclusive_1525_ = lean_ctor_get(v_s_1517_, 2);
    v___x_1526_ = lean_nat_sub(v_endExclusive_1525_, v_startInclusive_1524_);
    v___x_1527_ = lean_nat_dec_eq(v_it_1519_, v___x_1526_);
    lean_dec(v___x_1526_);
    if v___x_1527_ == 0 {
        let mut v___x_1528_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1529_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1530_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1531_: u32 = 0;
        let mut v___x_1532_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1533_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1534_: *mut LeanObject = core::ptr::null_mut();
        v___x_1528_ = lean_nat_add(v_startInclusive_1524_, v_it_1519_);
        v___x_1529_ = lean_string_utf8_next_fast(v_str_1523_, v___x_1528_);
        v___x_1530_ = lean_nat_sub(v___x_1529_, v_startInclusive_1524_);
        v___x_1531_ = lean_string_utf8_get_fast(v_str_1523_, v___x_1528_);
        lean_dec(v___x_1528_);
        v___x_1532_ = lean_box_uint32(v___x_1531_);
        v___x_1533_ = lean_apply_2(v_f_1518_, v_acc_1520_, v___x_1532_);
        v___x_1534_ = lean_apply_4(
            v_recur_1522_,
            v___x_1530_,
            v___x_1533_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1534_;
    } else {
        lean_dec(v_recur_1522_);
        lean_dec(v_f_1518_);
        return v_acc_1520_;
    }
}
pub unsafe fn l_String_Slice_foldl___redArg___lam__0___boxed(
    mut v_s_1535_: *mut LeanObject,
    mut v_f_1536_: *mut LeanObject,
    mut v_it_1537_: *mut LeanObject,
    mut v_acc_1538_: *mut LeanObject,
    mut v_hP_1539_: *mut LeanObject,
    mut v_recur_1540_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1541_: *mut LeanObject = core::ptr::null_mut();
    v_res_1541_ = l_String_Slice_foldl___redArg___lam__0(
        v_s_1535_,
        v_f_1536_,
        v_it_1537_,
        v_acc_1538_,
        v_hP_1539_,
        v_recur_1540_,
    );
    lean_dec(v_it_1537_);
    lean_dec_ref(v_s_1535_);
    return v_res_1541_;
}
pub unsafe fn l_String_Slice_foldl___redArg(
    mut v_f_1542_: *mut LeanObject,
    mut v_init_1543_: *mut LeanObject,
    mut v_s_1544_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1545_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1547_: *mut LeanObject = core::ptr::null_mut();
    v___f_1545_ = lean_alloc_closure(
        l_String_Slice_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_1545_, 0, v_s_1544_);
    lean_closure_set(v___f_1545_, 1, v_f_1542_);
    v___x_1546_ = lean_unsigned_to_nat(0);
    v___x_1547_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1545_, v___x_1546_, v_init_1543_, lean_box(0));
    return v___x_1547_;
}
pub unsafe fn l_String_Slice_foldl(
    mut v_00_u03b1_1548_: *mut LeanObject,
    mut v_f_1549_: *mut LeanObject,
    mut v_init_1550_: *mut LeanObject,
    mut v_s_1551_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1554_: *mut LeanObject = core::ptr::null_mut();
    v___f_1552_ = lean_alloc_closure(
        l_String_Slice_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_1552_, 0, v_s_1551_);
    lean_closure_set(v___f_1552_, 1, v_f_1549_);
    v___x_1553_ = lean_unsigned_to_nat(0);
    v___x_1554_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1552_, v___x_1553_, v_init_1550_, lean_box(0));
    return v___x_1554_;
}
pub unsafe fn l_String_Slice_foldr___redArg___lam__0(
    mut v_s_1555_: *mut LeanObject,
    mut v_f_1556_: *mut LeanObject,
    mut v_it_1557_: *mut LeanObject,
    mut v_acc_1558_: *mut LeanObject,
    mut v_hP_1559_: *mut LeanObject,
    mut v_recur_1560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1562_: u8 = 0;
    v___x_1561_ = lean_unsigned_to_nat(0);
    v___x_1562_ = lean_nat_dec_eq(v_it_1557_, v___x_1561_);
    if v___x_1562_ == 0 {
        let mut v_str_1563_: *mut LeanObject = core::ptr::null_mut();
        let mut v_startInclusive_1564_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1565_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1566_: *mut LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1567_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1568_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1569_: u32 = 0;
        let mut v___x_1570_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1571_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1572_: *mut LeanObject = core::ptr::null_mut();
        v_str_1563_ = lean_ctor_get(v_s_1555_, 0);
        v_startInclusive_1564_ = lean_ctor_get(v_s_1555_, 1);
        v___x_1565_ = lean_unsigned_to_nat(1);
        v___x_1566_ = lean_nat_sub(v_it_1557_, v___x_1565_);
        v_prevPos_1567_ = l_String_Slice_posLE(v_s_1555_, v___x_1566_);
        v___x_1568_ = lean_nat_add(v_startInclusive_1564_, v_prevPos_1567_);
        v___x_1569_ = lean_string_utf8_get_fast(v_str_1563_, v___x_1568_);
        lean_dec(v___x_1568_);
        v___x_1570_ = lean_box_uint32(v___x_1569_);
        v___x_1571_ = lean_apply_2(v_f_1556_, v___x_1570_, v_acc_1558_);
        v___x_1572_ = lean_apply_4(
            v_recur_1560_,
            v_prevPos_1567_,
            v___x_1571_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1572_;
    } else {
        lean_dec(v_recur_1560_);
        lean_dec(v_f_1556_);
        return v_acc_1558_;
    }
}
pub unsafe fn l_String_Slice_foldr___redArg___lam__0___boxed(
    mut v_s_1573_: *mut LeanObject,
    mut v_f_1574_: *mut LeanObject,
    mut v_it_1575_: *mut LeanObject,
    mut v_acc_1576_: *mut LeanObject,
    mut v_hP_1577_: *mut LeanObject,
    mut v_recur_1578_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1579_: *mut LeanObject = core::ptr::null_mut();
    v_res_1579_ = l_String_Slice_foldr___redArg___lam__0(
        v_s_1573_,
        v_f_1574_,
        v_it_1575_,
        v_acc_1576_,
        v_hP_1577_,
        v_recur_1578_,
    );
    lean_dec(v_it_1575_);
    lean_dec_ref(v_s_1573_);
    return v_res_1579_;
}
pub unsafe fn l_String_Slice_foldr___redArg(
    mut v_f_1580_: *mut LeanObject,
    mut v_init_1581_: *mut LeanObject,
    mut v_s_1582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_1582_);
    v___f_1583_ = lean_alloc_closure(
        l_String_Slice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_1583_, 0, v_s_1582_);
    lean_closure_set(v___f_1583_, 1, v_f_1580_);
    v___x_1584_ = l_String_Slice_revPositions(v_s_1582_);
    lean_dec_ref(v_s_1582_);
    v___x_1585_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1583_, v___x_1584_, v_init_1581_, lean_box(0));
    return v___x_1585_;
}
pub unsafe fn l_String_Slice_foldr(
    mut v_00_u03b1_1586_: *mut LeanObject,
    mut v_f_1587_: *mut LeanObject,
    mut v_init_1588_: *mut LeanObject,
    mut v_s_1589_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: *mut LeanObject = core::ptr::null_mut();
    lean_inc_ref(v_s_1589_);
    v___f_1590_ = lean_alloc_closure(
        l_String_Slice_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        6,
        2,
    );
    lean_closure_set(v___f_1590_, 0, v_s_1589_);
    lean_closure_set(v___f_1590_, 1, v_f_1587_);
    v___x_1591_ = l_String_Slice_revPositions(v_s_1589_);
    lean_dec_ref(v_s_1589_);
    v___x_1592_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1590_, v___x_1591_, v_init_1588_, lean_box(0));
    return v___x_1592_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___redArg(
    mut v_x_1593_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1593_);
    return v_x_1593_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___redArg___boxed(
    mut v_x_1594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1595_: *mut LeanObject = core::ptr::null_mut();
    v_res_1595_ = l_String_Internal_ofToSliceWithProof___redArg(v_x_1594_);
    lean_dec(v_x_1594_);
    return v_res_1595_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof(
    mut v_s_1596_: *mut LeanObject,
    mut v_x_1597_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_1597_);
    return v_x_1597_;
}
pub unsafe fn l_String_Internal_ofToSliceWithProof___boxed(
    mut v_s_1598_: *mut LeanObject,
    mut v_x_1599_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1600_: *mut LeanObject = core::ptr::null_mut();
    v_res_1600_ = l_String_Internal_ofToSliceWithProof(v_s_1598_, v_x_1599_);
    lean_dec(v_x_1599_);
    lean_dec_ref(v_s_1598_);
    return v_res_1600_;
}
pub unsafe fn l_String_positionsFrom___redArg(mut v_p_1601_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_p_1601_);
    return v_p_1601_;
}
pub unsafe fn l_String_positionsFrom___redArg___boxed(
    mut v_p_1602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1603_: *mut LeanObject = core::ptr::null_mut();
    v_res_1603_ = l_String_positionsFrom___redArg(v_p_1602_);
    lean_dec(v_p_1602_);
    return v_res_1603_;
}
pub unsafe fn l_String_positionsFrom(
    mut v_s_1604_: *mut LeanObject,
    mut v_p_1605_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_1605_);
    return v_p_1605_;
}
pub unsafe fn l_String_positionsFrom___boxed(
    mut v_s_1606_: *mut LeanObject,
    mut v_p_1607_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1608_: *mut LeanObject = core::ptr::null_mut();
    v_res_1608_ = l_String_positionsFrom(v_s_1606_, v_p_1607_);
    lean_dec(v_p_1607_);
    lean_dec_ref(v_s_1606_);
    return v_res_1608_;
}
pub unsafe fn l_String_positions(mut v_s_1609_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1610_: *mut LeanObject = core::ptr::null_mut();
    v___x_1610_ = lean_unsigned_to_nat(0);
    return v___x_1610_;
}
pub unsafe fn l_String_positions___boxed(mut v_s_1611_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1612_: *mut LeanObject = core::ptr::null_mut();
    v_res_1612_ = l_String_positions(v_s_1611_);
    lean_dec_ref(v_s_1611_);
    return v_res_1612_;
}
pub unsafe fn l_String_chars(mut v_s_1613_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1614_: *mut LeanObject = core::ptr::null_mut();
    v___x_1614_ = lean_unsigned_to_nat(0);
    return v___x_1614_;
}
pub unsafe fn l_String_chars___boxed(mut v_s_1615_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1616_: *mut LeanObject = core::ptr::null_mut();
    v_res_1616_ = l_String_chars(v_s_1615_);
    lean_dec_ref(v_s_1615_);
    return v_res_1616_;
}
pub unsafe fn l_String_revPositionsFrom___redArg(
    mut v_p_1617_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_1617_);
    return v_p_1617_;
}
pub unsafe fn l_String_revPositionsFrom___redArg___boxed(
    mut v_p_1618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1619_: *mut LeanObject = core::ptr::null_mut();
    v_res_1619_ = l_String_revPositionsFrom___redArg(v_p_1618_);
    lean_dec(v_p_1618_);
    return v_res_1619_;
}
pub unsafe fn l_String_revPositionsFrom(
    mut v_s_1620_: *mut LeanObject,
    mut v_p_1621_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_p_1621_);
    return v_p_1621_;
}
pub unsafe fn l_String_revPositionsFrom___boxed(
    mut v_s_1622_: *mut LeanObject,
    mut v_p_1623_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1624_: *mut LeanObject = core::ptr::null_mut();
    v_res_1624_ = l_String_revPositionsFrom(v_s_1622_, v_p_1623_);
    lean_dec(v_p_1623_);
    lean_dec_ref(v_s_1622_);
    return v_res_1624_;
}
pub unsafe fn l_String_revPositions(mut v_s_1625_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1626_: *mut LeanObject = core::ptr::null_mut();
    v___x_1626_ = lean_string_utf8_byte_size(v_s_1625_);
    return v___x_1626_;
}
pub unsafe fn l_String_revPositions___boxed(mut v_s_1627_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_1628_: *mut LeanObject = core::ptr::null_mut();
    v_res_1628_ = l_String_revPositions(v_s_1627_);
    lean_dec_ref(v_s_1627_);
    return v_res_1628_;
}
pub unsafe fn l_String_revChars(mut v_s_1629_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1633_: *mut LeanObject = core::ptr::null_mut();
    v___x_1630_ = lean_unsigned_to_nat(0);
    v___x_1631_ = lean_string_utf8_byte_size(v_s_1629_);
    v___x_1632_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1632_, 0, v_s_1629_);
    lean_ctor_set(v___x_1632_, 1, v___x_1630_);
    lean_ctor_set(v___x_1632_, 2, v___x_1631_);
    v___x_1633_ = l_String_Slice_revPositions(v___x_1632_);
    lean_dec_ref_known(v___x_1632_, 3);
    return v___x_1633_;
}
pub unsafe fn l_String_byteIterator(mut v_s_1634_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1638_: *mut LeanObject = core::ptr::null_mut();
    v___x_1635_ = lean_unsigned_to_nat(0);
    v___x_1636_ = lean_string_utf8_byte_size(v_s_1634_);
    v___x_1637_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1637_, 0, v_s_1634_);
    lean_ctor_set(v___x_1637_, 1, v___x_1635_);
    lean_ctor_set(v___x_1637_, 2, v___x_1636_);
    v___x_1638_ = l_String_Slice_bytes(v___x_1637_);
    return v___x_1638_;
}
pub unsafe fn l_String_revBytes(mut v_s_1639_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_1640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut LeanObject = core::ptr::null_mut();
    v___x_1640_ = lean_unsigned_to_nat(0);
    v___x_1641_ = lean_string_utf8_byte_size(v_s_1639_);
    v___x_1642_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1642_, 0, v_s_1639_);
    lean_ctor_set(v___x_1642_, 1, v___x_1640_);
    lean_ctor_set(v___x_1642_, 2, v___x_1641_);
    v___x_1643_ = l_String_Slice_revBytes(v___x_1642_);
    return v___x_1643_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__2(
    mut v___x_1644_: *mut LeanObject,
    mut v_s_1645_: *mut LeanObject,
    mut v_toPure_1646_: *mut LeanObject,
    mut v_f_1647_: *mut LeanObject,
    mut v_toBind_1648_: *mut LeanObject,
    mut v___f_1649_: *mut LeanObject,
    mut v_it_1650_: *mut LeanObject,
    mut v_acc_1651_: *mut LeanObject,
    mut v_hP_1652_: *mut LeanObject,
    mut v_recur_1653_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1654_: u8 = 0;
    v___x_1654_ = lean_nat_dec_eq(v_it_1650_, v___x_1644_);
    if v___x_1654_ == 0 {
        let mut v___x_1655_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_1656_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1657_: u32 = 0;
        let mut v___x_1658_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1659_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1660_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1661_: *mut LeanObject = core::ptr::null_mut();
        v___x_1655_ = lean_string_utf8_next_fast(v_s_1645_, v_it_1650_);
        v___f_1656_ = lean_alloc_closure(
            l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__1
                as *mut core::ffi::c_void,
            4,
            3,
        );
        lean_closure_set(v___f_1656_, 0, v_toPure_1646_);
        lean_closure_set(v___f_1656_, 1, v_recur_1653_);
        lean_closure_set(v___f_1656_, 2, v___x_1655_);
        v___x_1657_ = lean_string_utf8_get_fast(v_s_1645_, v_it_1650_);
        v___x_1658_ = lean_box_uint32(v___x_1657_);
        v___x_1659_ = lean_apply_2(v_f_1647_, v___x_1658_, v_acc_1651_);
        lean_inc(v_toBind_1648_);
        v___x_1660_ = lean_apply_4(
            v_toBind_1648_,
            lean_box(0),
            lean_box(0),
            v___x_1659_,
            v___f_1649_,
        );
        v___x_1661_ = lean_apply_4(
            v_toBind_1648_,
            lean_box(0),
            lean_box(0),
            v___x_1660_,
            v___f_1656_,
        );
        return v___x_1661_;
    } else {
        let mut v___x_1662_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_recur_1653_);
        lean_dec(v___f_1649_);
        lean_dec(v_toBind_1648_);
        lean_dec(v_f_1647_);
        v___x_1662_ = lean_apply_2(v_toPure_1646_, lean_box(0), v_acc_1651_);
        return v___x_1662_;
    }
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__2___boxed(
    mut v___x_1663_: *mut LeanObject,
    mut v_s_1664_: *mut LeanObject,
    mut v_toPure_1665_: *mut LeanObject,
    mut v_f_1666_: *mut LeanObject,
    mut v_toBind_1667_: *mut LeanObject,
    mut v___f_1668_: *mut LeanObject,
    mut v_it_1669_: *mut LeanObject,
    mut v_acc_1670_: *mut LeanObject,
    mut v_hP_1671_: *mut LeanObject,
    mut v_recur_1672_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1673_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_1669_);
    lean_dec_ref(v_s_1664_);
    lean_dec(v___x_1663_);
    return v_res_1673_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg___lam__0(
    mut v_inst_1674_: *mut LeanObject,
    mut v_00_u03b2_1675_: *mut LeanObject,
    mut v_s_1676_: *mut LeanObject,
    mut v_b_1677_: *mut LeanObject,
    mut v_f_1678_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toApplicative_1679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toBind_1680_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toPure_1681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1686_: *mut LeanObject = core::ptr::null_mut();
    v_toApplicative_1679_ = lean_ctor_get(v_inst_1674_, 0);
    lean_inc_ref(v_toApplicative_1679_);
    v_toBind_1680_ = lean_ctor_get(v_inst_1674_, 1);
    lean_inc(v_toBind_1680_);
    lean_dec_ref(v_inst_1674_);
    v_toPure_1681_ = lean_ctor_get(v_toApplicative_1679_, 1);
    lean_inc_n(v_toPure_1681_, 2);
    lean_dec_ref(v_toApplicative_1679_);
    v___x_1682_ = lean_string_utf8_byte_size(v_s_1676_);
    v___x_1683_ = lean_unsigned_to_nat(0);
    v___f_1684_ = lean_alloc_closure(
        l_String_Slice_RevByteIterator_instForInCharOfMonad___redArg___lam__0
            as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1684_, 0, v_toPure_1681_);
    v___f_1685_ = lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__2___boxed as *mut core::ffi::c_void,
        10,
        6,
    );
    lean_closure_set(v___f_1685_, 0, v___x_1682_);
    lean_closure_set(v___f_1685_, 1, v_s_1676_);
    lean_closure_set(v___f_1685_, 2, v_toPure_1681_);
    lean_closure_set(v___f_1685_, 3, v_f_1678_);
    lean_closure_set(v___f_1685_, 4, v_toBind_1680_);
    lean_closure_set(v___f_1685_, 5, v___f_1684_);
    v___x_1686_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1685_, v___x_1683_, v_b_1677_, lean_box(0));
    return v___x_1686_;
}
pub unsafe fn l_String_instForInCharOfMonad___redArg(
    mut v_inst_1687_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1688_: *mut LeanObject = core::ptr::null_mut();
    v___f_1688_ = lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1688_, 0, v_inst_1687_);
    return v___f_1688_;
}
pub unsafe fn l_String_instForInCharOfMonad(
    mut v_m_1689_: *mut LeanObject,
    mut v_inst_1690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_1691_: *mut LeanObject = core::ptr::null_mut();
    v___f_1691_ = lean_alloc_closure(
        l_String_instForInCharOfMonad___redArg___lam__0 as *mut core::ffi::c_void,
        5,
        1,
    );
    lean_closure_set(v___f_1691_, 0, v_inst_1690_);
    return v___f_1691_;
}
pub unsafe fn l_String_foldl___redArg___lam__0(
    mut v___x_1692_: *mut LeanObject,
    mut v_s_1693_: *mut LeanObject,
    mut v_f_1694_: *mut LeanObject,
    mut v_it_1695_: *mut LeanObject,
    mut v_acc_1696_: *mut LeanObject,
    mut v_hP_1697_: *mut LeanObject,
    mut v_recur_1698_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1699_: u8 = 0;
    v___x_1699_ = lean_nat_dec_eq(v_it_1695_, v___x_1692_);
    if v___x_1699_ == 0 {
        let mut v___x_1700_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1701_: u32 = 0;
        let mut v___x_1702_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1703_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1704_: *mut LeanObject = core::ptr::null_mut();
        v___x_1700_ = lean_string_utf8_next_fast(v_s_1693_, v_it_1695_);
        v___x_1701_ = lean_string_utf8_get_fast(v_s_1693_, v_it_1695_);
        v___x_1702_ = lean_box_uint32(v___x_1701_);
        v___x_1703_ = lean_apply_2(v_f_1694_, v_acc_1696_, v___x_1702_);
        v___x_1704_ = lean_apply_4(
            v_recur_1698_,
            v___x_1700_,
            v___x_1703_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1704_;
    } else {
        lean_dec(v_recur_1698_);
        lean_dec(v_f_1694_);
        return v_acc_1696_;
    }
}
pub unsafe fn l_String_foldl___redArg___lam__0___boxed(
    mut v___x_1705_: *mut LeanObject,
    mut v_s_1706_: *mut LeanObject,
    mut v_f_1707_: *mut LeanObject,
    mut v_it_1708_: *mut LeanObject,
    mut v_acc_1709_: *mut LeanObject,
    mut v_hP_1710_: *mut LeanObject,
    mut v_recur_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1712_: *mut LeanObject = core::ptr::null_mut();
    v_res_1712_ = l_String_foldl___redArg___lam__0(
        v___x_1705_,
        v_s_1706_,
        v_f_1707_,
        v_it_1708_,
        v_acc_1709_,
        v_hP_1710_,
        v_recur_1711_,
    );
    lean_dec(v_it_1708_);
    lean_dec_ref(v_s_1706_);
    lean_dec(v___x_1705_);
    return v_res_1712_;
}
pub unsafe fn l_String_foldl___redArg(
    mut v_f_1713_: *mut LeanObject,
    mut v_init_1714_: *mut LeanObject,
    mut v_s_1715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1719_: *mut LeanObject = core::ptr::null_mut();
    v___x_1716_ = lean_string_utf8_byte_size(v_s_1715_);
    v___f_1717_ = lean_alloc_closure(
        l_String_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1717_, 0, v___x_1716_);
    lean_closure_set(v___f_1717_, 1, v_s_1715_);
    lean_closure_set(v___f_1717_, 2, v_f_1713_);
    v___x_1718_ = lean_unsigned_to_nat(0);
    v___x_1719_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1717_, v___x_1718_, v_init_1714_, lean_box(0));
    return v___x_1719_;
}
pub unsafe fn l_String_foldl(
    mut v_00_u03b1_1720_: *mut LeanObject,
    mut v_f_1721_: *mut LeanObject,
    mut v_init_1722_: *mut LeanObject,
    mut v_s_1723_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut LeanObject = core::ptr::null_mut();
    v___x_1724_ = lean_string_utf8_byte_size(v_s_1723_);
    v___f_1725_ = lean_alloc_closure(
        l_String_foldl___redArg___lam__0___boxed as *mut core::ffi::c_void,
        7,
        3,
    );
    lean_closure_set(v___f_1725_, 0, v___x_1724_);
    lean_closure_set(v___f_1725_, 1, v_s_1723_);
    lean_closure_set(v___f_1725_, 2, v_f_1721_);
    v___x_1726_ = lean_unsigned_to_nat(0);
    v___x_1727_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1725_, v___x_1726_, v_init_1722_, lean_box(0));
    return v___x_1727_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
    mut v_f_1728_: *mut LeanObject,
    mut v___x_1729_: *mut LeanObject,
    mut v_s_1730_: *mut LeanObject,
    mut v_a_1731_: *mut LeanObject,
    mut v_b_1732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_startInclusive_1733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_endExclusive_1734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: u8 = 0;
    let mut v___x_1737_: u32 = 0;
    let mut v___x_1738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1740_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_startInclusive_1733_ = lean_ctor_get(v___x_1729_, 1);
                v_endExclusive_1734_ = lean_ctor_get(v___x_1729_, 2);
                v___x_1735_ = lean_nat_sub(v_endExclusive_1734_, v_startInclusive_1733_);
                v___x_1736_ = lean_nat_dec_eq(v_a_1731_, v___x_1735_);
                lean_dec(v___x_1735_);
                if v___x_1736_ == 0 {
                    v___x_1737_ = lean_string_utf8_get_fast(v_s_1730_, v_a_1731_);
                    v___x_1738_ = lean_string_utf8_next_fast(v_s_1730_, v_a_1731_);
                    lean_dec(v_a_1731_);
                    v___x_1739_ = lean_box_uint32(v___x_1737_);
                    lean_inc_ref(v_f_1728_);
                    v___x_1740_ = lean_apply_2(v_f_1728_, v_b_1732_, v___x_1739_);
                    v_a_1731_ = v___x_1738_;
                    v_b_1732_ = v___x_1740_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_1731_);
                    lean_dec_ref(v_f_1728_);
                    return v_b_1732_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg___boxed(
    mut v_f_1742_: *mut LeanObject,
    mut v___x_1743_: *mut LeanObject,
    mut v_s_1744_: *mut LeanObject,
    mut v_a_1745_: *mut LeanObject,
    mut v_b_1746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1747_: *mut LeanObject = core::ptr::null_mut();
    v_res_1747_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
        v_f_1742_,
        v___x_1743_,
        v_s_1744_,
        v_a_1745_,
        v_b_1746_,
    );
    lean_dec_ref(v_s_1744_);
    lean_dec_ref(v___x_1743_);
    return v_res_1747_;
}
pub unsafe fn lean_string_foldl(
    mut v_f_1748_: *mut LeanObject,
    mut v_init_1749_: *mut LeanObject,
    mut v_s_1750_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1754_: *mut LeanObject = core::ptr::null_mut();
    v___x_1751_ = lean_unsigned_to_nat(0);
    v___x_1752_ = lean_string_utf8_byte_size(v_s_1750_);
    lean_inc_ref(v_s_1750_);
    v___x_1753_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1753_, 0, v_s_1750_);
    lean_ctor_set(v___x_1753_, 1, v___x_1751_);
    lean_ctor_set(v___x_1753_, 2, v___x_1752_);
    v___x_1754_ = l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0___redArg(
        v_f_1748_,
        v___x_1753_,
        v_s_1750_,
        v___x_1751_,
        v_init_1749_,
    );
    lean_dec_ref(v_s_1750_);
    lean_dec_ref_known(v___x_1753_, 3);
    return v___x_1754_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00String_Internal_foldlImpl_spec__0(
    mut v_f_1755_: *mut LeanObject,
    mut v___x_1756_: *mut LeanObject,
    mut v_s_1757_: *mut LeanObject,
    mut v_inst_1758_: *mut LeanObject,
    mut v_R_1759_: *mut LeanObject,
    mut v_a_1760_: *mut LeanObject,
    mut v_b_1761_: *mut LeanObject,
    mut v_c_1762_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1763_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_f_1764_: *mut LeanObject,
    mut v___x_1765_: *mut LeanObject,
    mut v_s_1766_: *mut LeanObject,
    mut v_inst_1767_: *mut LeanObject,
    mut v_R_1768_: *mut LeanObject,
    mut v_a_1769_: *mut LeanObject,
    mut v_b_1770_: *mut LeanObject,
    mut v_c_1771_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1772_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec_ref(v_s_1766_);
    lean_dec_ref(v___x_1765_);
    return v_res_1772_;
}
pub unsafe fn l_String_foldr___redArg___lam__0(
    mut v___x_1773_: *mut LeanObject,
    mut v___x_1774_: *mut LeanObject,
    mut v_s_1775_: *mut LeanObject,
    mut v_f_1776_: *mut LeanObject,
    mut v_it_1777_: *mut LeanObject,
    mut v_acc_1778_: *mut LeanObject,
    mut v_hP_1779_: *mut LeanObject,
    mut v_recur_1780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1781_: u8 = 0;
    v___x_1781_ = lean_nat_dec_eq(v_it_1777_, v___x_1773_);
    if v___x_1781_ == 0 {
        let mut v___x_1782_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1783_: *mut LeanObject = core::ptr::null_mut();
        let mut v_prevPos_1784_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1785_: u32 = 0;
        let mut v___x_1786_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1787_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_1788_: *mut LeanObject = core::ptr::null_mut();
        v___x_1782_ = lean_unsigned_to_nat(1);
        v___x_1783_ = lean_nat_sub(v_it_1777_, v___x_1782_);
        v_prevPos_1784_ = l_String_Slice_posLE(v___x_1774_, v___x_1783_);
        v___x_1785_ = lean_string_utf8_get_fast(v_s_1775_, v_prevPos_1784_);
        v___x_1786_ = lean_box_uint32(v___x_1785_);
        v___x_1787_ = lean_apply_2(v_f_1776_, v___x_1786_, v_acc_1778_);
        v___x_1788_ = lean_apply_4(
            v_recur_1780_,
            v_prevPos_1784_,
            v___x_1787_,
            lean_box(0),
            lean_box(0),
        );
        return v___x_1788_;
    } else {
        lean_dec(v_recur_1780_);
        lean_dec(v_f_1776_);
        return v_acc_1778_;
    }
}
pub unsafe fn l_String_foldr___redArg___lam__0___boxed(
    mut v___x_1789_: *mut LeanObject,
    mut v___x_1790_: *mut LeanObject,
    mut v_s_1791_: *mut LeanObject,
    mut v_f_1792_: *mut LeanObject,
    mut v_it_1793_: *mut LeanObject,
    mut v_acc_1794_: *mut LeanObject,
    mut v_hP_1795_: *mut LeanObject,
    mut v_recur_1796_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1797_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_it_1793_);
    lean_dec_ref(v_s_1791_);
    lean_dec_ref(v___x_1790_);
    lean_dec(v___x_1789_);
    return v_res_1797_;
}
pub unsafe fn l_String_foldr___redArg(
    mut v_f_1798_: *mut LeanObject,
    mut v_init_1799_: *mut LeanObject,
    mut v_s_1800_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1806_: *mut LeanObject = core::ptr::null_mut();
    v___x_1801_ = lean_unsigned_to_nat(0);
    v___x_1802_ = lean_string_utf8_byte_size(v_s_1800_);
    lean_inc_ref(v_s_1800_);
    v___x_1803_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1803_, 0, v_s_1800_);
    lean_ctor_set(v___x_1803_, 1, v___x_1801_);
    lean_ctor_set(v___x_1803_, 2, v___x_1802_);
    lean_inc_ref(v___x_1803_);
    v___f_1804_ = lean_alloc_closure(
        l_String_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_1804_, 0, v___x_1801_);
    lean_closure_set(v___f_1804_, 1, v___x_1803_);
    lean_closure_set(v___f_1804_, 2, v_s_1800_);
    lean_closure_set(v___f_1804_, 3, v_f_1798_);
    v___x_1805_ = l_String_Slice_revPositions(v___x_1803_);
    lean_dec_ref_known(v___x_1803_, 3);
    v___x_1806_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1804_, v___x_1805_, v_init_1799_, lean_box(0));
    return v___x_1806_;
}
pub unsafe fn l_String_foldr(
    mut v_00_u03b1_1807_: *mut LeanObject,
    mut v_f_1808_: *mut LeanObject,
    mut v_init_1809_: *mut LeanObject,
    mut v_s_1810_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    v___x_1811_ = lean_unsigned_to_nat(0);
    v___x_1812_ = lean_string_utf8_byte_size(v_s_1810_);
    lean_inc_ref(v_s_1810_);
    v___x_1813_ = lean_alloc_ctor(0, 3, (0) as u32);
    lean_ctor_set(v___x_1813_, 0, v_s_1810_);
    lean_ctor_set(v___x_1813_, 1, v___x_1811_);
    lean_ctor_set(v___x_1813_, 2, v___x_1812_);
    lean_inc_ref(v___x_1813_);
    v___f_1814_ = lean_alloc_closure(
        l_String_foldr___redArg___lam__0___boxed as *mut core::ffi::c_void,
        8,
        4,
    );
    lean_closure_set(v___f_1814_, 0, v___x_1811_);
    lean_closure_set(v___f_1814_, 1, v___x_1813_);
    lean_closure_set(v___f_1814_, 2, v_s_1810_);
    lean_closure_set(v___f_1814_, 3, v_f_1808_);
    v___x_1815_ = l_String_Slice_revPositions(v___x_1813_);
    lean_dec_ref_known(v___x_1813_, 3);
    v___x_1816_ =
        l_WellFounded_opaqueFix_u2083___redArg(v___f_1814_, v___x_1815_, v_init_1809_, lean_box(0));
    return v___x_1816_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_String_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_String_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_String_Iterate(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_String_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_String_Lemmas_FindPos(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_String_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_String_Iterate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_String_Iterate(builtin);
}

// Lean compiler output
// Module: Init.Data.Array.Find
// Imports: Init.Data.List.Nat.Sum Init.Data.Array.Basic Init.Data.Array.Attach Init.Data.Option.BasicAux Init.ByCases Init.Data.Array.Bootstrap Init.Data.Array.MapIdx Init.Data.Bool Init.Data.Fin.Lemmas Init.Data.List.Count Init.Data.List.Find Init.Data.List.Impl Init.Data.List.Nat.Find Init.Data.List.Nat.TakeDrop Init.Data.List.TakeDrop Init.Omega
use crate::r#gen::Init::ByCases::{initialize_Init_ByCases, runtime_initialize_Init_ByCases};
use crate::r#gen::Init::Data::Array::Attach::{
    initialize_Init_Data_Array_Attach, runtime_initialize_Init_Data_Array_Attach,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Bootstrap::{
    initialize_Init_Data_Array_Bootstrap, runtime_initialize_Init_Data_Array_Bootstrap,
};
use crate::r#gen::Init::Data::Array::MapIdx::{
    initialize_Init_Data_Array_MapIdx, runtime_initialize_Init_Data_Array_MapIdx,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Fin::Lemmas::{
    initialize_Init_Data_Fin_Lemmas, runtime_initialize_Init_Data_Fin_Lemmas,
};
use crate::r#gen::Init::Data::List::Count::{
    initialize_Init_Data_List_Count, runtime_initialize_Init_Data_List_Count,
};
use crate::r#gen::Init::Data::List::Find::{
    initialize_Init_Data_List_Find, runtime_initialize_Init_Data_List_Find,
};
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Data::List::Nat::Find::{
    initialize_Init_Data_List_Nat_Find, runtime_initialize_Init_Data_List_Nat_Find,
};
use crate::r#gen::Init::Data::List::Nat::Sum::{
    initialize_Init_Data_List_Nat_Sum, runtime_initialize_Init_Data_List_Nat_Sum,
};
use crate::r#gen::Init::Data::List::Nat::TakeDrop::{
    initialize_Init_Data_List_Nat_TakeDrop, runtime_initialize_Init_Data_List_Nat_TakeDrop,
};
use crate::r#gen::Init::Data::List::TakeDrop::{
    initialize_Init_Data_List_TakeDrop, runtime_initialize_Init_Data_List_TakeDrop,
};
use crate::r#gen::Init::Data::Option::BasicAux::{
    initialize_Init_Data_Option_BasicAux, runtime_initialize_Init_Data_Option_BasicAux,
};
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
pub unsafe fn l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter___redArg(
    mut v_x_59_: *mut crate::leanh::LeanObject,
    mut v_h__1_60_: *mut crate::leanh::LeanObject,
    mut v_h__2_61_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_59_) == 0 {
        let mut v___x_62_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_63_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_60_);
        v___x_62_ = crate::leanh::lean_box(0);
        v___x_63_ = crate::leanh::lean_apply_1(v_h__2_61_, v___x_62_);
        return v___x_63_;
    } else {
        let mut v_val_64_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_65_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_61_);
        v_val_64_ = crate::leanh::lean_ctor_get(v_x_59_, 0);
        crate::leanh::lean_inc(v_val_64_);
        crate::leanh::lean_dec_ref_known(v_x_59_, 1);
        v___x_65_ = crate::leanh::lean_apply_1(v_h__1_60_, v_val_64_);
        return v___x_65_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__Array_of__findIdx_x3f__eq__some_match__1_splitter(
    mut v_00_u03b1_66_: *mut crate::leanh::LeanObject,
    mut v_motive_67_: *mut crate::leanh::LeanObject,
    mut v_x_68_: *mut crate::leanh::LeanObject,
    mut v_h__1_69_: *mut crate::leanh::LeanObject,
    mut v_h__2_70_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_68_) == 0 {
        let mut v___x_71_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_72_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_69_);
        v___x_71_ = crate::leanh::lean_box(0);
        v___x_72_ = crate::leanh::lean_apply_1(v_h__2_70_, v___x_71_);
        return v___x_72_;
    } else {
        let mut v_val_73_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_74_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_70_);
        v_val_73_ = crate::leanh::lean_ctor_get(v_x_68_, 0);
        crate::leanh::lean_inc(v_val_73_);
        crate::leanh::lean_dec_ref_known(v_x_68_, 1);
        v___x_74_ = crate::leanh::lean_apply_1(v_h__1_69_, v_val_73_);
        return v___x_74_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter___redArg(
    mut v_x_75_: *mut crate::leanh::LeanObject,
    mut v_h__1_76_: *mut crate::leanh::LeanObject,
    mut v_h__2_77_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_75_) == 0 {
        let mut v___x_78_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_79_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_76_);
        v___x_78_ = crate::leanh::lean_box(0);
        v___x_79_ = crate::leanh::lean_apply_1(v_h__2_77_, v___x_78_);
        return v___x_79_;
    } else {
        let mut v_val_80_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_81_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_77_);
        v_val_80_ = crate::leanh::lean_ctor_get(v_x_75_, 0);
        crate::leanh::lean_inc(v_val_80_);
        crate::leanh::lean_dec_ref_known(v_x_75_, 1);
        v___x_81_ = crate::leanh::lean_apply_1(v_h__1_76_, v_val_80_);
        return v___x_81_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__List_of__findIdx_x3f__eq__some_match__1_splitter(
    mut v_00_u03b1_82_: *mut crate::leanh::LeanObject,
    mut v_motive_83_: *mut crate::leanh::LeanObject,
    mut v_x_84_: *mut crate::leanh::LeanObject,
    mut v_h__1_85_: *mut crate::leanh::LeanObject,
    mut v_h__2_86_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_84_) == 0 {
        let mut v___x_87_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_88_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_85_);
        v___x_87_ = crate::leanh::lean_box(0);
        v___x_88_ = crate::leanh::lean_apply_1(v_h__2_86_, v___x_87_);
        return v___x_88_;
    } else {
        let mut v_val_89_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_90_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_86_);
        v_val_89_ = crate::leanh::lean_ctor_get(v_x_84_, 0);
        crate::leanh::lean_inc(v_val_89_);
        crate::leanh::lean_dec_ref_known(v_x_84_, 1);
        v___x_90_ = crate::leanh::lean_apply_1(v_h__1_85_, v_val_89_);
        return v___x_90_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___redArg(
    mut v_o_91_: *mut crate::leanh::LeanObject,
    mut v_h__1_92_: *mut crate::leanh::LeanObject,
    mut v_h__2_93_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_91_) == 0 {
        let mut v___x_94_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_93_);
        v___x_94_ = crate::leanh::lean_apply_1(v_h__1_92_, crate::leanh::lean_box(0));
        return v___x_94_;
    } else {
        let mut v_val_95_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_92_);
        v_val_95_ = crate::leanh::lean_ctor_get(v_o_91_, 0);
        crate::leanh::lean_inc(v_val_95_);
        crate::leanh::lean_dec_ref_known(v_o_91_, 1);
        v___x_96_ = crate::leanh::lean_apply_2(v_h__2_93_, v_val_95_, crate::leanh::lean_box(0));
        return v___x_96_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter(
    mut v_00_u03b1_97_: *mut crate::leanh::LeanObject,
    mut v_p_98_: *mut crate::leanh::LeanObject,
    mut v_o_x27_99_: *mut crate::leanh::LeanObject,
    mut v_motive_100_: *mut crate::leanh::LeanObject,
    mut v_o_101_: *mut crate::leanh::LeanObject,
    mut v_h_102_: *mut crate::leanh::LeanObject,
    mut v_h__1_103_: *mut crate::leanh::LeanObject,
    mut v_h__2_104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_o_101_) == 0 {
        let mut v___x_105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_104_);
        v___x_105_ = crate::leanh::lean_apply_1(v_h__1_103_, crate::leanh::lean_box(0));
        return v___x_105_;
    } else {
        let mut v_val_106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_103_);
        v_val_106_ = crate::leanh::lean_ctor_get(v_o_101_, 0);
        crate::leanh::lean_inc(v_val_106_);
        crate::leanh::lean_dec_ref_known(v_o_101_, 1);
        v___x_107_ = crate::leanh::lean_apply_2(v_h__2_104_, v_val_106_, crate::leanh::lean_box(0));
        return v___x_107_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter___boxed(
    mut v_00_u03b1_108_: *mut crate::leanh::LeanObject,
    mut v_p_109_: *mut crate::leanh::LeanObject,
    mut v_o_x27_110_: *mut crate::leanh::LeanObject,
    mut v_motive_111_: *mut crate::leanh::LeanObject,
    mut v_o_112_: *mut crate::leanh::LeanObject,
    mut v_h_113_: *mut crate::leanh::LeanObject,
    mut v_h__1_114_: *mut crate::leanh::LeanObject,
    mut v_h__2_115_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_116_ = l___private_Init_Data_Array_Find_0__Option_pmap__or_match__1_splitter(
        v_00_u03b1_108_,
        v_p_109_,
        v_o_x27_110_,
        v_motive_111_,
        v_o_112_,
        v_h_113_,
        v_h__1_114_,
        v_h__2_115_,
    );
    crate::leanh::lean_dec(v_o_x27_110_);
    return v_res_116_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_Find(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Nat_Sum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_TakeDrop(builtin);
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
pub unsafe fn meta_initialize_Init_Data_Array_Find(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_Find(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Nat_Sum(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_ByCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Bootstrap(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_MapIdx(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Fin_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Count(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_Nat_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_List_TakeDrop(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_Find(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_Find(builtin);
}

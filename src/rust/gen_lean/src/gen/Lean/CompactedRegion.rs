// Lean compiler output
// Module: Lean.CompactedRegion
// Imports: Init.System.IO Lean.Data.Name
use crate::ffi::{
    lean_compacted_region_free, lean_compacted_region_is_memory_mapped, lean_compacted_region_read,
    lean_compacted_region_save, lean_compacted_region_size,
};
use crate::r#gen::Init::System::IO::{
    initialize_Init_System_IO, runtime_initialize_Init_System_IO,
};
use crate::r#gen::Lean::Data::Name::{
    initialize_Lean_Data_Name, runtime_initialize_Lean_Data_Name,
};
pub static mut l___private_Lean_CompactedRegion_0__Lean_CompactorSpec:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_CompactedRegion_isMemoryMapped___boxed(
    mut v_a_00___x40___internal___hyg_46_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_47_: usize = 0;
    let mut v_res_48_: u8 = 0;
    let mut v_r_49_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_47_ =
        leanh::lean_unbox_usize(v_a_00___x40___internal___hyg_46_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_46_);
    v_res_48_ = lean_compacted_region_is_memory_mapped(v_a_00___x40___internal___hyg_1__boxed_47_);
    v_r_49_ = leanh::lean_box((v_res_48_) as usize);
    return v_r_49_;
}
pub unsafe fn l_Lean_CompactedRegion_size___boxed(
    mut v_a_00___x40___internal___hyg_51_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_52_: usize = 0;
    let mut v_res_53_: usize = 0;
    let mut v_r_54_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_52_ =
        leanh::lean_unbox_usize(v_a_00___x40___internal___hyg_51_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_51_);
    v_res_53_ = lean_compacted_region_size(v_a_00___x40___internal___hyg_1__boxed_52_);
    v_r_54_ = leanh::lean_box_usize(v_res_53_);
    return v_r_54_;
}
pub unsafe fn l_Lean_CompactedRegion_free___boxed(
    mut v_a_00___x40___internal___hyg_57_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_58_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_00___x40___internal___hyg_1__boxed_59_: usize = 0;
    let mut v_res_60_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_00___x40___internal___hyg_1__boxed_59_ =
        leanh::lean_unbox_usize(v_a_00___x40___internal___hyg_57_);
    leanh::lean_dec(v_a_00___x40___internal___hyg_57_);
    v_res_60_ = lean_compacted_region_free(v_a_00___x40___internal___hyg_1__boxed_59_);
    return v_res_60_;
}
pub unsafe fn _init_l___private_Lean_CompactedRegion_0__Lean_CompactorSpec()
-> *mut leanh::LeanObject {
    let mut v___x_61_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_61_ = leanh::lean_box(0);
    return v___x_61_;
}
pub unsafe fn l_Lean_CompactedRegion_save___boxed(
    mut v_00_u03b1_70_: *mut leanh::LeanObject,
    mut v_fname_71_: *mut leanh::LeanObject,
    mut v_key_72_: *mut leanh::LeanObject,
    mut v_data_73_: *mut leanh::LeanObject,
    mut v_depRegions_74_: *mut leanh::LeanObject,
    mut v_prev_75_: *mut leanh::LeanObject,
    mut v_allowClosures_76_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_77_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_allowClosures_boxed_78_: u8 = 0;
    let mut v_res_79_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_allowClosures_boxed_78_ = (leanh::lean_unbox(v_allowClosures_76_) as u8);
    v_res_79_ = lean_compacted_region_save(
        v_fname_71_,
        v_key_72_,
        v_data_73_,
        v_depRegions_74_,
        v_prev_75_,
        v_allowClosures_boxed_78_,
    );
    leanh::lean_dec_ref(v_depRegions_74_);
    leanh::lean_dec(v_data_73_);
    leanh::lean_dec(v_key_72_);
    leanh::lean_dec_ref(v_fname_71_);
    return v_res_79_;
}
pub unsafe fn l_Lean_CompactedRegion_read___boxed(
    mut v_00_u03b1_84_: *mut leanh::LeanObject,
    mut v_fname_85_: *mut leanh::LeanObject,
    mut v_depRegions_86_: *mut leanh::LeanObject,
    mut v_a_00___x40___internal___hyg_87_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_88_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_88_ = lean_compacted_region_read(v_fname_85_, v_depRegions_86_);
    leanh::lean_dec_ref(v_depRegions_86_);
    leanh::lean_dec_ref(v_fname_85_);
    return v_res_88_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_CompactedRegion(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l___private_Lean_CompactedRegion_0__Lean_CompactorSpec =
        _init_l___private_Lean_CompactedRegion_0__Lean_CompactorSpec();
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_CompactedRegion(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_CompactedRegion(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_System_IO(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_Name(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_CompactedRegion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_CompactedRegion(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_CompactedRegion(builtin);
}
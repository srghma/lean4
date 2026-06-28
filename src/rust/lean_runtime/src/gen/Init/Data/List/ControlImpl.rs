// Lean compiler output
// Module: Init.Data.List.ControlImpl
// Imports: Init.Data.List.Control Init.Data.List.Impl
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::List::Control::{
    initialize_Init_Data_List_Control, runtime_initialize_Init_Data_List_Control,
};
use crate::r#gen::Init::Data::List::Impl::{
    initialize_Init_Data_List_Impl, l___private_Init_Data_List_Impl_0__List_flatMapTR_go,
    runtime_initialize_Init_Data_List_Impl,
};
use crate::r#gen::Init::Prelude::l_id___boxed;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_2, lean_apply_3, lean_apply_4, lean_box, lean_closure_set, lean_ctor_get,
    lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc, lean_inc_ref,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_obj_tag,
};
pub static l_List_flatMapMTR_loop___redArg___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_id___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_List_flatMapMTR_loop___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_List_flatMapMTR_loop___redArg___closed__0_value) as *mut LeanObject;
pub static l_List_flatMapMTR_loop___redArg___closed__1_value: LeanArrayObject<0> =
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
static mut l_List_flatMapMTR_loop___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_List_flatMapMTR_loop___redArg___closed__1_value) as *mut LeanObject;
pub unsafe fn l_List_flatMapMTR_loop___redArg(
    mut v_inst_90_: *mut LeanObject,
    mut v_f_91_: *mut LeanObject,
    mut v_x_92_: *mut LeanObject,
    mut v_x_93_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_92_) == 0 {
        let mut v_toApplicative_94_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_95_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_96_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_97_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_98_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_99_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_100_: *mut LeanObject = core::ptr::null_mut();
        v_toApplicative_94_ = lean_ctor_get(v_inst_90_, 0);
        lean_inc_ref(v_toApplicative_94_);
        lean_dec(v_f_91_);
        lean_dec_ref(v_inst_90_);
        v_toPure_95_ = lean_ctor_get(v_toApplicative_94_, 1);
        lean_inc(v_toPure_95_);
        lean_dec_ref(v_toApplicative_94_);
        v___x_96_ = l_List_reverse___redArg(v_x_93_);
        v___x_97_ = l_List_flatMapMTR_loop___redArg___closed__0;
        v___x_98_ = l_List_flatMapMTR_loop___redArg___closed__1;
        v___x_99_ = l___private_Init_Data_List_Impl_0__List_flatMapTR_go(
            lean_box(0),
            lean_box(0),
            v___x_97_,
            v___x_96_,
            v___x_98_,
        );
        v___x_100_ = lean_apply_2(v_toPure_95_, lean_box(0), v___x_99_);
        return v___x_100_;
    } else {
        let mut v_toBind_101_: *mut LeanObject = core::ptr::null_mut();
        let mut v_head_102_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_103_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_104_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_105_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_106_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_101_ = lean_ctor_get(v_inst_90_, 1);
        lean_inc(v_toBind_101_);
        v_head_102_ = lean_ctor_get(v_x_92_, 0);
        lean_inc(v_head_102_);
        v_tail_103_ = lean_ctor_get(v_x_92_, 1);
        lean_inc(v_tail_103_);
        lean_dec_ref_known(v_x_92_, 2);
        lean_inc(v_f_91_);
        v___f_104_ = lean_alloc_closure(
            l_List_flatMapMTR_loop___redArg___lam__0 as *mut core::ffi::c_void,
            5,
            4,
        );
        lean_closure_set(v___f_104_, 0, v_x_93_);
        lean_closure_set(v___f_104_, 1, v_inst_90_);
        lean_closure_set(v___f_104_, 2, v_f_91_);
        lean_closure_set(v___f_104_, 3, v_tail_103_);
        v___x_105_ = lean_apply_1(v_f_91_, v_head_102_);
        v___x_106_ = lean_apply_4(
            v_toBind_101_,
            lean_box(0),
            lean_box(0),
            v___x_105_,
            v___f_104_,
        );
        return v___x_106_;
    }
}
pub unsafe fn l_List_flatMapMTR_loop___redArg___lam__0(
    mut v_x_107_: *mut LeanObject,
    mut v_inst_108_: *mut LeanObject,
    mut v_f_109_: *mut LeanObject,
    mut v_tail_110_: *mut LeanObject,
    mut v_bs_x27_111_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_113_: *mut LeanObject = core::ptr::null_mut();
    v___x_112_ = lean_alloc_ctor(1, 2, (0) as u32);
    lean_ctor_set(v___x_112_, 0, v_bs_x27_111_);
    lean_ctor_set(v___x_112_, 1, v_x_107_);
    v___x_113_ = l_List_flatMapMTR_loop___redArg(v_inst_108_, v_f_109_, v_tail_110_, v___x_112_);
    return v___x_113_;
}
pub unsafe fn l_List_flatMapMTR_loop(
    mut v_m_114_: *mut LeanObject,
    mut v_inst_115_: *mut LeanObject,
    mut v_00_u03b1_116_: *mut LeanObject,
    mut v_00_u03b2_117_: *mut LeanObject,
    mut v_f_118_: *mut LeanObject,
    mut v_x_119_: *mut LeanObject,
    mut v_x_120_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_121_: *mut LeanObject = core::ptr::null_mut();
    v___x_121_ = l_List_flatMapMTR_loop___redArg(v_inst_115_, v_f_118_, v_x_119_, v_x_120_);
    return v___x_121_;
}
pub unsafe fn l_List_flatMapMTR___redArg(
    mut v_inst_122_: *mut LeanObject,
    mut v_f_123_: *mut LeanObject,
    mut v_as_124_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
    v___x_125_ = lean_box(0);
    v___x_126_ = l_List_flatMapMTR_loop___redArg(v_inst_122_, v_f_123_, v_as_124_, v___x_125_);
    return v___x_126_;
}
pub unsafe fn l_List_flatMapMTR(
    mut v_m_127_: *mut LeanObject,
    mut v_inst_128_: *mut LeanObject,
    mut v_00_u03b1_129_: *mut LeanObject,
    mut v_00_u03b2_130_: *mut LeanObject,
    mut v_f_131_: *mut LeanObject,
    mut v_as_132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_134_: *mut LeanObject = core::ptr::null_mut();
    v___x_133_ = lean_box(0);
    v___x_134_ = l_List_flatMapMTR_loop___redArg(v_inst_128_, v_f_131_, v_as_132_, v___x_133_);
    return v___x_134_;
}
pub unsafe fn l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter___redArg(
    mut v_x_135_: *mut LeanObject,
    mut v_x_136_: *mut LeanObject,
    mut v_h__1_137_: *mut LeanObject,
    mut v_h__2_138_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_135_) == 0 {
        let mut v___x_139_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_138_);
        v___x_139_ = lean_apply_1(v_h__1_137_, v_x_136_);
        return v___x_139_;
    } else {
        let mut v_head_140_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_141_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_142_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_137_);
        v_head_140_ = lean_ctor_get(v_x_135_, 0);
        lean_inc(v_head_140_);
        v_tail_141_ = lean_ctor_get(v_x_135_, 1);
        lean_inc(v_tail_141_);
        lean_dec_ref_known(v_x_135_, 2);
        v___x_142_ = lean_apply_3(v_h__2_138_, v_head_140_, v_tail_141_, v_x_136_);
        return v___x_142_;
    }
}
pub unsafe fn l___private_Init_Data_List_ControlImpl_0__List_flatMapM_match__1_splitter(
    mut v_00_u03b1_143_: *mut LeanObject,
    mut v_00_u03b2_144_: *mut LeanObject,
    mut v_motive_145_: *mut LeanObject,
    mut v_x_146_: *mut LeanObject,
    mut v_x_147_: *mut LeanObject,
    mut v_h__1_148_: *mut LeanObject,
    mut v_h__2_149_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_146_) == 0 {
        let mut v___x_150_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_149_);
        v___x_150_ = lean_apply_1(v_h__1_148_, v_x_147_);
        return v___x_150_;
    } else {
        let mut v_head_151_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_152_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_153_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_148_);
        v_head_151_ = lean_ctor_get(v_x_146_, 0);
        lean_inc(v_head_151_);
        v_tail_152_ = lean_ctor_get(v_x_146_, 1);
        lean_inc(v_tail_152_);
        lean_dec_ref_known(v_x_146_, 2);
        v___x_153_ = lean_apply_3(v_h__2_149_, v_head_151_, v_tail_152_, v_x_147_);
        return v___x_153_;
    }
}
pub unsafe fn l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter___redArg(
    mut v_x_154_: *mut LeanObject,
    mut v_x_155_: *mut LeanObject,
    mut v_h__1_156_: *mut LeanObject,
    mut v_h__2_157_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_154_) == 0 {
        let mut v___x_158_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_157_);
        v___x_158_ = lean_apply_1(v_h__1_156_, v_x_155_);
        return v___x_158_;
    } else {
        let mut v_head_159_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_160_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_161_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_156_);
        v_head_159_ = lean_ctor_get(v_x_154_, 0);
        lean_inc(v_head_159_);
        v_tail_160_ = lean_ctor_get(v_x_154_, 1);
        lean_inc(v_tail_160_);
        lean_dec_ref_known(v_x_154_, 2);
        v___x_161_ = lean_apply_3(v_h__2_157_, v_head_159_, v_tail_160_, v_x_155_);
        return v___x_161_;
    }
}
pub unsafe fn l___private_Init_Data_List_ControlImpl_0__List_flatMapMTR_match__1_splitter(
    mut v_00_u03b1_162_: *mut LeanObject,
    mut v_00_u03b2_163_: *mut LeanObject,
    mut v_motive_164_: *mut LeanObject,
    mut v_x_165_: *mut LeanObject,
    mut v_x_166_: *mut LeanObject,
    mut v_h__1_167_: *mut LeanObject,
    mut v_h__2_168_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_165_) == 0 {
        let mut v___x_169_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_168_);
        v___x_169_ = lean_apply_1(v_h__1_167_, v_x_166_);
        return v___x_169_;
    } else {
        let mut v_head_170_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_172_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_167_);
        v_head_170_ = lean_ctor_get(v_x_165_, 0);
        lean_inc(v_head_170_);
        v_tail_171_ = lean_ctor_get(v_x_165_, 1);
        lean_inc(v_tail_171_);
        lean_dec_ref_known(v_x_165_, 2);
        v___x_172_ = lean_apply_3(v_h__2_168_, v_head_170_, v_tail_171_, v_x_166_);
        return v___x_172_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_List_ControlImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_List_ControlImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_List_ControlImpl(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_List_Control(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_List_Impl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_List_ControlImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_List_ControlImpl(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_List_ControlImpl(builtin);
}

// Lean compiler output
// Module: Init.Data.Option.Attach
// Imports: Init.Data.Array.Attach Init.Data.Option.Lemmas Init.Data.Bool Init.Data.Option.Array Init.Data.Option.List Init.Data.Subtype.Basic
use crate::r#gen::Init::Data::Array::Attach::{
    initialize_Init_Data_Array_Attach, runtime_initialize_Init_Data_Array_Attach,
};
use crate::r#gen::Init::Data::Bool::{
    initialize_Init_Data_Bool, runtime_initialize_Init_Data_Bool,
};
use crate::r#gen::Init::Data::Option::Array::{
    initialize_Init_Data_Option_Array, runtime_initialize_Init_Data_Option_Array,
};
use crate::r#gen::Init::Data::Option::Lemmas::{
    initialize_Init_Data_Option_Lemmas, runtime_initialize_Init_Data_Option_Lemmas,
};
use crate::r#gen::Init::Data::Option::List::{
    initialize_Init_Data_Option_List, runtime_initialize_Init_Data_Option_List,
};
use crate::r#gen::Init::Data::Subtype::Basic::{
    initialize_Init_Data_Subtype_Basic, runtime_initialize_Init_Data_Subtype_Basic,
};
pub static l_Option_instMonadAttach___closed__0_value: crate::leanh::LeanClosureObject<0> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Option_instMonadAttach___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Option_instMonadAttach___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_instMonadAttach___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Option_instMonadAttach: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Option_instMonadAttach___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(
    mut v_o_100_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_o_100_);
    return v_o_100_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(
    mut v_o_101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_102_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(v_o_101_);
    crate::leanh::lean_dec(v_o_101_);
    return v_res_102_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(
    mut v_00_u03b1_103_: *mut crate::leanh::LeanObject,
    mut v_o_104_: *mut crate::leanh::LeanObject,
    mut v_P_105_: *mut crate::leanh::LeanObject,
    mut v_x_106_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_o_104_);
    return v_o_104_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(
    mut v_00_u03b1_107_: *mut crate::leanh::LeanObject,
    mut v_o_108_: *mut crate::leanh::LeanObject,
    mut v_P_109_: *mut crate::leanh::LeanObject,
    mut v_x_110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_111_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(
        v_00_u03b1_107_,
        v_o_108_,
        v_P_109_,
        v_x_110_,
    );
    crate::leanh::lean_dec(v_o_108_);
    return v_res_111_;
}
pub unsafe fn l_Option_attach___redArg(
    mut v_xs_112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_xs_112_);
    return v_xs_112_;
}
pub unsafe fn l_Option_attach___redArg___boxed(
    mut v_xs_113_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_114_ = l_Option_attach___redArg(v_xs_113_);
    crate::leanh::lean_dec(v_xs_113_);
    return v_res_114_;
}
pub unsafe fn l_Option_attach(
    mut v_00_u03b1_115_: *mut crate::leanh::LeanObject,
    mut v_xs_116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_xs_116_);
    return v_xs_116_;
}
pub unsafe fn l_Option_attach___boxed(
    mut v_00_u03b1_117_: *mut crate::leanh::LeanObject,
    mut v_xs_118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_119_ = l_Option_attach(v_00_u03b1_117_, v_xs_118_);
    crate::leanh::lean_dec(v_xs_118_);
    return v_res_119_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_120_: *mut crate::leanh::LeanObject,
    mut v_h__1_121_: *mut crate::leanh::LeanObject,
    mut v_h__2_122_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_120_) == 0 {
        let mut v___x_123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_122_);
        v___x_123_ = crate::leanh::lean_box(0);
        v___x_124_ = crate::leanh::lean_apply_1(v_h__1_121_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_val_125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_121_);
        v_val_125_ = crate::leanh::lean_ctor_get(v_b_120_, 0);
        crate::leanh::lean_inc(v_val_125_);
        crate::leanh::lean_dec_ref_known(v_b_120_, 1);
        v___x_126_ = crate::leanh::lean_apply_1(v_h__2_122_, v_val_125_);
        return v___x_126_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_127_: *mut crate::leanh::LeanObject,
    mut v_motive_128_: *mut crate::leanh::LeanObject,
    mut v_b_129_: *mut crate::leanh::LeanObject,
    mut v_h__1_130_: *mut crate::leanh::LeanObject,
    mut v_h__2_131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_b_129_) == 0 {
        let mut v___x_132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_131_);
        v___x_132_ = crate::leanh::lean_box(0);
        v___x_133_ = crate::leanh::lean_apply_1(v_h__1_130_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_val_134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_130_);
        v_val_134_ = crate::leanh::lean_ctor_get(v_b_129_, 0);
        crate::leanh::lean_inc(v_val_134_);
        crate::leanh::lean_dec_ref_known(v_b_129_, 1);
        v___x_135_ = crate::leanh::lean_apply_1(v_h__2_131_, v_val_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Option_unattach___redArg(
    mut v_o_136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_141_: u8 = 0;
    let mut v___x_143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_o_136_) == 0 {
                    v___x_137_ = crate::leanh::lean_box(0);
                    return v___x_137_;
                } else {
                    v_val_138_ = crate::leanh::lean_ctor_get(v_o_136_, 0);
                    v_isSharedCheck_145_ = (!crate::leanh::lean_is_exclusive(v_o_136_)) as u8;
                    if v_isSharedCheck_145_ == 0 {
                        v___x_140_ = v_o_136_;
                        v_isShared_141_ = v_isSharedCheck_145_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_138_);
                        crate::leanh::lean_dec(v_o_136_);
                        v___x_140_ = crate::leanh::lean_box(0);
                        v_isShared_141_ = v_isSharedCheck_145_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_141_ == 0 {
                    v___x_143_ = v___x_140_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_144_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_144_, 0, v_val_138_);
                    v___x_143_ = v_reuseFailAlloc_144_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_143_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Option_unattach(
    mut v_00_u03b1_146_: *mut crate::leanh::LeanObject,
    mut v_p_147_: *mut crate::leanh::LeanObject,
    mut v_o_148_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Option_unattach___redArg(v_o_148_);
    return v___x_149_;
}
pub unsafe fn l_Option_instMonadAttach___lam__0(
    mut v_00_u03b1_150_: *mut crate::leanh::LeanObject,
    mut v_x_151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc(v_x_151_);
    return v_x_151_;
}
pub unsafe fn l_Option_instMonadAttach___lam__0___boxed(
    mut v_00_u03b1_152_: *mut crate::leanh::LeanObject,
    mut v_x_153_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_154_ = l_Option_instMonadAttach___lam__0(v_00_u03b1_152_, v_x_153_);
    crate::leanh::lean_dec(v_x_153_);
    return v_res_154_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(
    mut v_x_157_: *mut crate::leanh::LeanObject,
    mut v_h__1_158_: *mut crate::leanh::LeanObject,
    mut v_h__2_159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_157_) == 0 {
        let mut v___x_160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_158_);
        v___x_160_ = crate::leanh::lean_apply_1(v_h__2_159_, crate::leanh::lean_box(0));
        return v___x_160_;
    } else {
        let mut v_val_161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_159_);
        v_val_161_ = crate::leanh::lean_ctor_get(v_x_157_, 0);
        crate::leanh::lean_inc(v_val_161_);
        crate::leanh::lean_dec_ref_known(v_x_157_, 1);
        v___x_162_ = crate::leanh::lean_apply_2(v_h__1_158_, v_val_161_, crate::leanh::lean_box(0));
        return v___x_162_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(
    mut v_m_163_: *mut crate::leanh::LeanObject,
    mut v_inst_164_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_165_: *mut crate::leanh::LeanObject,
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_motive_167_: *mut crate::leanh::LeanObject,
    mut v_x_168_: *mut crate::leanh::LeanObject,
    mut v_h__1_169_: *mut crate::leanh::LeanObject,
    mut v_h__2_170_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_168_) == 0 {
        let mut v___x_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_169_);
        v___x_171_ = crate::leanh::lean_apply_1(v_h__2_170_, crate::leanh::lean_box(0));
        return v___x_171_;
    } else {
        let mut v_val_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_170_);
        v_val_172_ = crate::leanh::lean_ctor_get(v_x_168_, 0);
        crate::leanh::lean_inc(v_val_172_);
        crate::leanh::lean_dec_ref_known(v_x_168_, 1);
        v___x_173_ = crate::leanh::lean_apply_2(v_h__1_169_, v_val_172_, crate::leanh::lean_box(0));
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(
    mut v_m_174_: *mut crate::leanh::LeanObject,
    mut v_inst_175_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_176_: *mut crate::leanh::LeanObject,
    mut v_x_177_: *mut crate::leanh::LeanObject,
    mut v_motive_178_: *mut crate::leanh::LeanObject,
    mut v_x_179_: *mut crate::leanh::LeanObject,
    mut v_h__1_180_: *mut crate::leanh::LeanObject,
    mut v_h__2_181_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_182_ = l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(
        v_m_174_,
        v_inst_175_,
        v_00_u03b1_176_,
        v_x_177_,
        v_motive_178_,
        v_x_179_,
        v_h__1_180_,
        v_h__2_181_,
    );
    crate::leanh::lean_dec(v_x_177_);
    crate::leanh::lean_dec(v_inst_175_);
    return v_res_182_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_183_: *mut crate::leanh::LeanObject,
    mut v_h__1_184_: *mut crate::leanh::LeanObject,
    mut v_h__2_185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_183_) == 0 {
        let mut v___x_186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_184_);
        v___x_186_ = crate::leanh::lean_box(0);
        v___x_187_ = crate::leanh::lean_apply_1(v_h__2_185_, v___x_186_);
        return v___x_187_;
    } else {
        let mut v_val_188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_185_);
        v_val_188_ = crate::leanh::lean_ctor_get(v_____do__lift_183_, 0);
        crate::leanh::lean_inc(v_val_188_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_183_, 1);
        v___x_189_ = crate::leanh::lean_apply_1(v_h__1_184_, v_val_188_);
        return v___x_189_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_190_: *mut crate::leanh::LeanObject,
    mut v_motive_191_: *mut crate::leanh::LeanObject,
    mut v_____do__lift_192_: *mut crate::leanh::LeanObject,
    mut v_h__1_193_: *mut crate::leanh::LeanObject,
    mut v_h__2_194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_____do__lift_192_) == 0 {
        let mut v___x_195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_193_);
        v___x_195_ = crate::leanh::lean_box(0);
        v___x_196_ = crate::leanh::lean_apply_1(v_h__2_194_, v___x_195_);
        return v___x_196_;
    } else {
        let mut v_val_197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_194_);
        v_val_197_ = crate::leanh::lean_ctor_get(v_____do__lift_192_, 0);
        crate::leanh::lean_inc(v_val_197_);
        crate::leanh::lean_dec_ref_known(v_____do__lift_192_, 1);
        v___x_198_ = crate::leanh::lean_apply_1(v_h__1_193_, v_val_197_);
        return v___x_198_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Attach(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Attach(
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
pub unsafe fn initialize_Init_Data_Option_Attach(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_Array(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Attach(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Option_Attach(builtin);
}

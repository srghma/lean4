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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_1, lean_apply_2, lean_box,
    lean_ctor_get, lean_ctor_set, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_inc,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_tag,
};
pub static l_Option_instMonadAttach___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Option_instMonadAttach___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Option_instMonadAttach___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Option_instMonadAttach___closed__0_value) as *mut LeanObject;
pub static mut l_Option_instMonadAttach: *mut LeanObject =
    core::ptr::addr_of!(l_Option_instMonadAttach___closed__0_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(
    mut v_o_100_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_o_100_);
    return v_o_100_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg___boxed(
    mut v_o_101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_102_: *mut LeanObject = core::ptr::null_mut();
    v_res_102_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___redArg(v_o_101_);
    lean_dec(v_o_101_);
    return v_res_102_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(
    mut v_00_u03b1_103_: *mut LeanObject,
    mut v_o_104_: *mut LeanObject,
    mut v_P_105_: *mut LeanObject,
    mut v_x_106_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_o_104_);
    return v_o_104_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_attachWithImpl___boxed(
    mut v_00_u03b1_107_: *mut LeanObject,
    mut v_o_108_: *mut LeanObject,
    mut v_P_109_: *mut LeanObject,
    mut v_x_110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_111_: *mut LeanObject = core::ptr::null_mut();
    v_res_111_ = l___private_Init_Data_Option_Attach_0__Option_attachWithImpl(
        v_00_u03b1_107_,
        v_o_108_,
        v_P_109_,
        v_x_110_,
    );
    lean_dec(v_o_108_);
    return v_res_111_;
}
pub unsafe fn l_Option_attach___redArg(mut v_xs_112_: *mut LeanObject) -> *mut LeanObject {
    lean_inc(v_xs_112_);
    return v_xs_112_;
}
pub unsafe fn l_Option_attach___redArg___boxed(mut v_xs_113_: *mut LeanObject) -> *mut LeanObject {
    let mut v_res_114_: *mut LeanObject = core::ptr::null_mut();
    v_res_114_ = l_Option_attach___redArg(v_xs_113_);
    lean_dec(v_xs_113_);
    return v_res_114_;
}
pub unsafe fn l_Option_attach(
    mut v_00_u03b1_115_: *mut LeanObject,
    mut v_xs_116_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_xs_116_);
    return v_xs_116_;
}
pub unsafe fn l_Option_attach___boxed(
    mut v_00_u03b1_117_: *mut LeanObject,
    mut v_xs_118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_119_: *mut LeanObject = core::ptr::null_mut();
    v_res_119_ = l_Option_attach(v_00_u03b1_117_, v_xs_118_);
    lean_dec(v_xs_118_);
    return v_res_119_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter___redArg(
    mut v_b_120_: *mut LeanObject,
    mut v_h__1_121_: *mut LeanObject,
    mut v_h__2_122_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_120_) == 0 {
        let mut v___x_123_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_124_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_122_);
        v___x_123_ = lean_box(0);
        v___x_124_ = lean_apply_1(v_h__1_121_, v___x_123_);
        return v___x_124_;
    } else {
        let mut v_val_125_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_126_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_121_);
        v_val_125_ = lean_ctor_get(v_b_120_, 0);
        lean_inc(v_val_125_);
        lean_dec_ref_known(v_b_120_, 1);
        v___x_126_ = lean_apply_1(v_h__2_122_, v_val_125_);
        return v___x_126_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__Option_instDecidableEq_match__1_splitter(
    mut v_00_u03b1_127_: *mut LeanObject,
    mut v_motive_128_: *mut LeanObject,
    mut v_b_129_: *mut LeanObject,
    mut v_h__1_130_: *mut LeanObject,
    mut v_h__2_131_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_b_129_) == 0 {
        let mut v___x_132_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_133_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_131_);
        v___x_132_ = lean_box(0);
        v___x_133_ = lean_apply_1(v_h__1_130_, v___x_132_);
        return v___x_133_;
    } else {
        let mut v_val_134_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_135_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_130_);
        v_val_134_ = lean_ctor_get(v_b_129_, 0);
        lean_inc(v_val_134_);
        lean_dec_ref_known(v_b_129_, 1);
        v___x_135_ = lean_apply_1(v_h__2_131_, v_val_134_);
        return v___x_135_;
    }
}
pub unsafe fn l_Option_unattach___redArg(mut v_o_136_: *mut LeanObject) -> *mut LeanObject {
    let mut v___x_137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_141_: u8 = 0;
    let mut v___x_143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_145_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_o_136_) == 0 {
                    v___x_137_ = lean_box(0);
                    return v___x_137_;
                } else {
                    v_val_138_ = lean_ctor_get(v_o_136_, 0);
                    v_isSharedCheck_145_ = (!lean_is_exclusive(v_o_136_)) as u8;
                    if v_isSharedCheck_145_ == 0 {
                        v___x_140_ = v_o_136_;
                        v_isShared_141_ = v_isSharedCheck_145_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_138_);
                        lean_dec(v_o_136_);
                        v___x_140_ = lean_box(0);
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
                    v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_144_, 0, v_val_138_);
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
    mut v_00_u03b1_146_: *mut LeanObject,
    mut v_p_147_: *mut LeanObject,
    mut v_o_148_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_149_: *mut LeanObject = core::ptr::null_mut();
    v___x_149_ = l_Option_unattach___redArg(v_o_148_);
    return v___x_149_;
}
pub unsafe fn l_Option_instMonadAttach___lam__0(
    mut v_00_u03b1_150_: *mut LeanObject,
    mut v_x_151_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc(v_x_151_);
    return v_x_151_;
}
pub unsafe fn l_Option_instMonadAttach___lam__0___boxed(
    mut v_00_u03b1_152_: *mut LeanObject,
    mut v_x_153_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_154_: *mut LeanObject = core::ptr::null_mut();
    v_res_154_ = l_Option_instMonadAttach___lam__0(v_00_u03b1_152_, v_x_153_);
    lean_dec(v_x_153_);
    return v_res_154_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___redArg(
    mut v_x_157_: *mut LeanObject,
    mut v_h__1_158_: *mut LeanObject,
    mut v_h__2_159_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_157_) == 0 {
        let mut v___x_160_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_158_);
        v___x_160_ = lean_apply_1(v_h__2_159_, lean_box(0));
        return v___x_160_;
    } else {
        let mut v_val_161_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_162_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_159_);
        v_val_161_ = lean_ctor_get(v_x_157_, 0);
        lean_inc(v_val_161_);
        lean_dec_ref_known(v_x_157_, 1);
        v___x_162_ = lean_apply_2(v_h__1_158_, v_val_161_, lean_box(0));
        return v___x_162_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter(
    mut v_m_163_: *mut LeanObject,
    mut v_inst_164_: *mut LeanObject,
    mut v_00_u03b1_165_: *mut LeanObject,
    mut v_x_166_: *mut LeanObject,
    mut v_motive_167_: *mut LeanObject,
    mut v_x_168_: *mut LeanObject,
    mut v_h__1_169_: *mut LeanObject,
    mut v_h__2_170_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_168_) == 0 {
        let mut v___x_171_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_169_);
        v___x_171_ = lean_apply_1(v_h__2_170_, lean_box(0));
        return v___x_171_;
    } else {
        let mut v_val_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_170_);
        v_val_172_ = lean_ctor_get(v_x_168_, 0);
        lean_inc(v_val_172_);
        lean_dec_ref_known(v_x_168_, 1);
        v___x_173_ = lean_apply_2(v_h__1_169_, v_val_172_, lean_box(0));
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_instMonadAttach_match__1_splitter___boxed(
    mut v_m_174_: *mut LeanObject,
    mut v_inst_175_: *mut LeanObject,
    mut v_00_u03b1_176_: *mut LeanObject,
    mut v_x_177_: *mut LeanObject,
    mut v_motive_178_: *mut LeanObject,
    mut v_x_179_: *mut LeanObject,
    mut v_h__1_180_: *mut LeanObject,
    mut v_h__2_181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_182_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_x_177_);
    lean_dec(v_inst_175_);
    return v_res_182_;
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter___redArg(
    mut v_____do__lift_183_: *mut LeanObject,
    mut v_h__1_184_: *mut LeanObject,
    mut v_h__2_185_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_183_) == 0 {
        let mut v___x_186_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_187_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_184_);
        v___x_186_ = lean_box(0);
        v___x_187_ = lean_apply_1(v_h__2_185_, v___x_186_);
        return v___x_187_;
    } else {
        let mut v_val_188_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_189_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_185_);
        v_val_188_ = lean_ctor_get(v_____do__lift_183_, 0);
        lean_inc(v_val_188_);
        lean_dec_ref_known(v_____do__lift_183_, 1);
        v___x_189_ = lean_apply_1(v_h__1_184_, v_val_188_);
        return v___x_189_;
    }
}
pub unsafe fn l___private_Init_Data_Option_Attach_0__OptionT_bind_match__1_splitter(
    mut v_00_u03b1_190_: *mut LeanObject,
    mut v_motive_191_: *mut LeanObject,
    mut v_____do__lift_192_: *mut LeanObject,
    mut v_h__1_193_: *mut LeanObject,
    mut v_h__2_194_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_____do__lift_192_) == 0 {
        let mut v___x_195_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_193_);
        v___x_195_ = lean_box(0);
        v___x_196_ = lean_apply_1(v_h__2_194_, v___x_195_);
        return v___x_196_;
    } else {
        let mut v_val_197_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_198_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_194_);
        v_val_197_ = lean_ctor_get(v_____do__lift_192_, 0);
        lean_inc(v_val_197_);
        lean_dec_ref_known(v_____do__lift_192_, 1);
        v___x_198_ = lean_apply_1(v_h__1_193_, v_val_197_);
        return v___x_198_;
    }
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Option_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Option_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Option_Attach(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Bool(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_Array(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Option_List(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Subtype_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Option_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Option_Attach(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Option_Attach(builtin);
}

// Lean compiler output
// Module: Init.Data.Array.BasicAux
// Imports: Init.Data.Array.Basic Init.Data.Array.Set Init.Util Init.Data.Nat.Linear
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::{
    initialize_Init_Data_Array_Basic, runtime_initialize_Init_Data_Array_Basic,
};
use crate::r#gen::Init::Data::Array::Set::{
    initialize_Init_Data_Array_Set, runtime_initialize_Init_Data_Array_Set,
};
use crate::r#gen::Init::Data::Nat::Linear::{
    initialize_Init_Data_Nat_Linear, runtime_initialize_Init_Data_Nat_Linear,
};
use crate::r#gen::Init::Util::{initialize_Init_Util, runtime_initialize_Init_Util};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_get_size, lean_array_push, lean_mk_empty_array_with_capacity,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_apply_1, lean_apply_2, lean_apply_3,
    lean_apply_4, lean_box, lean_closure_set, lean_ctor_get, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_inc, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_obj_tag, lean_unsigned_to_nat,
};
pub static l_Array_mapMono___redArg___closed__0_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__0_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__1_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__1_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__2_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__2_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__3_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__3_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__4_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__4_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__5_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__5_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__6_value: LeanClosureObject<0> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Array_mapMono___redArg___closed__6: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__6_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__7_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__0_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__1_value) as *mut LeanObject,
    ],
};
static mut l_Array_mapMono___redArg___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__7_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__8_value: LeanCtorObject<5> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__7_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__2_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__3_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__4_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__5_value) as *mut LeanObject,
    ],
};
static mut l_Array_mapMono___redArg___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__8_value) as *mut LeanObject;
pub static l_Array_mapMono___redArg___closed__9_value: LeanCtorObject<2> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__8_value) as *mut LeanObject,
        core::ptr::addr_of!(l_Array_mapMono___redArg___closed__6_value) as *mut LeanObject,
    ],
};
static mut l_Array_mapMono___redArg___closed__9: *mut LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__9_value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(
    mut v_x_166_: *mut LeanObject,
    mut v_x_167_: *mut LeanObject,
    mut v_h__1_168_: *mut LeanObject,
    mut v_h__2_169_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_166_) == 0 {
        let mut v___x_170_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_169_);
        v___x_170_ = lean_apply_1(v_h__1_168_, v_x_167_);
        return v___x_170_;
    } else {
        let mut v_head_171_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_172_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_168_);
        v_head_171_ = lean_ctor_get(v_x_166_, 0);
        lean_inc(v_head_171_);
        v_tail_172_ = lean_ctor_get(v_x_166_, 1);
        lean_inc(v_tail_172_);
        lean_dec_ref_known(v_x_166_, 2);
        v___x_173_ = lean_apply_3(v_h__2_169_, v_head_171_, v_tail_172_, v_x_167_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(
    mut v_00_u03b1_174_: *mut LeanObject,
    mut v_motive_175_: *mut LeanObject,
    mut v_x_176_: *mut LeanObject,
    mut v_x_177_: *mut LeanObject,
    mut v_h__1_178_: *mut LeanObject,
    mut v_h__2_179_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_x_176_) == 0 {
        let mut v___x_180_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__2_179_);
        v___x_180_ = lean_apply_1(v_h__1_178_, v_x_177_);
        return v___x_180_;
    } else {
        let mut v_head_181_: *mut LeanObject = core::ptr::null_mut();
        let mut v_tail_182_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_h__1_178_);
        v_head_181_ = lean_ctor_get(v_x_176_, 0);
        lean_inc(v_head_181_);
        v_tail_182_ = lean_ctor_get(v_x_176_, 1);
        lean_inc(v_tail_182_);
        lean_dec_ref_known(v_x_176_, 2);
        v___x_183_ = lean_apply_3(v_h__2_179_, v_head_181_, v_tail_182_, v_x_177_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(
    mut v_i_184_: *mut LeanObject,
    mut v_acc_185_: *mut LeanObject,
    mut v_inst_186_: *mut LeanObject,
    mut v_f_187_: *mut LeanObject,
    mut v_as_188_: *mut LeanObject,
    mut v_b_189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_190_: *mut LeanObject = core::ptr::null_mut();
    v_res_190_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(
        v_i_184_,
        v_acc_185_,
        v_inst_186_,
        v_f_187_,
        v_as_188_,
        v_b_189_,
    );
    lean_dec(v_i_184_);
    return v_res_190_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(
    mut v_inst_191_: *mut LeanObject,
    mut v_f_192_: *mut LeanObject,
    mut v_as_193_: *mut LeanObject,
    mut v_i_194_: *mut LeanObject,
    mut v_acc_195_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    v___x_196_ = lean_array_get_size(v_as_193_);
    v___x_197_ = lean_nat_dec_eq(v_i_194_, v___x_196_);
    if v___x_197_ == 0 {
        let mut v_toBind_198_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_199_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_198_ = lean_ctor_get(v_inst_191_, 1);
        lean_inc(v_toBind_198_);
        lean_inc_ref(v_as_193_);
        lean_inc(v_f_192_);
        lean_inc(v_i_194_);
        v___f_199_ = lean_alloc_closure(
            l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_199_, 0, v_i_194_);
        lean_closure_set(v___f_199_, 1, v_acc_195_);
        lean_closure_set(v___f_199_, 2, v_inst_191_);
        lean_closure_set(v___f_199_, 3, v_f_192_);
        lean_closure_set(v___f_199_, 4, v_as_193_);
        v___x_200_ = lean_array_fget(v_as_193_, v_i_194_);
        lean_dec(v_i_194_);
        lean_dec_ref(v_as_193_);
        v___x_201_ = lean_apply_1(v_f_192_, v___x_200_);
        v___x_202_ = lean_apply_4(
            v_toBind_198_,
            lean_box(0),
            lean_box(0),
            v___x_201_,
            v___f_199_,
        );
        return v___x_202_;
    } else {
        let mut v_toApplicative_203_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_204_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_194_);
        lean_dec_ref(v_as_193_);
        lean_dec(v_f_192_);
        v_toApplicative_203_ = lean_ctor_get(v_inst_191_, 0);
        lean_inc_ref(v_toApplicative_203_);
        lean_dec_ref(v_inst_191_);
        v_toPure_204_ = lean_ctor_get(v_toApplicative_203_, 1);
        lean_inc(v_toPure_204_);
        lean_dec_ref(v_toApplicative_203_);
        v___x_205_ = lean_apply_2(v_toPure_204_, lean_box(0), v_acc_195_);
        return v___x_205_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(
    mut v_i_206_: *mut LeanObject,
    mut v_acc_207_: *mut LeanObject,
    mut v_inst_208_: *mut LeanObject,
    mut v_f_209_: *mut LeanObject,
    mut v_as_210_: *mut LeanObject,
    mut v_b_211_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut LeanObject = core::ptr::null_mut();
    v___x_212_ = lean_unsigned_to_nat(1);
    v___x_213_ = lean_nat_add(v_i_206_, v___x_212_);
    v___x_214_ = lean_array_push(v_acc_207_, v_b_211_);
    v___x_215_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(
        v_inst_208_,
        v_f_209_,
        v_as_210_,
        v___x_213_,
        v___x_214_,
    );
    return v___x_215_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go(
    mut v_m_216_: *mut LeanObject,
    mut v_00_u03b1_217_: *mut LeanObject,
    mut v_00_u03b2_218_: *mut LeanObject,
    mut v_inst_219_: *mut LeanObject,
    mut v_f_220_: *mut LeanObject,
    mut v_as_221_: *mut LeanObject,
    mut v_i_222_: *mut LeanObject,
    mut v_acc_223_: *mut LeanObject,
    mut v_hle_224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_225_: *mut LeanObject = core::ptr::null_mut();
    v___x_225_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(
        v_inst_219_,
        v_f_220_,
        v_as_221_,
        v_i_222_,
        v_acc_223_,
    );
    return v___x_225_;
}
pub unsafe fn l_Array_mapM_x27___redArg(
    mut v_inst_226_: *mut LeanObject,
    mut v_f_227_: *mut LeanObject,
    mut v_as_228_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut LeanObject = core::ptr::null_mut();
    v___x_229_ = lean_unsigned_to_nat(0);
    v___x_230_ = lean_array_get_size(v_as_228_);
    v___x_231_ = lean_mk_empty_array_with_capacity(v___x_230_);
    v___x_232_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(
        v_inst_226_,
        v_f_227_,
        v_as_228_,
        v___x_229_,
        v___x_231_,
    );
    return v___x_232_;
}
pub unsafe fn l_Array_mapM_x27(
    mut v_m_233_: *mut LeanObject,
    mut v_00_u03b1_234_: *mut LeanObject,
    mut v_00_u03b2_235_: *mut LeanObject,
    mut v_inst_236_: *mut LeanObject,
    mut v_f_237_: *mut LeanObject,
    mut v_as_238_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_239_: *mut LeanObject = core::ptr::null_mut();
    v___x_239_ = l_Array_mapM_x27___redArg(v_inst_236_, v_f_237_, v_as_238_);
    return v___x_239_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(
    mut v_a_240_: *mut LeanObject,
    mut v_i_241_: *mut LeanObject,
    mut v_as_242_: *mut LeanObject,
    mut v_inst_243_: *mut LeanObject,
    mut v_f_244_: *mut LeanObject,
    mut v_b_245_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_246_: *mut LeanObject = core::ptr::null_mut();
    v_res_246_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(
        v_a_240_,
        v_i_241_,
        v_as_242_,
        v_inst_243_,
        v_f_244_,
        v_b_245_,
    );
    lean_dec(v_i_241_);
    lean_dec(v_a_240_);
    return v_res_246_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
    mut v_inst_247_: *mut LeanObject,
    mut v_f_248_: *mut LeanObject,
    mut v_i_249_: *mut LeanObject,
    mut v_as_250_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_252_: u8 = 0;
    v___x_251_ = lean_array_get_size(v_as_250_);
    v___x_252_ = lean_nat_dec_lt(v_i_249_, v___x_251_);
    if v___x_252_ == 0 {
        let mut v_toApplicative_253_: *mut LeanObject = core::ptr::null_mut();
        let mut v_toPure_254_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_i_249_);
        lean_dec(v_f_248_);
        v_toApplicative_253_ = lean_ctor_get(v_inst_247_, 0);
        lean_inc_ref(v_toApplicative_253_);
        lean_dec_ref(v_inst_247_);
        v_toPure_254_ = lean_ctor_get(v_toApplicative_253_, 1);
        lean_inc(v_toPure_254_);
        lean_dec_ref(v_toApplicative_253_);
        v___x_255_ = lean_apply_2(v_toPure_254_, lean_box(0), v_as_250_);
        return v___x_255_;
    } else {
        let mut v_toBind_256_: *mut LeanObject = core::ptr::null_mut();
        let mut v_a_257_: *mut LeanObject = core::ptr::null_mut();
        let mut v___f_258_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut LeanObject = core::ptr::null_mut();
        v_toBind_256_ = lean_ctor_get(v_inst_247_, 1);
        lean_inc(v_toBind_256_);
        v_a_257_ = lean_array_fget(v_as_250_, v_i_249_);
        lean_inc(v_f_248_);
        lean_inc(v_a_257_);
        v___f_258_ = lean_alloc_closure(
            l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        lean_closure_set(v___f_258_, 0, v_a_257_);
        lean_closure_set(v___f_258_, 1, v_i_249_);
        lean_closure_set(v___f_258_, 2, v_as_250_);
        lean_closure_set(v___f_258_, 3, v_inst_247_);
        lean_closure_set(v___f_258_, 4, v_f_248_);
        v___x_259_ = lean_apply_1(v_f_248_, v_a_257_);
        v___x_260_ = lean_apply_4(
            v_toBind_256_,
            lean_box(0),
            lean_box(0),
            v___x_259_,
            v___f_258_,
        );
        return v___x_260_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(
    mut v_a_261_: *mut LeanObject,
    mut v_i_262_: *mut LeanObject,
    mut v_as_263_: *mut LeanObject,
    mut v_inst_264_: *mut LeanObject,
    mut v_f_265_: *mut LeanObject,
    mut v_b_266_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_267_: usize = 0;
    let mut v___x_268_: usize = 0;
    let mut v___x_269_: u8 = 0;
    v___x_267_ = lean_ptr_addr(v_a_261_);
    v___x_268_ = lean_ptr_addr(v_b_266_);
    v___x_269_ = lean_usize_dec_eq(v___x_267_, v___x_268_);
    if v___x_269_ == 0 {
        let mut v___x_270_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut LeanObject = core::ptr::null_mut();
        v___x_270_ = lean_unsigned_to_nat(1);
        v___x_271_ = lean_nat_add(v_i_262_, v___x_270_);
        v___x_272_ = lean_array_fset(v_as_263_, v_i_262_, v_b_266_);
        v___x_273_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
            v_inst_264_,
            v_f_265_,
            v___x_271_,
            v___x_272_,
        );
        return v___x_273_;
    } else {
        let mut v___x_274_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_b_266_);
        v___x_274_ = lean_unsigned_to_nat(1);
        v___x_275_ = lean_nat_add(v_i_262_, v___x_274_);
        v___x_276_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
            v_inst_264_,
            v_f_265_,
            v___x_275_,
            v_as_263_,
        );
        return v___x_276_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go(
    mut v_m_277_: *mut LeanObject,
    mut v_00_u03b1_278_: *mut LeanObject,
    mut v_inst_279_: *mut LeanObject,
    mut v_f_280_: *mut LeanObject,
    mut v_i_281_: *mut LeanObject,
    mut v_as_282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_283_: *mut LeanObject = core::ptr::null_mut();
    v___x_283_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_279_,
        v_f_280_,
        v_i_281_,
        v_as_282_,
    );
    return v___x_283_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(
    mut v_inst_284_: *mut LeanObject,
    mut v_as_285_: *mut LeanObject,
    mut v_f_286_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut LeanObject = core::ptr::null_mut();
    v___x_287_ = lean_unsigned_to_nat(0);
    v___x_288_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_284_,
        v_f_286_,
        v___x_287_,
        v_as_285_,
    );
    return v___x_288_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(
    mut v_m_289_: *mut LeanObject,
    mut v_00_u03b1_290_: *mut LeanObject,
    mut v_inst_291_: *mut LeanObject,
    mut v_as_292_: *mut LeanObject,
    mut v_f_293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut LeanObject = core::ptr::null_mut();
    v___x_294_ = lean_unsigned_to_nat(0);
    v___x_295_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_291_,
        v_f_293_,
        v___x_294_,
        v_as_292_,
    );
    return v___x_295_;
}
pub unsafe fn l_Array_mapMono___redArg___lam__0(
    mut v_f_296_: *mut LeanObject,
    mut v_x_297_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_298_: *mut LeanObject = core::ptr::null_mut();
    v___x_298_ = lean_apply_1(v_f_296_, v_x_297_);
    return v___x_298_;
}
pub unsafe fn l_Array_mapMono___redArg(
    mut v_as_318_: *mut LeanObject,
    mut v_f_319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_320_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut LeanObject = core::ptr::null_mut();
    v___f_320_ = lean_alloc_closure(
        l_Array_mapMono___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_320_, 0, v_f_319_);
    v___x_321_ = l_Array_mapMono___redArg___closed__9;
    v___x_322_ = lean_unsigned_to_nat(0);
    v___x_323_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v___x_321_, v___f_320_, v___x_322_, v_as_318_,
    );
    return v___x_323_;
}
pub unsafe fn l_Array_mapMono(
    mut v_00_u03b1_324_: *mut LeanObject,
    mut v_as_325_: *mut LeanObject,
    mut v_f_326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut LeanObject = core::ptr::null_mut();
    v___f_327_ = lean_alloc_closure(
        l_Array_mapMono___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_327_, 0, v_f_326_);
    v___x_328_ = l_Array_mapMono___redArg___closed__9;
    v___x_329_ = lean_unsigned_to_nat(0);
    v___x_330_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v___x_328_, v___f_327_, v___x_329_, v_as_325_,
    );
    return v___x_330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Array_BasicAux(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_BasicAux(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Init_Data_Array_BasicAux(builtin);
}

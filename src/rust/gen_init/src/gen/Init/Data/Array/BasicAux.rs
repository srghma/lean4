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
pub static l_Array_mapMono___redArg___closed__0_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__1_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__2_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__3_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__4_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__5_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__6_value: crate::leanh::LeanClosureObject<0> =
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
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Array_mapMono___redArg___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__7_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__0_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__1_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_mapMono___redArg___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__8_value: crate::leanh::LeanCtorObject<5> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__7_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__2_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__3_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__4_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__5_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_mapMono___redArg___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Array_mapMono___redArg___closed__9_value: crate::leanh::LeanCtorObject<2> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__8_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Array_mapMono___redArg___closed__6_value)
                as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Array_mapMono___redArg___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Array_mapMono___redArg___closed__9_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter___redArg(
    mut v_x_166_: *mut crate::leanh::LeanObject,
    mut v_x_167_: *mut crate::leanh::LeanObject,
    mut v_h__1_168_: *mut crate::leanh::LeanObject,
    mut v_h__2_169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_166_) == 0 {
        let mut v___x_170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_169_);
        v___x_170_ = crate::leanh::lean_apply_1(v_h__1_168_, v_x_167_);
        return v___x_170_;
    } else {
        let mut v_head_171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_168_);
        v_head_171_ = crate::leanh::lean_ctor_get(v_x_166_, 0);
        crate::leanh::lean_inc(v_head_171_);
        v_tail_172_ = crate::leanh::lean_ctor_get(v_x_166_, 1);
        crate::leanh::lean_inc(v_tail_172_);
        crate::leanh::lean_dec_ref_known(v_x_166_, 2);
        v___x_173_ = crate::leanh::lean_apply_3(v_h__2_169_, v_head_171_, v_tail_172_, v_x_167_);
        return v___x_173_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__List_toArrayAux_match__1_splitter(
    mut v_00_u03b1_174_: *mut crate::leanh::LeanObject,
    mut v_motive_175_: *mut crate::leanh::LeanObject,
    mut v_x_176_: *mut crate::leanh::LeanObject,
    mut v_x_177_: *mut crate::leanh::LeanObject,
    mut v_h__1_178_: *mut crate::leanh::LeanObject,
    mut v_h__2_179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_176_) == 0 {
        let mut v___x_180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__2_179_);
        v___x_180_ = crate::leanh::lean_apply_1(v_h__1_178_, v_x_177_);
        return v___x_180_;
    } else {
        let mut v_head_181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_h__1_178_);
        v_head_181_ = crate::leanh::lean_ctor_get(v_x_176_, 0);
        crate::leanh::lean_inc(v_head_181_);
        v_tail_182_ = crate::leanh::lean_ctor_get(v_x_176_, 1);
        crate::leanh::lean_inc(v_tail_182_);
        crate::leanh::lean_dec_ref_known(v_x_176_, 2);
        v___x_183_ = crate::leanh::lean_apply_3(v_h__2_179_, v_head_181_, v_tail_182_, v_x_177_);
        return v___x_183_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed(
    mut v_i_184_: *mut crate::leanh::LeanObject,
    mut v_acc_185_: *mut crate::leanh::LeanObject,
    mut v_inst_186_: *mut crate::leanh::LeanObject,
    mut v_f_187_: *mut crate::leanh::LeanObject,
    mut v_as_188_: *mut crate::leanh::LeanObject,
    mut v_b_189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_190_ = l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(
        v_i_184_,
        v_acc_185_,
        v_inst_186_,
        v_f_187_,
        v_as_188_,
        v_b_189_,
    );
    crate::leanh::lean_dec(v_i_184_);
    return v_res_190_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg(
    mut v_inst_191_: *mut crate::leanh::LeanObject,
    mut v_f_192_: *mut crate::leanh::LeanObject,
    mut v_as_193_: *mut crate::leanh::LeanObject,
    mut v_i_194_: *mut crate::leanh::LeanObject,
    mut v_acc_195_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_197_: u8 = 0;
    v___x_196_ = lean_array_get_size(v_as_193_);
    v___x_197_ = lean_nat_dec_eq(v_i_194_, v___x_196_);
    if v___x_197_ == 0 {
        let mut v_toBind_198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_198_ = crate::leanh::lean_ctor_get(v_inst_191_, 1);
        crate::leanh::lean_inc(v_toBind_198_);
        crate::leanh::lean_inc_ref(v_as_193_);
        crate::leanh::lean_inc(v_f_192_);
        crate::leanh::lean_inc(v_i_194_);
        v___f_199_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_199_, 0, v_i_194_);
        crate::leanh::lean_closure_set(v___f_199_, 1, v_acc_195_);
        crate::leanh::lean_closure_set(v___f_199_, 2, v_inst_191_);
        crate::leanh::lean_closure_set(v___f_199_, 3, v_f_192_);
        crate::leanh::lean_closure_set(v___f_199_, 4, v_as_193_);
        v___x_200_ = lean_array_fget(v_as_193_, v_i_194_);
        crate::leanh::lean_dec(v_i_194_);
        crate::leanh::lean_dec_ref(v_as_193_);
        v___x_201_ = crate::leanh::lean_apply_1(v_f_192_, v___x_200_);
        v___x_202_ = crate::leanh::lean_apply_4(
            v_toBind_198_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_201_,
            v___f_199_,
        );
        return v___x_202_;
    } else {
        let mut v_toApplicative_203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_194_);
        crate::leanh::lean_dec_ref(v_as_193_);
        crate::leanh::lean_dec(v_f_192_);
        v_toApplicative_203_ = crate::leanh::lean_ctor_get(v_inst_191_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_203_);
        crate::leanh::lean_dec_ref(v_inst_191_);
        v_toPure_204_ = crate::leanh::lean_ctor_get(v_toApplicative_203_, 1);
        crate::leanh::lean_inc(v_toPure_204_);
        crate::leanh::lean_dec_ref(v_toApplicative_203_);
        v___x_205_ =
            crate::leanh::lean_apply_2(v_toPure_204_, crate::leanh::lean_box(0), v_acc_195_);
        return v___x_205_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__Array_mapM_x27_go___redArg___lam__0(
    mut v_i_206_: *mut crate::leanh::LeanObject,
    mut v_acc_207_: *mut crate::leanh::LeanObject,
    mut v_inst_208_: *mut crate::leanh::LeanObject,
    mut v_f_209_: *mut crate::leanh::LeanObject,
    mut v_as_210_: *mut crate::leanh::LeanObject,
    mut v_b_211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_212_ = crate::leanh::lean_unsigned_to_nat(1);
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
    mut v_m_216_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_217_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_218_: *mut crate::leanh::LeanObject,
    mut v_inst_219_: *mut crate::leanh::LeanObject,
    mut v_f_220_: *mut crate::leanh::LeanObject,
    mut v_as_221_: *mut crate::leanh::LeanObject,
    mut v_i_222_: *mut crate::leanh::LeanObject,
    mut v_acc_223_: *mut crate::leanh::LeanObject,
    mut v_hle_224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    mut v_inst_226_: *mut crate::leanh::LeanObject,
    mut v_f_227_: *mut crate::leanh::LeanObject,
    mut v_as_228_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_229_ = crate::leanh::lean_unsigned_to_nat(0);
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
    mut v_m_233_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_234_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_235_: *mut crate::leanh::LeanObject,
    mut v_inst_236_: *mut crate::leanh::LeanObject,
    mut v_f_237_: *mut crate::leanh::LeanObject,
    mut v_as_238_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_239_ = l_Array_mapM_x27___redArg(v_inst_236_, v_f_237_, v_as_238_);
    return v___x_239_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed(
    mut v_a_240_: *mut crate::leanh::LeanObject,
    mut v_i_241_: *mut crate::leanh::LeanObject,
    mut v_as_242_: *mut crate::leanh::LeanObject,
    mut v_inst_243_: *mut crate::leanh::LeanObject,
    mut v_f_244_: *mut crate::leanh::LeanObject,
    mut v_b_245_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_246_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(
        v_a_240_,
        v_i_241_,
        v_as_242_,
        v_inst_243_,
        v_f_244_,
        v_b_245_,
    );
    crate::leanh::lean_dec(v_i_241_);
    crate::leanh::lean_dec(v_a_240_);
    return v_res_246_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
    mut v_inst_247_: *mut crate::leanh::LeanObject,
    mut v_f_248_: *mut crate::leanh::LeanObject,
    mut v_i_249_: *mut crate::leanh::LeanObject,
    mut v_as_250_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_252_: u8 = 0;
    v___x_251_ = lean_array_get_size(v_as_250_);
    v___x_252_ = lean_nat_dec_lt(v_i_249_, v___x_251_);
    if v___x_252_ == 0 {
        let mut v_toApplicative_253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_toPure_254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_i_249_);
        crate::leanh::lean_dec(v_f_248_);
        v_toApplicative_253_ = crate::leanh::lean_ctor_get(v_inst_247_, 0);
        crate::leanh::lean_inc_ref(v_toApplicative_253_);
        crate::leanh::lean_dec_ref(v_inst_247_);
        v_toPure_254_ = crate::leanh::lean_ctor_get(v_toApplicative_253_, 1);
        crate::leanh::lean_inc(v_toPure_254_);
        crate::leanh::lean_dec_ref(v_toApplicative_253_);
        v___x_255_ =
            crate::leanh::lean_apply_2(v_toPure_254_, crate::leanh::lean_box(0), v_as_250_);
        return v___x_255_;
    } else {
        let mut v_toBind_256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_a_257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___f_258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_toBind_256_ = crate::leanh::lean_ctor_get(v_inst_247_, 1);
        crate::leanh::lean_inc(v_toBind_256_);
        v_a_257_ = lean_array_fget(v_as_250_, v_i_249_);
        crate::leanh::lean_inc(v_f_248_);
        crate::leanh::lean_inc(v_a_257_);
        v___f_258_ = crate::leanh::lean_alloc_closure(
            l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0___boxed
                as *mut core::ffi::c_void,
            6,
            5,
        );
        crate::leanh::lean_closure_set(v___f_258_, 0, v_a_257_);
        crate::leanh::lean_closure_set(v___f_258_, 1, v_i_249_);
        crate::leanh::lean_closure_set(v___f_258_, 2, v_as_250_);
        crate::leanh::lean_closure_set(v___f_258_, 3, v_inst_247_);
        crate::leanh::lean_closure_set(v___f_258_, 4, v_f_248_);
        v___x_259_ = crate::leanh::lean_apply_1(v_f_248_, v_a_257_);
        v___x_260_ = crate::leanh::lean_apply_4(
            v_toBind_256_,
            crate::leanh::lean_box(0),
            crate::leanh::lean_box(0),
            v___x_259_,
            v___f_258_,
        );
        return v___x_260_;
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg___lam__0(
    mut v_a_261_: *mut crate::leanh::LeanObject,
    mut v_i_262_: *mut crate::leanh::LeanObject,
    mut v_as_263_: *mut crate::leanh::LeanObject,
    mut v_inst_264_: *mut crate::leanh::LeanObject,
    mut v_f_265_: *mut crate::leanh::LeanObject,
    mut v_b_266_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_267_: usize = 0;
    let mut v___x_268_: usize = 0;
    let mut v___x_269_: u8 = 0;
    v___x_267_ = lean_ptr_addr(v_a_261_);
    v___x_268_ = lean_ptr_addr(v_b_266_);
    v___x_269_ = lean_usize_dec_eq(v___x_267_, v___x_268_);
    if v___x_269_ == 0 {
        let mut v___x_270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_270_ = crate::leanh::lean_unsigned_to_nat(1);
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
        let mut v___x_274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_b_266_);
        v___x_274_ = crate::leanh::lean_unsigned_to_nat(1);
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
    mut v_m_277_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_278_: *mut crate::leanh::LeanObject,
    mut v_inst_279_: *mut crate::leanh::LeanObject,
    mut v_f_280_: *mut crate::leanh::LeanObject,
    mut v_i_281_: *mut crate::leanh::LeanObject,
    mut v_as_282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_279_,
        v_f_280_,
        v_i_281_,
        v_as_282_,
    );
    return v___x_283_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp___redArg(
    mut v_inst_284_: *mut crate::leanh::LeanObject,
    mut v_as_285_: *mut crate::leanh::LeanObject,
    mut v_f_286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_287_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_288_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_284_,
        v_f_286_,
        v___x_287_,
        v_as_285_,
    );
    return v___x_288_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp(
    mut v_m_289_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_290_: *mut crate::leanh::LeanObject,
    mut v_inst_291_: *mut crate::leanh::LeanObject,
    mut v_as_292_: *mut crate::leanh::LeanObject,
    mut v_f_293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_294_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_295_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v_inst_291_,
        v_f_293_,
        v___x_294_,
        v_as_292_,
    );
    return v___x_295_;
}
pub unsafe fn l_Array_mapMono___redArg___lam__0(
    mut v_f_296_: *mut crate::leanh::LeanObject,
    mut v_x_297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_298_ = crate::leanh::lean_apply_1(v_f_296_, v_x_297_);
    return v___x_298_;
}
pub unsafe fn l_Array_mapMono___redArg(
    mut v_as_318_: *mut crate::leanh::LeanObject,
    mut v_f_319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_320_ = crate::leanh::lean_alloc_closure(
        l_Array_mapMono___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_320_, 0, v_f_319_);
    v___x_321_ = l_Array_mapMono___redArg___closed__9;
    v___x_322_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_323_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v___x_321_, v___f_320_, v___x_322_, v_as_318_,
    );
    return v___x_323_;
}
pub unsafe fn l_Array_mapMono(
    mut v_00_u03b1_324_: *mut crate::leanh::LeanObject,
    mut v_as_325_: *mut crate::leanh::LeanObject,
    mut v_f_326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_327_ = crate::leanh::lean_alloc_closure(
        l_Array_mapMono___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_327_, 0, v_f_326_);
    v___x_328_ = l_Array_mapMono___redArg___closed__9;
    v___x_329_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_330_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___redArg(
        v___x_328_, v___f_327_, v___x_329_, v_as_325_,
    );
    return v___x_330_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Array_BasicAux(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Set(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Array_BasicAux(
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
pub unsafe fn initialize_Init_Data_Array_BasicAux(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Array_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Set(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Linear(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Array_BasicAux(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Init_Data_Array_BasicAux(builtin);
}

// Lean compiler output
// Module: Init.Data.Vector.Attach
// Imports: Init.Data.Vector.Lemmas Init.Data.Array.Attach
use crate::ffi::{
    lean_array_size, lean_array_uget, lean_array_uset, lean_usize_add, lean_usize_dec_lt,
};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Attach::{
    initialize_Init_Data_Array_Attach,
    l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg,
    runtime_initialize_Init_Data_Array_Attach,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map;
use crate::r#gen::Init::Data::Vector::Lemmas::{
    initialize_Init_Data_Vector_Lemmas, runtime_initialize_Init_Data_Vector_Lemmas,
};
pub static l_Vector_pmapImpl___redArg___closed__0_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__1_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__2_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
        m_arity: 2,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__3_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__4_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__5_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__6_value: leanh::LeanClosureObject<0> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 0)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
        m_arity: 4,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Vector_pmapImpl___redArg___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__7_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__0_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__1_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_pmapImpl___redArg___closed__7: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__8_value: leanh::LeanCtorObject<5> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 5
                + 0) as u16,
            other: 5,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__7_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__3_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__4_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__5_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_pmapImpl___redArg___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Vector_pmapImpl___redArg___closed__9_value: leanh::LeanCtorObject<2> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 2
                + 0) as u16,
            other: 2,
            tag: 0,
        },
        m_objs: [
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__8_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__6_value)
                as *mut leanh::LeanObject,
        ],
    };
static mut l_Vector_pmapImpl___redArg___closed__9: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Vector_pmapImpl___redArg___closed__9_value)
        as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(
    mut v_f_145_: *mut leanh::LeanObject,
    mut v_sz_146_: usize,
    mut v_i_147_: usize,
    mut v_bs_148_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_149_: u8 = 0;
    let mut v_v_150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_154_: usize = 0;
    let mut v___x_155_: usize = 0;
    let mut v___x_156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_149_ = lean_usize_dec_lt(v_i_147_, v_sz_146_);
                if v___x_149_ == 0 {
                    leanh::lean_dec(v_f_145_);
                    return v_bs_148_;
                } else {
                    v_v_150_ = lean_array_uget(v_bs_148_, v_i_147_);
                    v___x_151_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_152_ = lean_array_uset(v_bs_148_, v_i_147_, v___x_151_);
                    leanh::lean_inc(v_f_145_);
                    v___x_153_ =
                        leanh::lean_apply_2(v_f_145_, v_v_150_, leanh::lean_box(0));
                    v___x_154_ = 1usize;
                    v___x_155_ = lean_usize_add(v_i_147_, v___x_154_);
                    v___x_156_ = lean_array_uset(v_bs_x27_152_, v_i_147_, v___x_153_);
                    v_i_147_ = v___x_155_;
                    v_bs_148_ = v___x_156_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg___boxed(
    mut v_f_158_: *mut leanh::LeanObject,
    mut v_sz_159_: *mut leanh::LeanObject,
    mut v_i_160_: *mut leanh::LeanObject,
    mut v_bs_161_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_162_: usize = 0;
    let mut v_i_boxed_163_: usize = 0;
    let mut v_res_164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_162_ = leanh::lean_unbox_usize(v_sz_159_);
    leanh::lean_dec(v_sz_159_);
    v_i_boxed_163_ = leanh::lean_unbox_usize(v_i_160_);
    leanh::lean_dec(v_i_160_);
    v_res_164_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_158_, v_sz_boxed_162_, v_i_boxed_163_, v_bs_161_);
    return v_res_164_;
}
pub unsafe fn l_Vector_pmap___redArg(
    mut v_f_165_: *mut leanh::LeanObject,
    mut v_xs_166_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_167_: usize = 0;
    let mut v___x_168_: usize = 0;
    let mut v___x_169_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_167_ = lean_array_size(v_xs_166_);
    v___x_168_ = 0usize;
    v___x_169_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_165_, v_sz_167_, v___x_168_, v_xs_166_);
    return v___x_169_;
}
pub unsafe fn l_Vector_pmap(
    mut v_00_u03b1_170_: *mut leanh::LeanObject,
    mut v_00_u03b2_171_: *mut leanh::LeanObject,
    mut v_n_172_: *mut leanh::LeanObject,
    mut v_P_173_: *mut leanh::LeanObject,
    mut v_f_174_: *mut leanh::LeanObject,
    mut v_xs_175_: *mut leanh::LeanObject,
    mut v_H_176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_177_ = l_Vector_pmap___redArg(v_f_174_, v_xs_175_);
    return v___x_177_;
}
pub unsafe fn l_Vector_pmap___boxed(
    mut v_00_u03b1_178_: *mut leanh::LeanObject,
    mut v_00_u03b2_179_: *mut leanh::LeanObject,
    mut v_n_180_: *mut leanh::LeanObject,
    mut v_P_181_: *mut leanh::LeanObject,
    mut v_f_182_: *mut leanh::LeanObject,
    mut v_xs_183_: *mut leanh::LeanObject,
    mut v_H_184_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_185_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_185_ = l_Vector_pmap(
        v_00_u03b1_178_,
        v_00_u03b2_179_,
        v_n_180_,
        v_P_181_,
        v_f_182_,
        v_xs_183_,
        v_H_184_,
    );
    leanh::lean_dec(v_n_180_);
    return v_res_185_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(
    mut v_00_u03b1_186_: *mut leanh::LeanObject,
    mut v_00_u03b2_187_: *mut leanh::LeanObject,
    mut v_f_188_: *mut leanh::LeanObject,
    mut v_sz_189_: usize,
    mut v_i_190_: usize,
    mut v_bs_191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_192_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___redArg(v_f_188_, v_sz_189_, v_i_190_, v_bs_191_);
    return v___x_192_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0___boxed(
    mut v_00_u03b1_193_: *mut leanh::LeanObject,
    mut v_00_u03b2_194_: *mut leanh::LeanObject,
    mut v_f_195_: *mut leanh::LeanObject,
    mut v_sz_196_: *mut leanh::LeanObject,
    mut v_i_197_: *mut leanh::LeanObject,
    mut v_bs_198_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_199_: usize = 0;
    let mut v_i_boxed_200_: usize = 0;
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_199_ = leanh::lean_unbox_usize(v_sz_196_);
    leanh::lean_dec(v_sz_196_);
    v_i_boxed_200_ = leanh::lean_unbox_usize(v_i_197_);
    leanh::lean_dec(v_i_197_);
    v_res_201_ =
        l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Vector_pmap_spec__0(
            v_00_u03b1_193_,
            v_00_u03b2_194_,
            v_f_195_,
            v_sz_boxed_199_,
            v_i_boxed_200_,
            v_bs_198_,
        );
    return v_res_201_;
}
pub unsafe fn l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(
    mut v_xs_202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_202_);
    return v_xs_202_;
}
pub unsafe fn l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg___boxed(
    mut v_xs_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_204_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___redArg(v_xs_203_);
    leanh::lean_dec_ref(v_xs_203_);
    return v_res_204_;
}
pub unsafe fn l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(
    mut v_00_u03b1_205_: *mut leanh::LeanObject,
    mut v_n_206_: *mut leanh::LeanObject,
    mut v_xs_207_: *mut leanh::LeanObject,
    mut v_P_208_: *mut leanh::LeanObject,
    mut v_x_209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_207_);
    return v_xs_207_;
}
pub unsafe fn l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl___boxed(
    mut v_00_u03b1_210_: *mut leanh::LeanObject,
    mut v_n_211_: *mut leanh::LeanObject,
    mut v_xs_212_: *mut leanh::LeanObject,
    mut v_P_213_: *mut leanh::LeanObject,
    mut v_x_214_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_215_ = l___private_Init_Data_Vector_Attach_0__Vector_attachWithImpl(
        v_00_u03b1_210_,
        v_n_211_,
        v_xs_212_,
        v_P_213_,
        v_x_214_,
    );
    leanh::lean_dec_ref(v_xs_212_);
    leanh::lean_dec(v_n_211_);
    return v_res_215_;
}
pub unsafe fn l_Vector_attach___redArg(
    mut v_xs_216_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_216_);
    return v_xs_216_;
}
pub unsafe fn l_Vector_attach___redArg___boxed(
    mut v_xs_217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_218_ = l_Vector_attach___redArg(v_xs_217_);
    leanh::lean_dec_ref(v_xs_217_);
    return v_res_218_;
}
pub unsafe fn l_Vector_attach(
    mut v_00_u03b1_219_: *mut leanh::LeanObject,
    mut v_n_220_: *mut leanh::LeanObject,
    mut v_xs_221_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v_xs_221_);
    return v_xs_221_;
}
pub unsafe fn l_Vector_attach___boxed(
    mut v_00_u03b1_222_: *mut leanh::LeanObject,
    mut v_n_223_: *mut leanh::LeanObject,
    mut v_xs_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_225_ = l_Vector_attach(v_00_u03b1_222_, v_n_223_, v_xs_224_);
    leanh::lean_dec_ref(v_xs_224_);
    leanh::lean_dec(v_n_223_);
    return v_res_225_;
}
pub unsafe fn l_Vector_pmapImpl___redArg___lam__0(
    mut v_f_226_: *mut leanh::LeanObject,
    mut v_x_227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_228_ = leanh::lean_apply_2(v_f_226_, v_x_227_, leanh::lean_box(0));
    return v___x_228_;
}
pub unsafe fn l_Vector_pmapImpl___redArg(
    mut v_f_248_: *mut leanh::LeanObject,
    mut v_xs_249_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_252_: usize = 0;
    let mut v___x_253_: usize = 0;
    let mut v___x_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_250_ = leanh::lean_alloc_closure(
        l_Vector_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_250_, 0, v_f_248_);
    v___x_251_ = l_Vector_pmapImpl___redArg___closed__9;
    v_sz_252_ = lean_array_size(v_xs_249_);
    v___x_253_ = 0usize;
    v___x_254_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_251_,
        v___f_250_,
        v_sz_252_,
        v___x_253_,
        v_xs_249_,
    );
    return v___x_254_;
}
pub unsafe fn l_Vector_pmapImpl(
    mut v_00_u03b1_255_: *mut leanh::LeanObject,
    mut v_00_u03b2_256_: *mut leanh::LeanObject,
    mut v_n_257_: *mut leanh::LeanObject,
    mut v_P_258_: *mut leanh::LeanObject,
    mut v_f_259_: *mut leanh::LeanObject,
    mut v_xs_260_: *mut leanh::LeanObject,
    mut v_H_261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_264_: usize = 0;
    let mut v___x_265_: usize = 0;
    let mut v___x_266_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_262_ = leanh::lean_alloc_closure(
        l_Vector_pmapImpl___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_262_, 0, v_f_259_);
    v___x_263_ = l_Vector_pmapImpl___redArg___closed__9;
    v_sz_264_ = lean_array_size(v_xs_260_);
    v___x_265_ = 0usize;
    v___x_266_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_263_,
        v___f_262_,
        v_sz_264_,
        v___x_265_,
        v_xs_260_,
    );
    return v___x_266_;
}
pub unsafe fn l_Vector_pmapImpl___boxed(
    mut v_00_u03b1_267_: *mut leanh::LeanObject,
    mut v_00_u03b2_268_: *mut leanh::LeanObject,
    mut v_n_269_: *mut leanh::LeanObject,
    mut v_P_270_: *mut leanh::LeanObject,
    mut v_f_271_: *mut leanh::LeanObject,
    mut v_xs_272_: *mut leanh::LeanObject,
    mut v_H_273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_274_ = l_Vector_pmapImpl(
        v_00_u03b1_267_,
        v_00_u03b2_268_,
        v_n_269_,
        v_P_270_,
        v_f_271_,
        v_xs_272_,
        v_H_273_,
    );
    leanh::lean_dec(v_n_269_);
    return v_res_274_;
}
pub unsafe fn l_Vector_unattach___redArg(
    mut v_xs_275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_276_: usize = 0;
    let mut v___x_277_: usize = 0;
    let mut v___x_278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_276_ = lean_array_size(v_xs_275_);
    v___x_277_ = 0usize;
    v___x_278_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Array_unattach_spec__0___redArg(v_sz_276_, v___x_277_, v_xs_275_);
    return v___x_278_;
}
pub unsafe fn l_Vector_unattach(
    mut v_n_279_: *mut leanh::LeanObject,
    mut v_00_u03b1_280_: *mut leanh::LeanObject,
    mut v_p_281_: *mut leanh::LeanObject,
    mut v_xs_282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_283_ = l_Vector_unattach___redArg(v_xs_282_);
    return v___x_283_;
}
pub unsafe fn l_Vector_unattach___boxed(
    mut v_n_284_: *mut leanh::LeanObject,
    mut v_00_u03b1_285_: *mut leanh::LeanObject,
    mut v_p_286_: *mut leanh::LeanObject,
    mut v_xs_287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_288_ = l_Vector_unattach(v_n_284_, v_00_u03b1_285_, v_p_286_, v_xs_287_);
    leanh::lean_dec(v_n_284_);
    return v_res_288_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Init_Data_Vector_Attach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Init_Data_Vector_Attach(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_meta_initialized = true;
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Init_Data_Vector_Attach(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Init_Data_Vector_Lemmas(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Array_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Vector_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Init_Data_Vector_Attach(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Init_Data_Vector_Attach(builtin);
}
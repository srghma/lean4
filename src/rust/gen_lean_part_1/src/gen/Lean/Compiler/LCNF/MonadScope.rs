// Lean compiler output
// Module: Lean.Compiler.LCNF.MonadScope
// Imports: Lean.Compiler.LCNF.Basic
use crate::ffi::{lean_array_get_size, lean_nat_dec_le, lean_nat_dec_lt, lean_usize_of_nat};
use crate::r#gen::Init::Control::Id::{
    l_Id_instMonad___lam__0, l_Id_instMonad___lam__1___boxed, l_Id_instMonad___lam__2___boxed,
    l_Id_instMonad___lam__3, l_Id_instMonad___lam__4___boxed, l_Id_instMonad___lam__5___boxed,
    l_Id_instMonad___lam__6,
};
use crate::r#gen::Init::Data::Array::Basic::l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold;
use crate::r#gen::Init::Prelude::l_ReaderT_read___boxed;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    initialize_Lean_Compiler_LCNF_Basic, runtime_initialize_Lean_Compiler_LCNF_Basic,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed;
use crate::r#gen::Lean::Expr::l_Lean_FVarIdSet_insert;
use crate::r#gen::Std::Data::DTreeMap::Internal::Queries::l_Std_DTreeMap_Internal_Impl_contains___redArg;
pub static l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_inScope___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_inScope___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_inScope___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__0 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__1___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__2___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__3 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__4___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__5___boxed as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Id_instMonad___lam__6 as *const core::ffi::c_void,
    m_arity: 4,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__0_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__1_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value:
    leanh::LeanCtorObject<5> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 5
            + 0) as u16,
        other: 5,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__7_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__2_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__3_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__5_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__8_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__6_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withParams___redArg___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_withParams___redArg___lam__0 as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_withParams___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withParams___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0_value:
    leanh::LeanClosureObject<1> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 1,
    m_objs: [(((1 as usize) << 1) | 1) as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(
    mut v_00_u03b1_191_: *mut leanh::LeanObject,
    mut v___y_192_: *mut leanh::LeanObject,
    mut v___y_193_: *mut leanh::LeanObject,
    mut v___y_194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_196_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_194_);
    v___x_195_ = leanh::lean_apply_1(v___y_192_, v___y_194_);
    v___x_196_ = leanh::lean_apply_1(v___y_193_, v___x_195_);
    return v___x_196_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0___boxed(
    mut v_00_u03b1_197_: *mut leanh::LeanObject,
    mut v___y_198_: *mut leanh::LeanObject,
    mut v___y_199_: *mut leanh::LeanObject,
    mut v___y_200_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_201_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___lam__0(
        v_00_u03b1_197_,
        v___y_198_,
        v___y_199_,
        v___y_200_,
    );
    leanh::lean_dec(v___y_200_);
    return v_res_201_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(
    mut v_inst_203_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_206_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_204_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg___closed__0;
    v___x_205_ =
        leanh::lean_alloc_closure(l_ReaderT_read___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___x_205_, 0, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_205_, 1, leanh::lean_box(0));
    leanh::lean_closure_set(v___x_205_, 2, v_inst_203_);
    v___x_206_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_206_, 0, v___x_205_);
    leanh::lean_ctor_set(v___x_206_, 1, v___f_204_);
    return v___x_206_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad(
    mut v_m_207_: *mut leanh::LeanObject,
    mut v_inst_208_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_209_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_209_ = l_Lean_Compiler_LCNF_instMonadScopeScopeTOfMonad___redArg(v_inst_208_);
    return v___x_209_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0(
    mut v_withScope_210_: *mut leanh::LeanObject,
    mut v_f_211_: *mut leanh::LeanObject,
    mut v_00_u03b2_212_: *mut leanh::LeanObject,
    mut v___y_213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_214_ = leanh::lean_apply_3(
        v_withScope_210_,
        leanh::lean_box(0),
        v_f_211_,
        v___y_213_,
    );
    return v___x_214_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1(
    mut v_withScope_215_: *mut leanh::LeanObject,
    mut v_inst_216_: *mut leanh::LeanObject,
    mut v_00_u03b1_217_: *mut leanh::LeanObject,
    mut v_f_218_: *mut leanh::LeanObject,
    mut v___y_219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_220_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__0
            as *mut core::ffi::c_void,
        4,
        2,
    );
    leanh::lean_closure_set(v___f_220_, 0, v_withScope_215_);
    leanh::lean_closure_set(v___f_220_, 1, v_f_218_);
    v___x_221_ = leanh::lean_apply_3(
        v_inst_216_,
        leanh::lean_box(0),
        v___f_220_,
        v___y_219_,
    );
    return v___x_221_;
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(
    mut v_inst_222_: *mut leanh::LeanObject,
    mut v_inst_223_: *mut leanh::LeanObject,
    mut v_inst_224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_getScope_225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_withScope_226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_229_: u8 = 0;
    let mut v___f_230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_235_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_getScope_225_ = leanh::lean_ctor_get(v_inst_224_, 0);
                v_withScope_226_ = leanh::lean_ctor_get(v_inst_224_, 1);
                v_isSharedCheck_235_ = (!leanh::lean_is_exclusive(v_inst_224_)) as u8;
                if v_isSharedCheck_235_ == 0 {
                    v___x_228_ = v_inst_224_;
                    v_isShared_229_ = v_isSharedCheck_235_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_withScope_226_);
                    leanh::lean_inc(v_getScope_225_);
                    leanh::lean_dec(v_inst_224_);
                    v___x_228_ = leanh::lean_box(0);
                    v_isShared_229_ = v_isSharedCheck_235_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___f_230_ = leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg___lam__1
                        as *mut core::ffi::c_void,
                    5,
                    2,
                );
                leanh::lean_closure_set(v___f_230_, 0, v_withScope_226_);
                leanh::lean_closure_set(v___f_230_, 1, v_inst_223_);
                v___x_231_ = leanh::lean_apply_2(
                    v_inst_222_,
                    leanh::lean_box(0),
                    v_getScope_225_,
                );
                if v_isShared_229_ == 0 {
                    leanh::lean_ctor_set(v___x_228_, 1, v___f_230_);
                    leanh::lean_ctor_set(v___x_228_, 0, v___x_231_);
                    v___x_233_ = v___x_228_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_234_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_234_, 0, v___x_231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_234_, 1, v___f_230_);
                    v___x_233_ = v_reuseFailAlloc_234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor(
    mut v_m_236_: *mut leanh::LeanObject,
    mut v_n_237_: *mut leanh::LeanObject,
    mut v_inst_238_: *mut leanh::LeanObject,
    mut v_inst_239_: *mut leanh::LeanObject,
    mut v_inst_240_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_241_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_241_ = l_Lean_Compiler_LCNF_instMonadScopeOfMonadLiftOfMonadFunctor___redArg(
        v_inst_238_,
        v_inst_239_,
        v_inst_240_,
    );
    return v___x_241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inScope___redArg___lam__0(
    mut v___f_242_: *mut leanh::LeanObject,
    mut v_fvarId_243_: *mut leanh::LeanObject,
    mut v_toPure_244_: *mut leanh::LeanObject,
    mut v_____do__lift_245_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_246_: u8 = 0;
    let mut v___x_247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_246_ = l_Std_DTreeMap_Internal_Impl_contains___redArg(
        v___f_242_,
        v_fvarId_243_,
        v_____do__lift_245_,
    );
    v___x_247_ = leanh::lean_box((v___x_246_) as usize);
    v___x_248_ = leanh::lean_apply_2(v_toPure_244_, leanh::lean_box(0), v___x_247_);
    return v___x_248_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inScope___redArg(
    mut v_inst_250_: *mut leanh::LeanObject,
    mut v_inst_251_: *mut leanh::LeanObject,
    mut v_fvarId_252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_getScope_255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_253_ = leanh::lean_ctor_get(v_inst_251_, 0);
    leanh::lean_inc_ref(v_toApplicative_253_);
    v_toBind_254_ = leanh::lean_ctor_get(v_inst_251_, 1);
    leanh::lean_inc(v_toBind_254_);
    leanh::lean_dec_ref(v_inst_251_);
    v_getScope_255_ = leanh::lean_ctor_get(v_inst_250_, 0);
    leanh::lean_inc(v_getScope_255_);
    leanh::lean_dec_ref(v_inst_250_);
    v_toPure_256_ = leanh::lean_ctor_get(v_toApplicative_253_, 1);
    leanh::lean_inc(v_toPure_256_);
    leanh::lean_dec_ref(v_toApplicative_253_);
    v___f_257_ = l_Lean_Compiler_LCNF_inScope___redArg___closed__0;
    v___f_258_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_inScope___redArg___lam__0 as *mut core::ffi::c_void,
        4,
        3,
    );
    leanh::lean_closure_set(v___f_258_, 0, v___f_257_);
    leanh::lean_closure_set(v___f_258_, 1, v_fvarId_252_);
    leanh::lean_closure_set(v___f_258_, 2, v_toPure_256_);
    v___x_259_ = leanh::lean_apply_4(
        v_toBind_254_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_getScope_255_,
        v___f_258_,
    );
    return v___x_259_;
}
pub unsafe fn l_Lean_Compiler_LCNF_inScope(
    mut v_m_260_: *mut leanh::LeanObject,
    mut v_inst_261_: *mut leanh::LeanObject,
    mut v_inst_262_: *mut leanh::LeanObject,
    mut v_fvarId_263_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_264_ = l_Lean_Compiler_LCNF_inScope___redArg(v_inst_261_, v_inst_262_, v_fvarId_263_);
    return v___x_264_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withParams___redArg___lam__0(
    mut v_x1_265_: *mut leanh::LeanObject,
    mut v_x2_266_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fvarId_267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_267_ = leanh::lean_ctor_get(v_x2_266_, 0);
    leanh::lean_inc(v_fvarId_267_);
    leanh::lean_dec_ref(v_x2_266_);
    v___x_268_ = l_Lean_FVarIdSet_insert(v_x1_265_, v_fvarId_267_);
    return v___x_268_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withParams___redArg___lam__1(
    mut v_ps_288_: *mut leanh::LeanObject,
    mut v___f_289_: *mut leanh::LeanObject,
    mut v_s_290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_294_: u8 = 0;
    v___x_291_ = leanh::lean_unsigned_to_nat(0);
    v___x_292_ = lean_array_get_size(v_ps_288_);
    v___x_293_ = l_Lean_Compiler_LCNF_withParams___redArg___lam__1___closed__9;
    v___x_294_ = lean_nat_dec_lt(v___x_291_, v___x_292_);
    if v___x_294_ == 0 {
        leanh::lean_dec_ref(v___f_289_);
        leanh::lean_dec_ref(v_ps_288_);
        return v_s_290_;
    } else {
        let mut v___x_295_: u8 = 0;
        v___x_295_ = lean_nat_dec_le(v___x_292_, v___x_292_);
        if v___x_295_ == 0 {
            if v___x_294_ == 0 {
                leanh::lean_dec_ref(v___f_289_);
                leanh::lean_dec_ref(v_ps_288_);
                return v_s_290_;
            } else {
                let mut v___x_296_: usize = 0;
                let mut v___x_297_: usize = 0;
                let mut v___x_298_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_296_ = 0usize;
                v___x_297_ = lean_usize_of_nat(v___x_292_);
                v___x_298_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    leanh::lean_box(0),
                    v___x_293_,
                    v___f_289_,
                    v_ps_288_,
                    v___x_296_,
                    v___x_297_,
                    v_s_290_,
                );
                return v___x_298_;
            }
        } else {
            let mut v___x_299_: usize = 0;
            let mut v___x_300_: usize = 0;
            let mut v___x_301_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_299_ = 0usize;
            v___x_300_ = lean_usize_of_nat(v___x_292_);
            v___x_301_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold(
                leanh::lean_box(0),
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_293_,
                v___f_289_,
                v_ps_288_,
                v___x_299_,
                v___x_300_,
                v_s_290_,
            );
            return v___x_301_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_withParams___redArg(
    mut v_inst_303_: *mut leanh::LeanObject,
    mut v_ps_304_: *mut leanh::LeanObject,
    mut v_x_305_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_309_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_306_ = leanh::lean_ctor_get(v_inst_303_, 1);
    leanh::lean_inc(v_withScope_306_);
    leanh::lean_dec_ref(v_inst_303_);
    v___f_307_ = l_Lean_Compiler_LCNF_withParams___redArg___closed__0;
    v___f_308_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_withParams___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_308_, 0, v_ps_304_);
    leanh::lean_closure_set(v___f_308_, 1, v___f_307_);
    v___x_309_ = leanh::lean_apply_3(
        v_withScope_306_,
        leanh::lean_box(0),
        v___f_308_,
        v_x_305_,
    );
    return v___x_309_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withParams(
    mut v_m_310_: *mut leanh::LeanObject,
    mut v_pu_311_: u8,
    mut v_00_u03b1_312_: *mut leanh::LeanObject,
    mut v_inst_313_: *mut leanh::LeanObject,
    mut v_inst_314_: *mut leanh::LeanObject,
    mut v_ps_315_: *mut leanh::LeanObject,
    mut v_x_316_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_320_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_317_ = leanh::lean_ctor_get(v_inst_313_, 1);
    leanh::lean_inc(v_withScope_317_);
    leanh::lean_dec_ref(v_inst_313_);
    v___f_318_ = l_Lean_Compiler_LCNF_withParams___redArg___closed__0;
    v___f_319_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_withParams___redArg___lam__1 as *mut core::ffi::c_void,
        3,
        2,
    );
    leanh::lean_closure_set(v___f_319_, 0, v_ps_315_);
    leanh::lean_closure_set(v___f_319_, 1, v___f_318_);
    v___x_320_ = leanh::lean_apply_3(
        v_withScope_317_,
        leanh::lean_box(0),
        v___f_319_,
        v_x_316_,
    );
    return v___x_320_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withParams___boxed(
    mut v_m_321_: *mut leanh::LeanObject,
    mut v_pu_322_: *mut leanh::LeanObject,
    mut v_00_u03b1_323_: *mut leanh::LeanObject,
    mut v_inst_324_: *mut leanh::LeanObject,
    mut v_inst_325_: *mut leanh::LeanObject,
    mut v_ps_326_: *mut leanh::LeanObject,
    mut v_x_327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pu_boxed_328_: u8 = 0;
    let mut v_res_329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_328_ = (leanh::lean_unbox(v_pu_322_) as u8);
    v_res_329_ = l_Lean_Compiler_LCNF_withParams(
        v_m_321_,
        v_pu_boxed_328_,
        v_00_u03b1_323_,
        v_inst_324_,
        v_inst_325_,
        v_ps_326_,
        v_x_327_,
    );
    leanh::lean_dec_ref(v_inst_325_);
    return v_res_329_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withFVar___redArg___lam__0(
    mut v_fvarId_330_: *mut leanh::LeanObject,
    mut v_s_331_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_332_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_332_ = l_Lean_FVarIdSet_insert(v_s_331_, v_fvarId_330_);
    return v___x_332_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withFVar___redArg(
    mut v_inst_333_: *mut leanh::LeanObject,
    mut v_fvarId_334_: *mut leanh::LeanObject,
    mut v_x_335_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_336_ = leanh::lean_ctor_get(v_inst_333_, 1);
    leanh::lean_inc(v_withScope_336_);
    leanh::lean_dec_ref(v_inst_333_);
    v___f_337_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_withFVar___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_337_, 0, v_fvarId_334_);
    v___x_338_ = leanh::lean_apply_3(
        v_withScope_336_,
        leanh::lean_box(0),
        v___f_337_,
        v_x_335_,
    );
    return v___x_338_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withFVar(
    mut v_m_339_: *mut leanh::LeanObject,
    mut v_00_u03b1_340_: *mut leanh::LeanObject,
    mut v_inst_341_: *mut leanh::LeanObject,
    mut v_inst_342_: *mut leanh::LeanObject,
    mut v_fvarId_343_: *mut leanh::LeanObject,
    mut v_x_344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_347_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_345_ = leanh::lean_ctor_get(v_inst_341_, 1);
    leanh::lean_inc(v_withScope_345_);
    leanh::lean_dec_ref(v_inst_341_);
    v___f_346_ = leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_withFVar___redArg___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_346_, 0, v_fvarId_343_);
    v___x_347_ = leanh::lean_apply_3(
        v_withScope_345_,
        leanh::lean_box(0),
        v___f_346_,
        v_x_344_,
    );
    return v___x_347_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withFVar___boxed(
    mut v_m_348_: *mut leanh::LeanObject,
    mut v_00_u03b1_349_: *mut leanh::LeanObject,
    mut v_inst_350_: *mut leanh::LeanObject,
    mut v_inst_351_: *mut leanh::LeanObject,
    mut v_fvarId_352_: *mut leanh::LeanObject,
    mut v_x_353_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_354_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_354_ = l_Lean_Compiler_LCNF_withFVar(
        v_m_348_,
        v_00_u03b1_349_,
        v_inst_350_,
        v_inst_351_,
        v_fvarId_352_,
        v_x_353_,
    );
    leanh::lean_dec_ref(v_inst_351_);
    return v_res_354_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(
    mut v___x_355_: *mut leanh::LeanObject,
    mut v_x_356_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v___x_355_);
    return v___x_355_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0___boxed(
    mut v___x_357_: *mut leanh::LeanObject,
    mut v_x_358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_359_ = l_Lean_Compiler_LCNF_withNewScope___redArg___lam__0(v___x_357_, v_x_358_);
    leanh::lean_dec(v_x_358_);
    leanh::lean_dec(v___x_357_);
    return v_res_359_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNewScope___redArg(
    mut v_inst_362_: *mut leanh::LeanObject,
    mut v_x_363_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_366_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_364_ = leanh::lean_ctor_get(v_inst_362_, 1);
    leanh::lean_inc(v_withScope_364_);
    leanh::lean_dec_ref(v_inst_362_);
    v___f_365_ = l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0;
    v___x_366_ = leanh::lean_apply_3(
        v_withScope_364_,
        leanh::lean_box(0),
        v___f_365_,
        v_x_363_,
    );
    return v___x_366_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNewScope(
    mut v_m_367_: *mut leanh::LeanObject,
    mut v_00_u03b1_368_: *mut leanh::LeanObject,
    mut v_inst_369_: *mut leanh::LeanObject,
    mut v_inst_370_: *mut leanh::LeanObject,
    mut v_x_371_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_withScope_372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_withScope_372_ = leanh::lean_ctor_get(v_inst_369_, 1);
    leanh::lean_inc(v_withScope_372_);
    leanh::lean_dec_ref(v_inst_369_);
    v___f_373_ = l_Lean_Compiler_LCNF_withNewScope___redArg___closed__0;
    v___x_374_ = leanh::lean_apply_3(
        v_withScope_372_,
        leanh::lean_box(0),
        v___f_373_,
        v_x_371_,
    );
    return v___x_374_;
}
pub unsafe fn l_Lean_Compiler_LCNF_withNewScope___boxed(
    mut v_m_375_: *mut leanh::LeanObject,
    mut v_00_u03b1_376_: *mut leanh::LeanObject,
    mut v_inst_377_: *mut leanh::LeanObject,
    mut v_inst_378_: *mut leanh::LeanObject,
    mut v_x_379_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_380_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_380_ = l_Lean_Compiler_LCNF_withNewScope(
        v_m_375_,
        v_00_u03b1_376_,
        v_inst_377_,
        v_inst_378_,
        v_x_379_,
    );
    leanh::lean_dec_ref(v_inst_378_);
    return v_res_380_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_MonadScope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_MonadScope(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_MonadScope(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_MonadScope(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_MonadScope(builtin);
}